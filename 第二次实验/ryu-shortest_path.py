import logging# python的日志记录工具
import struct # https://docs.python.org/zh-cn/3.8/library/struct.html
import copy
import networkx as nx
from operator import attrgetter
from ryu import cfg
from ryu.base import app_manager# 这个文件中定义了ryuAPP基类
from ryu.controller import ofp_event# 完成了事件的定义，从而可以在函数中注册handler,监听事件，并作出回应
from ryu.controller.handler import MAIN_DISPATCHER, DEAD_DISPATCHER
from ryu.controller.handler import CONFIG_DISPATCHER
from ryu.controller.handler import set_ev_cls
from ryu.ofproto import ofproto_v1_3
from ryu.lib.packet import packet
from ryu.lib.packet import ethernet
from ryu.lib.packet import ipv4
from ryu.lib.packet import arp
from ryu.lib import hub
from collections import defaultdict

from ryu.topology import event, switches
from ryu.topology.api import get_all_switch, get_all_link, get_switch, get_link
import setting


class ShortestPath(app_manager.RyuApp):
    OFP_VERSIONS = [ofproto_v1_3.OFP_VERSION]

    def __init__(self, *args):
        super(ShortestPath, self).__init__(*args)
        self.dpid_mac_port = {}
        
        self.net = nx.DiGraph()# store the dj graph???
        self.topology_api_app = self
        self.name = "awareness"# python中的self就相当于C++中的this指针，当前对象的成员变量name赋值为awareness
        
        self.link_to_port = {}# 存储交换机之间链路与端口的映射关系 (src_dpid,dst_dpid)->(src_port,dst_port)
        self.access_table = {}# 存储主机的接入信息 {(sw,port) :[host1_ip]}
        self.switch_port_table = {}# 存储交换机端口列表 dpip->port_num
        self.access_ports = defaultdict(dict)# 存储外向端口(与终端连接的端口)dpid->port_num
        self.interior_ports = {}# 存储内部端口 dpid->port_num
        self.graph = nx.DiGraph()# 存储网络拓扑图
        
        self.pre_graph = nx.DiGraph()# 带有pre前缀的数据结构用于保存上一次获取的信息，用于和当前获取信息作比较
        self.pre_access_table = {}
        self.pre_link_to_port = {}
        
        self.shortest_paths = None
        self.datapaths = {}# store the shortest path????
        self.arp_num = 0
        self.n = 0

        self.discover_thread = hub.spawn(self.discover)

    def discover(self):# 在discover函数中，周期执行get_topology和是show_topology函数
        i = 0
        while True:
            self.show_topology()# show_topology函数则是将网络信息格式化地展示在终端中。
            if (i == 5):
                self.get_topology(None)
                '''在get_topology函数中，
                控制器可以获取到网络中的交换机和端口信息、链路信息、主机接入信息等。
                此外，控制器通过实时检测网络变化的异步事件来更新网络资源信息。'''
                i = 0
            i = i + 1
            hub.sleep(1)

    '''ryu控制器和交换机的连接有4个阶段，分别是
    ryu.controller.handler.HANDSHAKE_DISPATCHER
    ryu.controller.handler.CONFIG_DISPATCHER
    ryu.controller.handler.MAIN_DISPATCHER
    ryu.controller.handler.DEAD_DISPATCHER
    其中，CONFIG_DISPATCHER代表的是协议版本确认后向交换机发送特性请求消息的阶段。
    MAIN_DISPATCHER代表的是特性消息接受到后到断开连接前的阶段。
    当启动控制器再启动交换机后，先经历握手阶段，再经历CONFIG_DISPATCHER这一个阶段。
    进入CONFIG_DISPATCHER这个阶段后，控制器自动发送特性请求消息。
    交换机接受到特性请求消息后会回复消息，就是EventOFPSwitchFeatures。
    当控制器接受到EventOFPSwitchFeatures这个对象且还未转换到MAIN_DISPATCHER这个状态时，
    就触发这个方法。'''

    '''@set_ev_cls这个装饰器的用处是，当ofp_event.EventOFPSwitchFeatures这样的一个事件来临，
    且处于CONFIG_DISPATCHER这样一个阶段时，触发这个方法switch_features_handler(self, ev)，
    其中ev参数是ofp_event.EventOFPSwitchFeatures的这样一个事件类的对象。'''
    @set_ev_cls(ofp_event.EventOFPSwitchFeatures, CONFIG_DISPATCHER)
    def switch_features_handler(self, ev):# switch_features_handler是每个控制器的标配
        datapath = ev.msg.datapath
        '''datapath.ofproto对象是一个OpenFlow协议数据结构对象数据，
        成员包括OpenFlow协议的数据结构，如动作类型OFPP_FLOOD'''
        ofproto = datapath.ofproto
        parser = datapath.ofproto_parser# datapath.ofp_parser则是一个按照OpenFlow解析的数据结构
        msg = ev.msg
        # self.logger.info("switch:%s connected", datapath.id)

        # install table-miss flow entry
        match = parser.OFPMatch()# match这里构造的parser.OFPMatch()代表没有匹配任何东西。
        '''actions是一个列表，用于存放action list，可在其中添加动作。这里构造的意思是发送给控制器。
        意思是，当没有匹配任何其它流表时，发送请求给控制器。（因为它的优先级最低是0）'''
        actions = [parser.OFPActionOutput(ofproto.OFPP_CONTROLLER,ofproto.OFPCML_NO_BUFFER)]
        '''self.add_flow这个方法在这里配置的参数有datapath, priority，match，actions
        datapath存储交换机的基本信息，如id，端口信息。priority越高，优先级就越高。'''
        self.add_flow(datapath, 0, match, actions)

    def add_flow(self, dp, p, match, actions, idle_timeout=0, hard_timeout=0):# 每个控制器的标配
        ofproto = dp.ofproto
        parser = dp.ofproto_parser

        # construct flow_mod message and send it.
        inst = [parser.OFPInstructionActions(ofproto.OFPIT_APPLY_ACTIONS,actions)]
        # mod是控制器下发给交换机的修改流表的信息
        mod = parser.OFPFlowMod(datapath=dp, priority=p,idle_timeout=idle_timeout,hard_timeout=hard_timeout,match=match, instructions=inst)
        dp.send_msg(mod)# datapath.send_msg()函数用于发送数据到指定datapath。

    '''packet-out消息是从控制器向交换机发送的消息，是包含数据包发送命令的消息'''
    def send_packet_out(self, datapath, buffer_id, src_port, dst_port, data):
        out = self.build_packet_out(datapath, buffer_id,src_port, dst_port, data)
        if out:
            datapath.send_msg(out)# datapath.send_msg()函数用于发送数据到指定datapath。

    def build_packet_out(self, datapath, buffer_id, src_port, dst_port, data):
        actions = []
        if dst_port:
            actions.append(datapath.ofproto_parser.OFPActionOutput(dst_port))

        msg_data = None
        if buffer_id == datapath.ofproto.OFP_NO_BUFFER:
            if data is None:
                return None
            msg_data = data

        out = datapath.ofproto_parser.OFPPacketOut(datapath=datapath, buffer_id=buffer_id,data=msg_data, in_port=src_port, actions=actions)
        return out

    def get_host_location(self, host_ip):
        for key in self.access_table.keys():
            if self.access_table[key][0] == host_ip:
                return key
        self.logger.info("%s location is not found." % host_ip)
        return None

    events = [event.EventSwitchEnter,event.EventSwitchLeave, event.EventPortAdd,event.EventPortDelete, event.EventPortModify,event.EventLinkAdd, event.EventLinkDelete]

    @set_ev_cls(ofp_event.EventOFPStateChange, [MAIN_DISPATCHER, DEAD_DISPATCHER])
    def state_change_handler(self, ev):
        datapath = ev.datapath
        if ev.state == MAIN_DISPATCHER:
            if not datapath.id in self.datapaths:
                self.datapaths[datapath.id] = datapath
        elif ev.state == DEAD_DISPATCHER:
            if datapath.id in self.datapaths:
                del self.datapaths[datapath.id]

    def get_graph(self, link_list):
        for src in self.switches:
            for dst in self.switches:
                if src == dst:
                    self.graph.add_edge(src, dst, weight=0)
                elif (src, dst) in link_list:
                    self.graph.add_edge(src, dst, weight=1)
        return self.graph

    '''在get_topology函数中，控制器可以获取到网络中的交换机和端口信息、链路信息、主机接入信息等。
    此外，控制器通过实时检测网络变化的异步事件来更新网络资源信息。'''
    def get_topology(self, ev):
        j = 0
        switch_list = get_switch(self, None)
        self.create_port_map(switch_list)
        self.switches = self.switch_port_table.keys()
        links = get_link(self, None)
        self.create_interior_links(links)
        self.create_access_ports()
        self.get_graph(self.link_to_port.keys())

    def register_access_info(self, dpid, in_port, ip, mac):
        if in_port in self.access_ports[dpid]:
            if (dpid, in_port) in self.access_table:
                if self.access_table[(dpid, in_port)] == (ip, mac):
                    return
                else:
                    self.access_table[(dpid, in_port)] = (ip, mac)
                    return
            else:
                self.access_table.setdefault((dpid, in_port), None)
                self.access_table[(dpid, in_port)] = (ip, mac)
                return

    # 对拓扑中环路的处理：flood + arp_forwarding
    def flood(self, msg):
        datapath = msg.datapath
        ofproto = datapath.ofproto
        parser = datapath.ofproto_parser

        for dpid in self.access_ports:# access_ports存储外向端口(与终端连接的端口)dpid->port_num
            for port in self.access_ports[dpid]:
                if (dpid, port) not in self.access_table.keys():# access_table存储主机的接入信息 {(sw,port) :[host1_ip]}
                    datapath = self.datapaths[dpid]
                    out = self.build_packet_out(datapath, ofproto.OFP_NO_BUFFER,ofproto.OFPP_CONTROLLER, port, msg.data)
                    datapath.send_msg(out)
        self.logger.debug("Flooding msg")

    def arp_forwarding(self, msg, src_ip, dst_ip):
        datapath = msg.datapath
        ofproto = datapath.ofproto
        parser = datapath.ofproto_parser
        result = self.get_host_location(dst_ip)
        if result:  # host record in access table.
            datapath_dst, out_port = result[0], result[1]

            datapath_1 = self.datapaths[datapath_dst]
            out = self.build_packet_out(datapath_1, ofproto.OFP_NO_BUFFER,ofproto.OFPP_CONTROLLER,out_port, msg.data)
            datapath_1.send_msg(out)
            self.logger.debug("Reply ARP to knew host")
        else:
            self.flood(msg)

    # 交换机获取源地址和目的地址
    def get_sw(self, dpid, in_port, src, dst):
        src_sw = dpid
        dst_sw = None

        src_location = self.get_host_location(src)
        if in_port in self.access_ports[dpid]:
            if (dpid, in_port) == src_location:
                src_sw = src_location[0]
            else:
                return None

        dst_location = self.get_host_location(dst)
        if dst_location:
            dst_sw = dst_location[0]

        return src_sw, dst_sw

    def get_path(self, src, dst):# 利用networkx里的最短路径函数计算最短路径
        return nx.shortest_path(self.graph, src, dst, 1)

    def create_port_map(self, switch_list):
        for sw in switch_list:
            dpid = sw.dp.id
            self.switch_port_table.setdefault(dpid, set())
            self.interior_ports.setdefault(dpid, set())
            self.access_ports.setdefault(dpid, set())
            for p in sw.ports:
                self.switch_port_table[dpid].add(p.port_no)

    # get links`srouce port to dst port  from link_list,
    # link_to_port:(src_dpid,dst_dpid)->(src_port,dst_port)
    def create_interior_links(self, link_list):
        for link in link_list:
            src = link.src
            dst = link.dst
            self.link_to_port[
                (src.dpid, dst.dpid)] = (src.port_no, dst.port_no)

            # find the access ports and interiorior ports
            if link.src.dpid in self.switches:
                self.interior_ports[link.src.dpid].add(link.src.port_no)
            if link.dst.dpid in self.switches:
                self.interior_ports[link.dst.dpid].add(link.dst.port_no)

    # get ports without link into access_ports
    def create_access_ports(self):
        for sw in self.switch_port_table:
            all_port_table = self.switch_port_table[sw]
            interior_port = self.interior_ports[sw]
            self.access_ports[sw] = all_port_table - interior_port

    def get_link_to_port(self, link_to_port, src_dpid, dst_dpid):
        if (src_dpid, dst_dpid) in link_to_port:
            return link_to_port[(src_dpid, dst_dpid)]
        else:
            self.logger.info("dpid:%s->dpid:%s is not in links" % (
                src_dpid, dst_dpid))
            return None

    def send_flow_mod(self, datapath, flow_info, src_port, dst_port):
        parser = datapath.ofproto_parser
        actions = []
        actions.append(parser.OFPActionOutput(dst_port))
        match = parser.OFPMatch(in_port=src_port, eth_type=flow_info[0],ipv4_src=flow_info[1], ipv4_dst=flow_info[2])
        self.add_flow(datapath, 1, match, actions,idle_timeout=15, hard_timeout=60)

    def get_port(self, dst_ip, access_table):
        # access_table: {(sw,port) :(ip, mac)}
        if access_table:
            if isinstance(access_table.values()[0], tuple):
                for key in access_table.keys():
                    if dst_ip == access_table[key][0]:
                        dst_port = key[1]
                        return dst_port
        return None

    # 安装流表项函数
    def install_flow(self, datapaths, link_to_port, access_table, path,flow_info, buffer_id, data=None):
        ''' path=[dpid1, dpid2...]
            flow_info=(eth_type, src_ip, dst_ip, in_port)
        '''
        if path is None or len(path) == 0:
            self.logger.info("Path error!")
            return
        in_port = flow_info[3]
        first_dp = datapaths[path[0]]
        out_port = first_dp.ofproto.OFPP_LOCAL
        back_info = (flow_info[0], flow_info[2], flow_info[1])
        # inter_link
        if len(path) > 2:
            for i in xrange(1, len(path) - 1):
                port = self.get_link_to_port(link_to_port, path[i - 1], path[i])
                port_next = self.get_link_to_port(link_to_port,path[i], path[i + 1])
                if port and port_next:
                    src_port, dst_port = port[1], port_next[0]
                    datapath = datapaths[path[i]]
                    self.send_flow_mod(datapath, flow_info, src_port, dst_port)
                    self.send_flow_mod(datapath, back_info, dst_port, src_port)
                    self.logger.debug("inter_link flow install")
        if len(path) > 1:
            # the last flow entry: tor -> host
            port_pair = self.get_link_to_port(link_to_port, path[-2], path[-1])
            if port_pair is None:
                self.logger.info("Port is not found")
                return
            src_port = port_pair[1]

            dst_port = self.get_port(flow_info[2], access_table)
            if dst_port is None:
                self.logger.info("Last port is not found.")
                return

            last_dp = datapaths[path[-1]]
            self.send_flow_mod(last_dp, flow_info, src_port, dst_port)
            self.send_flow_mod(last_dp, back_info, dst_port, src_port)

            # the first flow entry
            port_pair = self.get_link_to_port(link_to_port, path[0], path[1])
            if port_pair is None:
                self.logger.info("Port not found in first hop.")
                return
            out_port = port_pair[0]
            self.send_flow_mod(first_dp, flow_info, in_port, out_port)
            self.send_flow_mod(first_dp, back_info, out_port, in_port)
            self.send_packet_out(first_dp, buffer_id, in_port, out_port, data)

        # src and dst on the same datapath
        else:
            out_port = self.get_port(flow_info[2], access_table)
            if out_port is None:
                self.logger.info("Out_port is None in same dp")
                return
            self.send_flow_mod(first_dp, flow_info, in_port, out_port)
            self.send_flow_mod(first_dp, back_info, out_port, in_port)
            self.send_packet_out(first_dp, buffer_id, in_port, out_port, data)

    def shortest_forwarding(self, msg, eth_type, ip_src, ip_dst):# 显示最短路径
        datapath = msg.datapath
        ofproto = datapath.ofproto
        parser = datapath.ofproto_parser
        in_port = msg.match['in_port']

        result = self.get_sw(datapath.id, in_port, ip_src, ip_dst)
        if result:
            src_sw, dst_sw = result[0], result[1]
            if dst_sw:
                path = self.get_path(src_sw, dst_sw)
                self.logger.info("[PATH]%s to %s: %s" % (ip_src, ip_dst, path))
                flow_info = (eth_type, ip_src, ip_dst, in_port)
                self.install_flow(self.datapaths,self.link_to_port,self.access_table, path,flow_info, msg.buffer_id, msg.data)
        return

    def show_topology(self):
        self.n = self.n + 1

    def packet_in_handler_2(self, ev):
        msg = ev.msg
        datapath = msg.datapath

        parser = datapath.ofproto_parser
        in_port = msg.match['in_port']
        pkt = packet.Packet(msg.data)

        eth_type = pkt.get_protocols(ethernet.ethernet)[0].ethertype
        arp_pkt = pkt.get_protocol(arp.arp)
        ip_pkt = pkt.get_protocol(ipv4.ipv4)

        if arp_pkt:
            arp_src_ip = arp_pkt.src_ip
            arp_dst_ip = arp_pkt.dst_ip
            mac = arp_pkt.src_mac

            # record the access info
            self.register_access_info(datapath.id, in_port, arp_src_ip, mac)

    '''@set_ev_cls用于告知ryu，被修饰的函数应该被调用.
    这个类代表交换机发送数据包给控制器引发的类，且一定是在MAIN_DISPATCHER这个阶段才触发。'''
    @set_ev_cls(ofp_event.EventOFPPacketIn, MAIN_DISPATCHER)
    def packet_in_handler(self, ev):# 此方法用于处理packet_in事件，每个控制器的标配
        self.packet_in_handler_2(ev)
        msg = ev.msg# 每一个事件类ev中都有msg成员，用于携带触发事件的数据包
        '''已经格式化的msg其实就是一个packet_in报文，
        msg.datapath直接可以获得packet_in报文的datapath结构。datapath用于描述一个交换网桥，
        也是和控制器通信的实体单元。'''
        datapath = msg.datapath
        # get the received port number from packet_in message.
        in_port = msg.match['in_port']
        
        pkt = packet.Packet(msg.data)
        arp_pkt = pkt.get_protocol(arp.arp)
        ip_pkt = pkt.get_protocol(ipv4.ipv4)

        if isinstance(arp_pkt, arp.arp):# isinstance来判断一个对象是否是一个已知的类型.其第一个参数为对象，第二个参数为类型名.
            self.arp_forwarding(msg, arp_pkt.src_ip, arp_pkt.dst_ip)

        if isinstance(ip_pkt, ipv4.ipv4):
            if len(pkt.get_protocols(ethernet.ethernet)):
                eth_type = pkt.get_protocols(ethernet.ethernet)[0].ethertype
                self.shortest_forwarding(msg, eth_type, ip_pkt.src, ip_pkt.dst)
