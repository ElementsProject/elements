#!/usr/bin/env python2

from time import sleep, time
import socket
import threading
import zmq
import traceback


# For error printing
import sys, os
sys.path.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../python-bitcoinrpc"))
from bitcoinrpc.authproxy import JSONRPCException

zmq_context = zmq.Context()
zmq_poller = zmq.Poller()

if (zmq.zmq_version() < 4):
	print("It is highly recommended you use a version of ZMQ > 4")

class ConsensusPublisher:
	def __init__(self, port):
		self.socket = zmq_context.socket(zmq.PUB)
		self.socket.bind("tcp://*:%d" % port)
		zmq_poller.register(self.socket, zmq.POLLOUT)

	def send_message(self, msg):
		self.socket.send("42 %s" % msg.encode("ascii", "strict"))

class ConsensusSocket:
	def __init__(self, host, port, proxy):
		self.host = host
		self.isSelf = False
		self.sock = zmq_context.socket(zmq.SUB)
		if proxy != None:
			self.sock.setsockopt(zmq.SOCKS_PROXY, proxy)
		self.sock.setsockopt(zmq.RECONNECT_IVL, 500)
		self.sock.setsockopt(zmq.RECONNECT_IVL_MAX, 10000)
		self.sock.connect("tcp://%s:%d" % (host, port))
		self.sock.setsockopt(zmq.SUBSCRIBE, "42")
		zmq_poller.register(self.sock, zmq.POLLIN)

	def read_message(self):
		if not dict(zmq_poller.poll()).has_key(self.sock):
			return None
		topic, msg = self.sock.recv().split(" ", 1)
		return msg

class Self:
	def __init__(self, host):
		self.host = host
		self.isSelf = True
	def read_message(self):
		return None

class RotatingConsensus:
	def __init__(self, nodes_list, my_host, port, interval, proxy):
		self.interval = interval
		self.nodes = [Self(my_host)]
		for host in nodes_list:
			self.nodes.append(ConsensusSocket(host, port, proxy))
		self.nodes.sort(key=lambda node: node.host)
		self.publisher = ConsensusPublisher(port)
		thread = threading.Thread(target=self.main_loop)
		thread.daemon = True
		thread.start()

	def main_loop(self):
		while True:
			sleep(self.interval - time() % self.interval)
			start_time = int(time())
			step = int(time()) % (self.interval * len(self.nodes)) / self.interval

			for node in self.nodes:
				msg = ""
				while msg != None:
					msg = node.read_message()

			if self.nodes[step].isSelf:
				print("Starting master round (as %s)" % self.nodes[step].host)

				sleep(self.interval / 10)
				msg = self._gen_master_msg()
				if msg == None:
					self.report_error("gen_master_msg threw or returned None")
					self._round_failed()
					continue
				if time() - start_time > self.interval / 5:
					self.report_error("gen_master_msg took longer than interval/5: Skipping round!")
					self._round_failed()
					continue
				self.publisher.send_message(msg)
				sleep(self.interval / 2 - (time() - start_time))

			else:
				print("Starting round with master %s" % self.nodes[step].host)
				sleep(self.interval / 4)
				msg = self.nodes[step].read_message()

				if msg == None:
					self.report_error("Missed message from master")
					self._round_failed()
					continue

				broadcast_msg = self._recv_master_msg(msg)
				if broadcast_msg == None:
					self.report_error("recv_master_msg threw or returned None")
					self._round_failed()
					continue
				if time() - start_time > self.interval / 2:
					self.report_error("recv_master_msg took longer than interval/4: Skipping round!")
					self._round_failed()
					continue
				self.publisher.send_message(broadcast_msg)

				sleep(self.interval / 2 - (time() - start_time))

			msgs = []
			for node in self.nodes:
				msg = node.read_message()
				if msg != None:
					msgs.append((node.host, msg))
				elif node != self.nodes[step] and not node.isSelf:
					self.report_error("Missed message from %s" % node.host)

			self._round_done(msgs)
			if time() > start_time + self.interval:
				self.report_error("round_done took longer than interval/2: We skipped a round!")

	def _gen_master_msg(self):
		try:
			return self.gen_master_msg()
		except Exception as e:
			if isinstance(e, JSONRPCException):
				print(e.error)
			print("gen_master_msg threw!")
			print(traceback.format_exc())
			return None

	def _recv_master_msg(self, msg):
		try:
			return self.recv_master_msg(msg)
		except Exception as e:
			if isinstance(e, JSONRPCException):
				print(e.error)
			print("recv_master_msg threw!")
			print(traceback.format_exc())
			return None

	def _round_done(self, peer_messages):
		try:
			self.round_done(peer_messages)
		except Exception as e:
			if isinstance(e, JSONRPCException):
				print(e.error)
			print("round_done threw!")
			print(traceback.format_exc())

	def _round_failed(self):
		try:
			self.round_failed()
		except Exception as e:
			if isinstance(e, JSONRPCException):
				print(e.error)
			print("round_failed threw!")
			print(traceback.format_exc())

	#OVERRIDE THESE:

	def gen_master_msg(self):
		return "MASTER INITIAL BROADCAST"

	def recv_master_msg(self, msg):
		print("GOT '%s' from master" % msg)
		return "PEER RESPONSE BROADCAST"

	def round_done(self, peer_messages):
		print("Finished round...")
		for msg in peer_messages:
			print("Got %s from %s" % (msg[1], msg[0]))

	def round_failed(self):
		return

	def report_error(self, msg):
		print("Error: %s" % msg)
