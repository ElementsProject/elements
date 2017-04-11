#!/usr/bin/env python2

import sys, os, json, traceback, decimal
sys.path.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../python-bitcoinrpc"))
from bitcoinrpc.authproxy import AuthServiceProxy, JSONRPCException
from rotating_consensus import RotatingConsensus
from threading import Lock, current_thread
from time import sleep
from constants import FedpegConstants
from httplib import CannotSendRequest


settings = FedpegConstants()
port = 14252

sidechain = AuthServiceProxy(settings.sidechain_url)

class WatchPeerController(RotatingConsensus):
	round_local_block_hex = ""

	def gen_master_msg(self):
		global sidechain
		try:
			self.round_local_block_hex = sidechain.getnewblockhex()
		except CannotSendRequest as e:
			sidechain = AuthServiceProxy(settings.sidechain_url)
			return None
		return self.round_local_block_hex

	def recv_master_msg(self, msg):
		self.round_local_block_hex = msg
		return sidechain.signblock(msg)

	def round_done(self, peer_messages):
		mysig = sidechain.signblock(self.round_local_block_hex)
		peer_messages.append(("self", mysig))
		sys.stdout.write("Got signatures from %s, now combining..." % str([x[0] for x in peer_messages if x[1][0] == "0" and x[1][1] == "0" and len(x[1]) == 132]))
		sys.stdout.flush()
		res = sidechain.combineblocksigs(self.round_local_block_hex, [x[1] for x in peer_messages])
		if res["complete"]:
			sys.stdout.write("got completely signed block, submitting to sidechaind...")
			sys.stdout.flush()
			sidechain.submitblock(res["hex"])
			print("done")
		else:
			print("got incomplete block")
			for x in peer_messages:
				if x[1][2:] not in res["hex"]:
					print("Signature from %s was probably useless" % x[0])

	def round_failed(self):
		self.round_local_block_hex = ""
		return

	def report_error(self, msg):
		settings.report_error(msg)

sidechain.importprivkey(settings.blocksigning_private_key)

settings.nodes.remove(settings.my_node)
WatchPeerController(settings.nodes, settings.my_node, port, 60, settings.socks_proxy)

while True:
	sleep(10)
