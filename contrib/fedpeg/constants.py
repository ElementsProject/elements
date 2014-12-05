#!/usr/bin/env python2

import os

class FedpegConstants:
	# VARIOUS SETTINGS...
	sidechain_url = "http://user:pass@127.0.0.1:4241"
	bitcoin_url = "http://user:pass@127.0.0.1:18332"

	redeem_script = "53210300ce2bc14b316474085b4037d126e948042d625f15502c7c9fab01a1a219e79b21021df31471281d4478df85bfce08a10aab82601dca949a79950f8ddf7002bd915a2103b426a9d88f3116fb4beeb4ccadaca9a52071cb8745c469c7b06a9141f9d54b3021023f37702bbe29dccba705cbb38fcdc3b1c19671693fdd3d84707d738a4625598d2103f08409b15dc6cc051b8a640d14c90eee98312d56d1fd4032408d12646acb73b255ae"
	redeem_script_address = "2N3cy1E6jX1penE8QVsV1piyikvooib4ZCA"
	secondScriptPubKeyHash = "9eac001049d5c38ece8996485418421f4a01e2d7"

	blocksigning_private_key = "FILL_ME_IN"
	functionary_private_key = "FILL_ME_IN"

	bitcoin_tx_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../bitcoin-tx")
	contracthashtool_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../contracthashtool/contracthashtool")
	is_testnet = 1

	#Bitcoin:
	bitcoin_genesis_hash = "000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f"
	#Testnet:
	#bitcoin_genesis_hash = "000000000933ea01ad0ee984209779baaec3ced90fa3f408719526f8d77f4943"

	nodes = ["127.0.0.1"]
	my_node = "FILL_ME_IN"

	# Set this to non-None if you're using a proxy (eg for Tor)
	# Note that this requires ZMQ 4.1
	socks_proxy = None
	#socks_proxy = "127.0.0.1:9050"

	def __init__(self):
		# Derived constants (dont touch)
		self.testnet_arg = ""
		if self.is_testnet == 1:
			self.cht_testnet_arg = "-t"
			self.btc_testnet_arg = "-testnet"
		else:
			self.cht_testnet_arg = ""
			self.btc_testnet_arg = ""

		self.sigs_required = int(self.redeem_script[:2], 16) - 0x50

		self.inverse_bitcoin_genesis_hash = "".join(reversed([self.bitcoin_genesis_hash[i:i+2] for i in range(0, len(self.bitcoin_genesis_hash), 2)]))
