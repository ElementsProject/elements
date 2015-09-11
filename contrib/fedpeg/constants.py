#!/usr/bin/env python2

import os

class FedpegConstants:
	# VARIOUS SETTINGS...
	sidechain_url = "http://user:pass@127.0.0.1:4241"
	bitcoin_url = "http://user:pass@127.0.0.1:18332"

	redeem_script = "55210269992fb441ae56968e5b77d46a3e53b69f136444ae65a94041fc937bdb28d93321021df31471281d4478df85bfce08a10aab82601dca949a79950f8ddf7002bd915a2102174c82021492c2c6dfcbfa4187d10d38bed06afb7fdcd72c880179fddd641ea121033f96e43d72c33327b6a4631ccaa6ea07f0b106c88b9dc71c9000bb6044d5e88a210313d8748790f2a86fb524579b46ce3c68fedd58d2a738716249a9f7d5458a15c221030b632eeb079eb83648886122a04c7bf6d98ab5dfb94cf353ee3e9382a4c2fab02102fb54a7fcaa73c307cfd70f3fa66a2e4247a71858ca731396343ad30c7c4009ce57ae"
	redeem_script_address = "2N353JioQVxQPpCmeidjsb8kRX28TYXtBtc"
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

	nodes =["WARREN", "GWILLEN", "LUKE-JR/WIZKID", "MAAKU", "APOELSTRA", "MATT", "GMAXWELL"]
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

	def report_error(self, msg):
		print("Error: %s" % msg)

