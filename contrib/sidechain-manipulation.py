#!/usr/bin/env python2

import sys, os, traceback
sys.path.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../python-bitcoinrpc"))
from bitcoinrpc.authproxy import AuthServiceProxy, JSONRPCException
from decimal import *

# VARIOUS SETTINGS...
sidechain_url = "http://user:pass@127.0.0.1:4241"
bitcoin_url = "http://user:pass@127.0.0.1:18332"

redeem_script = "55210269992fb441ae56968e5b77d46a3e53b69f136444ae65a94041fc937bdb28d93321021df31471281d4478df85bfce08a10aab82601dca949a79950f8ddf7002bd915a2102174c82021492c2c6dfcbfa4187d10d38bed06afb7fdcd72c880179fddd641ea121033f96e43d72c33327b6a4631ccaa6ea07f0b106c88b9dc71c9000bb6044d5e88a210313d8748790f2a86fb524579b46ce3c68fedd58d2a738716249a9f7d5458a15c221030b632eeb079eb83648886122a04c7bf6d98ab5dfb94cf353ee3e9382a4c2fab02102fb54a7fcaa73c307cfd70f3fa66a2e4247a71858ca731396343ad30c7c4009ce57ae"
secondScriptPubKey = "OP_DROP 144 OP_LESSTHANOREQUAL"
secondScriptPubKeyHash = "9eac001049d5c38ece8996485418421f4a01e2d7"

#Bitcoin:
bitcoin_genesis_hash = "000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f"
#Testnet:
#bitcoin_genesis_hash = "000000000933ea01ad0ee984209779baaec3ced90fa3f408719526f8d77f4943"

sidechain_tx_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../alpha-tx")

contracthashtool_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../contracthashtool/contracthashtool")
is_testnet = 1


# CODE THINGS...
sidechain = AuthServiceProxy(sidechain_url)
bitcoin = AuthServiceProxy(bitcoin_url)

testnet_arg = ""
if is_testnet == 1:
	testnet_arg = "-t"

inverse_bitcoin_genesis_hash = "".join(reversed([bitcoin_genesis_hash[i:i+2] for i in range(0, len(bitcoin_genesis_hash), 2)]))

def help():
	print("HELP: %s (generate-one-of-one-multisig (sidechain-wallet|mainchain-wallet))|(send-to-sidechain SIDECHAIN_ADDRESS AMOUNT)|(claim-on-sidechain SIDECHAIN_ADDRESS NONCE SEND_TXID)|(spend-from-claim SIDECHAIN_TX_HASH ONE_OF_ONE_ADDRESS)" % sys.argv[0])
	exit(1)

class UTXOFinder:
	in_txid = ""
	in_vout = -1
	in_value = -1

	def check_tx(self, tx):
		for vout, output in enumerate(tx["vout"]):
			if output["scriptPubKey"]["type"] == "withdraw":
				if output["value"] >= value:
					self.in_txid = tx["txid"]
					self.in_vout = vout
					txo = sidechain.gettxout(self.in_txid, self.in_vout, True)
					if txo == None:
						continue
					self.in_value = Decimal(txo["value"])
			if self.in_value > self.target_value:
				break

	def __init__(self, value):
		self.target_value = value

		for tx in sidechain.batch_([["getrawtransaction", txhash, 1] for txhash in sidechain.getrawmempool()]):
			self.check_tx(tx)
			if self.in_value > self.target_value:
				break

		for i in range(sidechain.getblockcount() + 1)[::-1]:
			if i == 0:
				# Special-case the genesis txo
				self.in_txid = sidechain.getblock(sidechain.getblockhash(0))["tx"][0]
				self.in_vout = 0
				txo = sidechain.gettxout(self.in_txid, self.in_vout, True)
				if txo == None:
					continue
				self.in_value = Decimal(txo["value"])
			else:
				block = sidechain.getblock(sidechain.getblockhash(i))
				for tx in sidechain.batch_([["getrawtransaction", txhash, 1] for txhash in block["tx"]]):
					self.check_tx(tx)
					if self.in_value > self.target_value:
						break
			if self.in_value > self.target_value:
				break

		assert(self.in_value > self.target_value)

try:
	if len(sys.argv) < 2:
		help()
	elif sys.argv[1] == "generate-one-of-one-multisig":
		if len(sys.argv) != 3:
			help()

		if sys.argv[2] == "sidechain-wallet":
			address = sidechain.getnewaddress()
			p2sh_res = sidechain.addmultisigaddress(1, [address])
		elif sys.argv[2] == "mainchain-wallet":
			address = bitcoin.getnewaddress()
			p2sh_res = bitcoin.addmultisigaddress(1, [address])
		else:
			help()
		print("One-of-one address: %s" % address)
		print("P2SH address: %s" % p2sh_res)
	elif sys.argv[1] == "send-to-sidechain":
		if len(sys.argv) != 4:
			help()

		cht = os.popen("%s %s -g -r %s -d %s" % (contracthashtool_path, testnet_arg, redeem_script, sys.argv[2]))
		cht_read = cht.read()
		nonce = cht_read.split("\n")[0 + is_testnet][7:]
		full_contract = cht_read.split("\n")[1 + is_testnet][26:]
		send_address = cht_read.split("\n")[3 + is_testnet][40:]
		assert(cht.close() == None)
		if full_contract[0:8] != "50325348":
			print("You must use a P2SH address")
			exit(1)

		print("Sending %s to %s..." % (sys.argv[3], send_address))
		print("(nonce: %s)" % nonce)

		try:
			tx_hex = bitcoin.createrawtransaction([], {send_address: Decimal(sys.argv[3])})
			tx_hex = bitcoin.fundrawtransaction(tx_hex)['hex']
			tx = bitcoin.signrawtransaction(tx_hex)
			assert(tx['complete'])

			tx_hex = tx['hex']

			total_length  = len(tx_hex)/2
			total_length += 14*32 # maximum length of spv proof 1MB blocks
			total_length += 1000 # len(full_contract) + len(secondScriptPubKey) and rounded up to 1000

			if total_length >= 10000:
				print("Transaction is too large.")
				exit(1)

			txid = bitcoin.sendrawtransaction(tx_hex)
		except:
			# Compensate for <0.9 BC Core by gracefully handling the "already unlocked" wallet case.
			try:
				bitcoin.walletpassphrase('walletPassword', 1000)
			except JSONRPCException as e:
				if e.error['code'] != '-17':
					print("Got the following error from an RPC Call:")
					print(e.error)
					sys.exit()
			txid = bitcoin.sendtoaddress(send_address, Decimal(sys.argv[3]))

		print("Sent tx with id %s" % txid)
	elif sys.argv[1] == "claim-on-sidechain":
		if len(sys.argv) != 5:
			help()

		raw_bitcoin_tx = bitcoin.getrawtransaction(sys.argv[4], 1)
		if not "confirmations" in raw_bitcoin_tx or raw_bitcoin_tx["confirmations"] <= 10:
			print("Please wait for at least 10 confirmations on the bitcoin transaction first")
			exit(1)
		raw_bitcoin_tx_hex = bitcoin.getrawtransaction(sys.argv[4], 0)

		# Might need to calculate the scriptSig here
		secondScriptSig = "1"

		bitcoin_block = bitcoin.getblock(raw_bitcoin_tx["blockhash"])
		coinbase_txid = bitcoin_block["tx"][0]
		raw_coinbase_tx_hex = bitcoin.getrawtransaction(coinbase_txid, 0)

		spv_proof = bitcoin.gettxoutproof([coinbase_txid, sys.argv[4]])

		cht = os.popen("%s %s -g -r %s -d %s -n %s" % (contracthashtool_path, testnet_arg, redeem_script, sys.argv[2], sys.argv[3]))
		cht_read = cht.read()
		assert(cht.close() == None)
		raw_dest = cht_read.split("\n")[1 + is_testnet][66:]
		full_contract = cht_read.split("\n")[1 + is_testnet][26:]
		send_address = cht_read.split("\n")[3 + is_testnet][40:]
		assert(len(raw_dest) == 40)

		nout = -1
		value = -1
		for vout, output in enumerate(raw_bitcoin_tx["vout"]):
			if output["scriptPubKey"]["type"] == "scripthash" and output["scriptPubKey"]["addresses"][0] == send_address:
				nout = vout
				value = Decimal(output["value"])
				break
		assert(nout != -1)

		#TODO: This is a pretty shitty way to find a lock utxo
		utxo = UTXOFinder(value)
		in_txid = utxo.in_txid
		in_vout = utxo.in_vout
		in_value = utxo.in_value

		print("Redeeming from utxo %s:%.16g (value %.16g, refund %.16g)" % (in_txid, in_vout, in_value, in_value - value))

		withdrawkeys = 'withdrawkeys:{"contract": "%s", "txoutproof": "%s", "tx": "%s", "nout": %d, "secondScriptPubKey": "%s", "secondScriptSig": "%s", "coinbase": "%s"}' % (full_contract, spv_proof, raw_bitcoin_tx_hex, nout, secondScriptPubKey, secondScriptSig, raw_coinbase_tx_hex)
		out_scriptPubKey = "OP_IF %d 0x20%s %d 0 0x14%s 0x20%s OP_REORGPROOFVERIFY OP_ELSE 144 OP_NOP3 OP_DROP OP_HASH160 0x14%s OP_EQUAL OP_ENDIF" % (bitcoin_block["height"], sys.argv[4], nout, secondScriptPubKeyHash, inverse_bitcoin_genesis_hash, raw_dest)
		relock_scriptPubKey = "0x20%s 0x14%s OP_WITHDRAWPROOFVERIFY" % (inverse_bitcoin_genesis_hash, secondScriptPubKeyHash)

		cht = os.popen('%s -create \'set=%s\' in=%s:%d:%s:-1 outscript=%s:"%s" outscript=%s:"%s" withdrawsign' % (sidechain_tx_path, withdrawkeys, in_txid, in_vout, str(in_value), str(value), out_scriptPubKey, str(in_value - value), relock_scriptPubKey))
		res_tx = cht.read().split("\n")[0]
		assert(cht.close() == None)

		txid = sidechain.sendrawtransaction(res_tx)
		print("Success!")
		print("Resulting txid: " + str(txid))

	elif sys.argv[1] == "spend-from-claim":
		#TODO: Maybe make wallets recognize this as theirs?
		if len(sys.argv) != 4:
			help()

		prev_tx = sidechain.getrawtransaction(sys.argv[2], 1)
		prev_out = prev_tx["vout"][0]
		assert(prev_out["scriptPubKey"]["type"] == "withdrawout")
		prev_script = prev_out["scriptPubKey"]["asm"].split(" ")
		assert(prev_script[10] == "OP_NOP3")
		if "confirmations" not in prev_tx or prev_tx["confirmations"] < int(prev_script[9]):
			print("You must wait for at least %s confirmations to claim this output (have %d)" % (prev_script[9], prev_tx["confirmations"]))
			exit(1)

		p2sh_res = sidechain.createmultisig(1, [sys.argv[3]])

		cht = os.popen('%s %s -create in=%s:%d:%s:%d outaddr=%s:"%s"' % (sidechain_tx_path, "-testnet" if is_testnet == 1 else "", sys.argv[2], 0, str(prev_out["value"]), 0x100000000 - int(prev_script[9]) - 1, str(prev_out["value"]), sidechain.getnewaddress()))
		tx_hex = cht.read().split("\n")[0]
		assert(cht.close() == None)

		tx_hex = sidechain.signrawtransaction(tx_hex, [{"txid": sys.argv[2], "vout": 0, "scriptPubKey": prev_out["scriptPubKey"]["hex"], "redeemScript": p2sh_res["redeemScript"], "nValue": prev_out["serValue"]}], [sidechain.dumpprivkey(sys.argv[3])])
		if tx_hex["complete"] != True:
			print("Got incomplete transaction (signing failed to create spendable transaction):")
			print(tx_hex["hex"])
		else:
			print("Submitting tx to mempool...")
			sidechain.sendrawtransaction(tx_hex["hex"])
			print("Success!")

	elif sys.argv[1] == "send-to-mainchain":
		if len(sys.argv) != 4:
			help()

		p2sh_tx_test = bitcoin.decoderawtransaction(bitcoin.createrawtransaction([], {sys.argv[2]: 0.1}))["vout"][0]["scriptPubKey"]
		if p2sh_tx_test["type"] != "scripthash":
			print("You must use a P2SH address")
			exit(1)
		p2sh_hex = p2sh_tx_test["asm"].split(" ")[1]

		cht = os.popen('%s -create outscript=%s:"0x1850325348%s OP_DROP 0x20%s 0x14%s WITHDRAWPROOFVERIFY"' % (sidechain_tx_path, sys.argv[3], p2sh_hex, inverse_bitcoin_genesis_hash, secondScriptPubKeyHash))
		res_tx = cht.read().split("\n")[0]
		assert(cht.close() == None)

		donation = sidechain.fundrawtransaction(res_tx)["fee"]
		if donation > 0:
			if donation < 550: # Probably dust
				donation = 550
			cht = os.popen('%s -create outscript=%s:"0x1850325348%s OP_DROP 0x20%s 0x14%s WITHDRAWPROOFVERIFY" outscript=%s:"RETURN"' % (sidechain_tx_path, sys.argv[3], p2sh_hex, inverse_bitcoin_genesis_hash, secondScriptPubKeyHash, str(Decimal(donation) / Decimal(100000000))))
			res_tx = cht.read().split("\n")[0]
			assert(cht.close() == None)

		res_tx = sidechain.fundrawtransaction(res_tx)
		fee = res_tx["fee"]
		res_tx = sidechain.signrawtransaction(res_tx["hex"])["hex"]

		print("Sending %s to functionaries for withdraw to %s (fee of %s satoshis)..." % (sys.argv[3], sys.argv[2], str(fee + donation)))
		txid = sidechain.sendrawtransaction(res_tx)
		print("Sent tx with id %s" % txid)

	else:
		help()
except JSONRPCException as e:
	print(traceback.format_exc())
	print("Got the following error from an RPC Call:")
	print(e.error)
