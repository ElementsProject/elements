#!/usr/bin/env python2

import sys, os, traceback, argparse
sys.path.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../python-bitcoinrpc"))
from bitcoinrpc.authproxy import AuthServiceProxy, JSONRPCException
from decimal import *
sys.path.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), "fedpeg/"))
from constants import FedpegConstants

# Command line arguments
parser = argparse.ArgumentParser(description = 'Script that accommodates the ' \
    'movement of coins in and out of sidechains. Optional arguments must ' \
    'come after the name of the action being performed and any related ' \
    'arguments.')
subparsers = parser.add_subparsers(help = 'Sidechain manipulation commands',
                                   dest = 'command')

parser_generate_1of1_MS = subparsers.add_parser('generate-one-of-one-multisig')
parser_generate_1of1_MS.add_argument('wallet', help = 'Determines if ' \
    'sidechain or mainchain wallet will generate an address', \
    choices = ('sidechain-wallet', 'mainchain-wallet'))

parser_send_sidechain = subparsers.add_parser('send-to-sidechain')
parser_send_sidechain.add_argument('-wp','--walletpassword', \
    dest = 'walletpassword', nargs = '?', default = None, help = 'Mainchain ' \
    'wallet unlock password')
parser_send_sidechain.add_argument('p2shSideAddress', help = 'P2SH 1-of-1 ' \
    'multisig sidechain address from the sidechain wallet')
parser_send_sidechain.add_argument('coinAmt', help = 'Amount of coins to pay ' \
    'the P2SH 1-of-1 multisig sidechain address from the mainchain wallet')

parser_claim_sidechain = subparsers.add_parser('claim-on-sidechain')
parser_claim_sidechain.add_argument('sidechainP2SHaddr', help = 'P2SH ' \
    'sidechain address')
parser_claim_sidechain.add_argument('nonce', help = '16-byte sidechain ' \
    'payment nonce')
parser_claim_sidechain.add_argument('sidechainRcvTx', help = 'ID for ' \
    'mainchain transaction where P2SH sidechain address received coins')

parser_spend_from_claim = subparsers.add_parser('spend-from-claim')
parser_spend_from_claim.add_argument('sidechainClaimTx', help = 'ID for ' \
    'sidechain transaction where P2SH sidechain address claimed coins')
parser_spend_from_claim.add_argument('sidechainAddress', help = 'Sidechain ' \
    'address that claimed (in 1-of-1 P2SH multisig form) the coins ')

parser_send_mainchain = subparsers.add_parser('send-to-mainchain')
parser_send_mainchain.add_argument('p2shMainAddress', help = 'P2SH 1-of-1 ' \
    'multisig mainchain address from the mainchain wallet')
parser_send_mainchain.add_argument('coinAmt', help = 'Amount of coins to pay ' \
    'the P2SH 1-of-1 multisig mainchain address from the sidechain wallet')

args = parser.parse_args()

# VARIOUS SETTINGS...
settings = FedpegConstants

sidechain_url = settings.sidechain_url
bitcoin_url = settings.bitcoin_url

redeem_script = settings.redeem_script
secondScriptPubKeyHash = settings.secondScriptPubKeyHash
secondScriptPubKey = "OP_DROP 144 OP_LESSTHANOREQUAL"

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
	if args.command == "generate-one-of-one-multisig":
		if args.wallet == "sidechain-wallet":
			address = sidechain.getnewaddress()
			p2sh_res = sidechain.addmultisigaddress(1, [address])
		elif args.wallet == "mainchain-wallet":
			address = bitcoin.getnewaddress()
			p2sh_res = bitcoin.addmultisigaddress(1, [address])
		print("One-of-one address: %s" % address)
		print("P2SH address: %s" % p2sh_res)
	elif args.command == "send-to-sidechain":
		cht = os.popen("%s %s -g -r %s -d %s" % (contracthashtool_path, testnet_arg, redeem_script, args.p2shSideAddress))
		cht_read = cht.read()
		nonce = cht_read.split("\n")[0 + is_testnet][7:]
		full_contract = cht_read.split("\n")[1 + is_testnet][26:]
		send_address = cht_read.split("\n")[3 + is_testnet][40:]
		assert(cht.close() == None)
		if full_contract[0:8] != "50325348":
			print("You must use a P2SH address")
			exit(1)

		print("Sending %s to %s..." % (args.coinAmt, send_address))
		print("(nonce: %s)" % nonce)

		try:
			tx_hex = bitcoin.createrawtransaction([], {send_address: Decimal(args.coinAmt)})
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
			print("sendrawtransaction - Sent tx with id %s" % txid)
		except JSONRPCException as er:
			print("Got the following error from an RPC Call:")
			print(er.error)

			# If wallet is locked, try to unlock it. Exit if unlock
			# fails. Ignore all other errors for now.
			if er.error['code'] == -13:
				try:
					bitcoin.walletpassphrase(args.walletpassword, 10)
				except JSONRPCException as e:
					# Compensate for <0.9 BC Core by ignoring the "already unlocked" wallet case.
					if e.error['code'] != -17:
						print("Got the following error from an RPC Call:")
						print(e.error)
						sys.exit()

			txid = bitcoin.sendtoaddress(send_address, Decimal(args.coinAmt))
			print("sendtoaddress - Sent tx with id %s" % txid)

	elif args.command == "claim-on-sidechain":
		raw_bitcoin_tx = bitcoin.getrawtransaction(args.sidechainRcvTx, 1)
		if not "confirmations" in raw_bitcoin_tx or raw_bitcoin_tx["confirmations"] <= 10:
			print("Please wait for at least 10 confirmations on the bitcoin transaction first")
			exit(1)
		raw_bitcoin_tx_hex = bitcoin.getrawtransaction(args.sidechainRcvTx, 0)

		# Might need to calculate the scriptSig here
		secondScriptSig = "1"

		bitcoin_block = bitcoin.getblock(raw_bitcoin_tx["blockhash"])
		coinbase_txid = bitcoin_block["tx"][0]
		raw_coinbase_tx_hex = bitcoin.getrawtransaction(coinbase_txid, 0)

		spv_proof = bitcoin.gettxoutproof([coinbase_txid, args.sidechainRcvTx])

		cht = os.popen("%s %s -g -r %s -d %s -n %s" % (contracthashtool_path, testnet_arg, redeem_script, args.sidechainP2SHaddr, args.nonce))
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
		out_scriptPubKey = "OP_IF %d 0x20%s %d 0 0x14%s 0x20%s OP_REORGPROOFVERIFY OP_ELSE 144 OP_NOP3 OP_DROP OP_HASH160 0x14%s OP_EQUAL OP_ENDIF" % (bitcoin_block["height"], args.sidechainRcvTx, nout, secondScriptPubKeyHash, inverse_bitcoin_genesis_hash, raw_dest)
		relock_scriptPubKey = "0x20%s 0x14%s OP_WITHDRAWPROOFVERIFY" % (inverse_bitcoin_genesis_hash, secondScriptPubKeyHash)

		cht = os.popen('%s -create \'set=%s\' in=%s:%d:%s:-1 outscript=%s:"%s" outscript=%s:"%s" withdrawsign' % (sidechain_tx_path, withdrawkeys, in_txid, in_vout, str(in_value), str(value), out_scriptPubKey, str(in_value - value), relock_scriptPubKey))
		res_tx = cht.read().split("\n")[0]
		assert(cht.close() == None)

		txid = sidechain.sendrawtransaction(res_tx)
		print("Success!")
		print("Resulting txid: " + str(txid))

	elif args.command == "spend-from-claim":
		#TODO: Maybe make wallets recognize this as theirs?
		prev_tx = sidechain.getrawtransaction(args.sidechainClaimTx, 1)
		prev_out = prev_tx["vout"][0]
		assert(prev_out["scriptPubKey"]["type"] == "withdrawout")
		prev_script = prev_out["scriptPubKey"]["asm"].split(" ")
		assert(prev_script[10] == "OP_NOP3")
		if "confirmations" not in prev_tx or prev_tx["confirmations"] < int(prev_script[9]):
			print("You must wait for at least %s confirmations to claim this output (have %d)" % (prev_script[9], prev_tx["confirmations"]))
			exit(1)

		p2sh_res = sidechain.createmultisig(1, [args.sidechainAddress])

		cht = os.popen('%s %s -create in=%s:%d:%s:%d outaddr=%s:"%s"' % (sidechain_tx_path, "-testnet" if is_testnet == 1 else "", args.sidechainClaimTx, 0, str(prev_out["value"]), 0x100000000 - int(prev_script[9]) - 1, str(prev_out["value"]), sidechain.getnewaddress()))
		tx_hex = cht.read().split("\n")[0]
		assert(cht.close() == None)

		tx_hex = sidechain.signrawtransaction(tx_hex, [{"txid": args.sidechainClaimTx, "vout": 0, "scriptPubKey": prev_out["scriptPubKey"]["hex"], "redeemScript": p2sh_res["redeemScript"], "nValue": prev_out["serValue"]}], [sidechain.dumpprivkey(args.sidechainAddress)])
		if tx_hex["complete"] != True:
			print("Got incomplete transaction (signing failed to create spendable transaction):")
			print(tx_hex["hex"])
		else:
			print("Submitting tx to mempool...")
			sidechain.sendrawtransaction(tx_hex["hex"])
			print("Success!")

	elif args.command == "send-to-mainchain":
		p2sh_tx_test = bitcoin.decoderawtransaction(bitcoin.createrawtransaction([], {args.p2shMainAddress: 0.1}))["vout"][0]["scriptPubKey"]
		if p2sh_tx_test["type"] != "scripthash":
			print("You must use a P2SH address")
			exit(1)
		p2sh_hex = p2sh_tx_test["asm"].split(" ")[1]

		cht = os.popen('%s -create outscript=%s:"0x1850325348%s OP_DROP 0x20%s 0x14%s WITHDRAWPROOFVERIFY"' % (sidechain_tx_path, args.coinAmt, p2sh_hex, inverse_bitcoin_genesis_hash, secondScriptPubKeyHash))
		res_tx = cht.read().split("\n")[0]
		assert(cht.close() == None)

		donation = sidechain.fundrawtransaction(res_tx)["fee"]
		if donation > 0:
			if donation < 550: # Probably dust
				donation = 550
			cht = os.popen('%s -create outscript=%s:"0x1850325348%s OP_DROP 0x20%s 0x14%s WITHDRAWPROOFVERIFY" outscript=%s:"RETURN"' % (sidechain_tx_path, args.coinAmt, p2sh_hex, inverse_bitcoin_genesis_hash, secondScriptPubKeyHash, str(Decimal(donation) / Decimal(100000000))))
			res_tx = cht.read().split("\n")[0]
			assert(cht.close() == None)

		res_tx = sidechain.fundrawtransaction(res_tx)
		fee = res_tx["fee"]
		res_tx = sidechain.signrawtransaction(res_tx["hex"])["hex"]

		print("Sending %s to functionaries for withdraw to %s (fee of %s satoshis)..." % (args.coinAmt, args.p2shMainAddress, str(fee + donation)))
		txid = sidechain.sendrawtransaction(res_tx)
		print("Sent tx with id %s" % txid)

except JSONRPCException as e:
	print(traceback.format_exc())
	print("Got the following error from an RPC Call:")
	print(e.error)
