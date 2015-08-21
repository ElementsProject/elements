#!/usr/bin/env python2

import sys, os, json, traceback, decimal
sys.path.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../python-bitcoinrpc"))
from bitcoinrpc.authproxy import AuthServiceProxy, JSONRPCException
from rotating_consensus import RotatingConsensus
from threading import Lock, current_thread
from time import sleep
from constants import FedpegConstants

from httplib import CannotSendRequest
import socket

settings = FedpegConstants()
port = 14242

sidechain = [AuthServiceProxy(settings.sidechain_url), AuthServiceProxy(settings.sidechain_url)]
# We need to do a rescan on bitcoin, so we set a huge timeout
bitcoin = [AuthServiceProxy(settings.bitcoin_url, timeout=60*10), AuthServiceProxy(settings.bitcoin_url)]

spent_from_history = {}

open('spent_from.log', 'a').close()  # Touch file (create if not already present)
with open('spent_from.log') as f:
	for line in f.readlines():
		l = eval(line)
		if l[0] not in spent_from_history:
			spent_from_history[l[0]] = set()
		spent_from_history[l[0]].add(l[1])

spent_from_log = os.open("spent_from.log", os.O_CREAT | os.O_WRONLY | os.O_SYNC | os.O_DSYNC | os.O_APPEND)

def check_reset_connections():
	global sidechain, bitcoin
	connections_good = True

	try:
		sidechain[thread_id()].getblockcount()
	except CannotSendRequest as e:
		sidechain[thread_id()] = AuthServiceProxy(settings.sidechain_url)
		connections_good = False
	except socket.timeout as e:
		sidechain[thread_id()] = AuthServiceProxy(settings.sidechain_url)
		connections_good = False

	try:
		bitcoin[thread_id()].getblockcount()
	except CannotSendRequest as e:
		bitcoin[thread_id()] = AuthServiceProxy(settings.bitcoin_url)
		connections_good = False
	except socket.timeout as e:
		bitcoin[thread_id()] = AuthServiceProxy(settings.bitcoin_url)
		connections_good = False

	return connections_good

# If there are two outputs to the same destination, the first output must fully
# confirm before we allow the second to process.
# This is really for ease of developer headache, though we could change some
# indexes and allow this

map_lock = Lock()
# withdraw metadata map: {"txid_concat": sidechain_txid_concat, "sidechain_height": height,
#                         "script_gen": p2sh_script_in_asm_for_bitcoin-tx, "script_match": p2sh_script_in_hex,
#                         "value": value, "spent_from": set({frozenset({(bitcoin_txid, bitcoin_vout), ...}), ...})}
#                         (spent_from is a set of sets of inputs used in every tx which was signed signed and had output)
# sidechain txid_concat -> withdraw metadata map
outputs_pending = {}
# withdraw_target_p2sh_script_hex -> txid_concat (for withdraw_claims_pending use)
outputs_pending_by_p2sh_hex = {}
# withdraw_target_p2sh_script_hex -> [withdraw metadata map, ...]
outputs_waiting = {}

# utxo metadata map: {"redeem_info": redeem_info_for_bitcoin_signrawtransaction, "privateKey": gen_private_key, "value": Decimal(value),
#                     "spent_by": set(), "donated_map": {frozenset({(bitcoin_txid, bitcoin_vout), ...}): value} }
# spent_by is a set of sidechain txid_concats which can be used to look up in outputs_pending
# donated_map is a map from input sets to the value taken from donated_funds as a fee
# (bitcoin_txid, bitcoin_vout) -> utxo metadata map
utxos = {}

#set of sets of txos we need to ensure are spent by fraud proofs
fraud_check_map = {}

donated_funds = 0

manual_check_lock = Lock()
manual_check_set = set()

main_thread = current_thread()
def thread_id():
	if current_thread() == main_thread:
		return 0
	return 1

def check_raise(cond):
	if not cond:
		raise Exception("assertion failed")

def trigger_bitcoin_rescan():
	# TODO: Replace with a really random one, instead
	cht = os.popen("%s %s -c -p %s -a SALT -n %s" % (settings.contracthashtool_path, settings.cht_testnet_arg, settings.functionary_private_key, os.urandom(16).encode("hex")))
	useless_private_key = cht.read().split("\n")[0 + settings.is_testnet][16:]
	check_raise(cht.close() == None)
	# Trigger a rescan by importing something useless and new
	sys.stdout.write("Now triggering a full wallet rescan of the bitcoin chain...")
	sys.stdout.flush()
	bitcoin[thread_id()].importprivkey(useless_private_key, "", True)
	print("done")


def process_bitcoin_tx_for_utxos(tx, is_donation=False, manual_check=False):
	global donated_funds

	manual_check_lock.acquire()
	if not manual_check and tx["txid"] in manual_check_set:
		manual_check_set.remove(tx["txid"])
		return
	elif manual_check:
		manual_check_set.add(tx["txid"])
	manual_check_lock.release()

	# Go through the outputs, adding any coins sent to the raw functionary address to utxos
	for nout, outp in enumerate(tx["vout"]):
		if outp["scriptPubKey"]["type"] == "scripthash" and outp["scriptPubKey"]["addresses"][0] == settings.redeem_script_address:
			txo = tx["vout"][nout]
			map_lock.acquire()

			print("Got %s UTXO sent to raw functioanry address (change or donation): %s:%d" % ("new" if (tx["txid"], nout) not in utxos else "existing", tx["txid"], nout))
			utxos[(tx["txid"], nout)] = {"redeem_info": {"txid": tx["txid"], "vout": nout, "scriptPubKey": outp["scriptPubKey"]["hex"], "redeemScript": settings.redeem_script}, "privateKey": settings.functionary_private_key, "value": decimal.Decimal(outp["value"]), "spent_by": set(), "donated_map": {}}

			if is_donation:
				print("Got donation of %s, now possibly paying fees" % str(outp["value"]))
				donated_funds = donated_funds + outp["value"]

			map_lock.release()


def sign_withdraw_tx(tx_hex, txid_concat_list):
	global donated_funds

	tx_raw = bitcoin[thread_id()].decoderawtransaction(tx_hex)
	max_sidechain_height = sidechain[thread_id()].getblockcount() - 6

	check_raise(len(tx_raw["vout"]) == len(txid_concat_list) + 1)
	check_raise(tx_raw["vout"][-1]["scriptPubKey"]["type"] == "scripthash")
	check_raise(tx_raw["vout"][-1]["scriptPubKey"]["addresses"][0] == settings.redeem_script_address)

	tx_value = decimal.Decimal(0)
	privKeys = []
	redeemScripts = []
	inputs_set = set()
	input_size = 0
	for inp in tx_raw["vin"]:
		if (inp["txid"], inp["vout"]) not in utxos:
			# To-functionary UTXOs are only added after sufficient confirmations,
			# so we may need to find them here.
			spent_tx = bitcoin[thread_id()].getrawtransaction(inp["txid"], 1)
			process_bitcoin_tx_for_utxos(spent_tx, manual_check=True)

		check_raise((inp["txid"], inp["vout"]) in utxos)
		utxo = utxos[(inp["txid"], inp["vout"])]
		redeemScripts.append(utxo["redeem_info"])
		privKeys.append(utxo["privateKey"])
		tx_value = tx_value + decimal.Decimal(utxo["value"])

		inputs_set.add((inp["txid"], inp["vout"]))
		input_size = input_size + len(inp["scriptSig"]["hex"])/2
		if len(inp["scriptSig"]["hex"])/2 >= 0xfd:
			input_size += 2

	txid_concat_set = set()
	for i, txid_concat in enumerate(txid_concat_list):
		check_raise(txid_concat in outputs_pending)
		output = outputs_pending[txid_concat]
		check_raise(output["sidechain_height"] <= max_sidechain_height)

		tx_vout = tx_raw["vout"][i]
		check_raise(tx_vout["scriptPubKey"]["hex"] == output["script_match"])
		check_raise(decimal.Decimal(tx_vout["value"]) == output["value"])
		tx_value = tx_value - decimal.Decimal(tx_vout["value"])
		for input_set in output["spent_from"]:
			check_raise(not inputs_set.isdisjoint(input_set))

		txid_concat_set.add(txid_concat)

	# scriptSig is OP_0 x*(1-byte pushlen + 73-byte max-sized signature) + redeemScript push
	# if it triggers a long var-int for the scriptlen we have to include that, too
	RS_push_size = len(settings.redeem_script) / 2
	RS_push_size += 1 if RS_push_size <= 0x4b else (2 if RS_push_size <= 0xff else 3)
	scriptSig_size = 1 + 74 * settings.sigs_required + RS_push_size
	if scriptSig_size >= 0xfd:
		scriptSig_size += 2

	fee_allowed = len(tx_hex)/2 - input_size + scriptSig_size * len(tx_raw["vin"])
	fee_allowed = min(fee_allowed, donated_funds * 100000000)
	fee_paid = tx_value - decimal.Decimal(tx_raw["vout"][-1]["value"])
	check_raise(fee_paid * 100000000 <= fee_allowed)

	donated_funds = donated_funds - fee_paid

	inputs_set = frozenset(inputs_set)

	for txid_concat in txid_concat_list:
		output = outputs_pending[txid_concat]
		if inputs_set not in output["spent_from"]:
			output["spent_from"].add(inputs_set)
			os.write(spent_from_log, "['%s', %s]\n" % (txid_concat, repr(inputs_set)))

	old_paid_memory = -1
	for inp in tx_raw["vin"]:
		utxo = utxos[(inp["txid"], inp["vout"])]
		utxo["spent_by"] = utxo["spent_by"] | txid_concat_set
		old_paid = 0
		if inputs_set in utxo["donated_map"]:
			old_paid = utxo["donated_map"][inputs_set]
			if old_paid_memory == -1:
				old_paid_memory = old_paid
			elif old_paid != old_paid_memory:
				print("Internal data structure inconsistency!")
				sys.exit(1)
		utxo["donated_map"][inputs_set] = fee_paid + old_paid

	return bitcoin[thread_id()].signrawtransaction(tx_hex, redeemScripts, privKeys)["hex"]


class WatchPeerController(RotatingConsensus):
	round_local_tx_hex = ""

	def gen_master_msg(self):
		if not check_reset_connections():
			return None

		map_lock.acquire()
		try:

			max_sidechain_height = sidechain[thread_id()].getblockcount() - 8
			txid_concat_list_untried = []
			txid_concat_list_retries = []
			command_untried = '%s %s -create' % (settings.bitcoin_tx_path, settings.btc_testnet_arg)
			command_retries = command_untried
			input_sets_retries = set()
			input_pairs_retries = set()
			for txid_concat in outputs_pending:
				output = outputs_pending[txid_concat]
				if output["sidechain_height"] > max_sidechain_height:
					continue
				if len(output["spent_from"]) == 0:
					command_untried = command_untried + ' outscript=%.16g:"%s"' % (output["value"], output["script_gen"])
					txid_concat_list_untried.append(txid_concat)
				elif len(txid_concat_list_untried) == 0:
					all_still_spendable = True
					for input_set in output["spent_from"]:
						for input_pair in input_set:
							if bitcoin[thread_id()].gettxout(input_pair[0], input_pair[1], True) == None:
								all_still_spendable = False
								break
						if not all_still_spendable:
							break
					if all_still_spendable:
						command_retries = command_retries + ' outscript=%.16g:"%s"' % (output["value"], output["script_gen"])
						txid_concat_list_retries.append(txid_concat)
						input_sets_retries = input_sets_retries | output["spent_from"]
						for input_set in output["spent_from"]:
							input_pairs_retries = input_pairs_retries | input_set

			if len(txid_concat_list_untried) != 0:
				txid_concat_list = txid_concat_list_untried
				command = command_untried
			elif len(txid_concat_list_retries) != 0:
				inputs_required = []
				while len(input_sets_retries) != 0:
					e = max(input_pairs_retries, key=lambda x: len([i for i in input_sets_retries if x in i]))
					inputs_required.append(e)
					input_sets_retries = set([x for x in input_sets_retries if e not in x])
				for input_pair in inputs_required:
					command_retries = command_retries + ' in="%s":%d' % (input_pair[0], input_pair[1])

				txid_concat_list = txid_concat_list_retries
				command = command_retries
			else:
				return None

			cht = os.popen(command)
			tx_hex = cht.read().split("\n")[0]
			check_raise(cht.close() == None)

			funded_tx = bitcoin[thread_id()].fundrawtransaction(tx_hex, True)
			tx_raw = bitcoin[thread_id()].decoderawtransaction(funded_tx["hex"])
			change_value = decimal.Decimal(funded_tx["fee"]) + decimal.Decimal(tx_raw["vout"][funded_tx["changepos"]]["value"])

			cht = os.popen('%s %s %s delout=%d outaddr=%s:%s' % (settings.bitcoin_tx_path, settings.btc_testnet_arg, funded_tx["hex"], funded_tx["changepos"], "0", settings.redeem_script_address))
			tx_hex = cht.read().split("\n")[0]
			check_raise(cht.close() == None)

			redeem_script_push_size = len(settings.redeem_script)/2
			if redeem_script_push_size <= 0x4b:
				redeem_script_push_size += 1
			elif redeem_script_push_size <= 0xff:
				redeem_script_push_size += 2
			else:
				redeem_script_push_size += 3

			input_size = 1 + 74 * settings.sigs_required + redeem_script_push_size
			if input_size >= 0xfd:
				input_size += 2

			pay_fee = decimal.Decimal(len(tx_hex)/2 + input_size * len(tx_raw["vin"])) / decimal.Decimal(100000000)
			pay_fee = min(pay_fee, funded_tx["fee"])
			if pay_fee > donated_funds:
				pay_fee = 0
			print("Paying fee of %s" % str(pay_fee))
			change_value = change_value - pay_fee

			cht = os.popen('%s %s %s delout=%d outaddr=%s:%s' % (settings.bitcoin_tx_path, settings.btc_testnet_arg, tx_hex, len(tx_raw["vout"]) - 1, change_value, settings.redeem_script_address))
			tx_hex = cht.read().split("\n")[0]
			check_raise(cht.close() == None)

			self.round_local_tx_hex = sign_withdraw_tx(tx_hex, txid_concat_list)

			return json.dumps([self.round_local_tx_hex, txid_concat_list])
		finally:
			map_lock.release()

	def recv_master_msg(self, msg):
		msg_decoded = json.loads(msg)
		map_lock.acquire()
		try:
			self.round_local_tx_hex = sign_withdraw_tx(msg_decoded[0], msg_decoded[1])
			return self.round_local_tx_hex
		finally:
			map_lock.release()

	def round_done(self, peer_messages):
		txn_concat = self.round_local_tx_hex
		check_raise(txn_concat != "")

		input_list = []
		for inp in bitcoin[thread_id()].decoderawtransaction(txn_concat)["vin"]:
			input_list.append((inp["txid"], inp["vout"]))

		for msg in peer_messages:
			try:
				for i, inp in enumerate(bitcoin[thread_id()].decoderawtransaction(msg[1])["vin"]):
					check_raise(input_list[i] == (inp["txid"], inp["vout"]))
				txn_concat = txn_concat + msg[1]
			except:
				print("Peer %s sent invalid transaction" % msg[0])

		res = bitcoin[thread_id()].signrawtransaction(txn_concat)
		print("Final round result:")
		print(res)

		if res["complete"]:
			bitcoin[thread_id()].sendrawtransaction(res["hex"])
		return

	def round_failed(self):
		self.round_local_tx_hex = ""
		return


def process_sidechain_tx_for_utxos(tx, height, avoid_rescans):
	for vout, output in enumerate(tx["vout"]):
		if output["scriptPubKey"]["type"] == "withdrawout":
			outp = output["scriptPubKey"]["asm"].split(" ")
			check_raise(len(outp) == 16)

			bitcoin_tx = outp[2]
			bitcoin_raw_tx = bitcoin[thread_id()].getrawtransaction(bitcoin_tx, 1)
			txo = bitcoin_raw_tx["vout"][int(outp[3])]

			inp = tx["vin"][vout]["scriptSig"]["asm"].split(" ")
			contract = inp[2]

			cht = os.popen("%s %s -g -r %s -f %s" % (settings.contracthashtool_path, settings.cht_testnet_arg, settings.redeem_script, contract))
			cht_out = cht.read()
			check_raise(cht.close() == None)
			modified_redeem_script = cht_out.split("\n")[2 + settings.is_testnet][24:]
			modified_address = cht_out.split("\n")[3 + settings.is_testnet][40:]
			bitcoin[thread_id()].importaddress(modified_redeem_script, "", not avoid_rescans, True)

			cht = os.popen("%s %s -c -p %s -f %s" % (settings.contracthashtool_path, settings.cht_testnet_arg, settings.functionary_private_key, contract))
			gen_private_key = cht.read().split("\n")[0 + settings.is_testnet][16:]
			check_raise(cht.close() == None)

			outp[3] = int(outp[3])

			map_lock.acquire()
			already_had = (bitcoin_tx, outp[3]) in utxos
			utxos[(bitcoin_tx, outp[3])] = {"redeem_info": {"txid": bitcoin_tx, "vout": outp[3], "scriptPubKey": txo["scriptPubKey"]["hex"], "redeemScript": modified_redeem_script}, "privateKey": gen_private_key, "value": decimal.Decimal(txo["value"]), "spent_by": set(), "donated_map": {}}
			if already_had:
				if height not in fraud_check_map:
					fraud_check_map[height] = []
				fraud_check_map[height].append((tx["txid"], vout))
			map_lock.release()

			print("Got %s UTXO (%s:%d) from sidechain tx %s:%d" % ("new" if not already_had else "existing", bitcoin_tx, outp[3], tx["txid"], vout))

def process_sidechain_tx_for_withdraw(tx, height):
	for vout, output in enumerate(tx["vout"]):
		if output["scriptPubKey"]["type"] == "withdraw":
			outp = output["scriptPubKey"]["asm"].split(" ")
			if len(outp) == 5 and outp[2] == settings.inverse_bitcoin_genesis_hash and outp[3] == settings.secondScriptPubKeyHash:
				check_raise(outp[1] == "OP_DROP" and outp[4] == "OP_WITHDRAWPROOFVERIFY")
				if outp[0][0:8] != "50325348":
					continue
				contract = outp[0][8:]
				check_raise(len(contract) == 40)

				p2sh_script = "OP_HASH160 0x14%s OP_EQUAL" % outp[0][8:]
				p2sh_hex = "a914%s87" % outp[0][8:]
				txid_concat = tx["txid"] + ":" + str(vout)
				value = decimal.Decimal(output["value"])
				if txid_concat in spent_from_history:
					output = {"txid_concat": txid_concat, "sidechain_height": height, "script_gen": p2sh_script, "script_match": p2sh_hex, "value": value, "spent_from": spent_from_history[txid_concat]}
				else:
					output = {"txid_concat": txid_concat, "sidechain_height": height, "script_gen": p2sh_script, "script_match": p2sh_hex, "value": value, "spent_from": set()}

				# We track the set of inputs (from the utxos map) from which we've sent the withdraw,
				# freely signing double-spends, but never allowing two non-conflicting withdraws
				map_lock.acquire()
				if txid_concat in outputs_pending:
					print("Re-ran process_sidechain_tx_for_withdraw with existing withdraw: %s???" % txid_concat)
					sys.exit(1)
				if p2sh_hex in outputs_pending_by_p2sh_hex:
					if p2sh_hex in outputs_waiting:
						outputs_waiting[p2sh_hex].append(output)
					else:
						outputs_waiting[p2sh_hex] = [output]

					print("Got new txo for withdraw (waiting on previous tx %s): %s" % (txid_concat, outputs_pending_by_p2sh_hex[p2sh_hex]))
					map_lock.release()
					continue

				outputs_pending[txid_concat] = output
				outputs_pending_by_p2sh_hex[p2sh_hex] = txid_concat
				print("Got new txo for withdraw: %s (to %s with value %s)" % (txid_concat, p2sh_hex, str(value)))
				map_lock.release()

def process_sidechain_blockchain(min_height, max_height, avoid_rescan):
	for height in range(min_height, max_height):
		block = sidechain[thread_id()].getblock(sidechain[thread_id()].getblockhash(height))
		for tx in sidechain[thread_id()].batch_([["getrawtransaction", txhash, 1] for txhash in block["tx"]]):
			process_sidechain_tx_for_utxos(tx, height, avoid_rescan)
			process_sidechain_tx_for_withdraw(tx, height)

def process_confirmed_sidechain_blockchain(min_height, max_height):
	global donated_funds

	for height in range(min_height, max_height):
		map_lock.acquire()
		fraud_check_list = None
		if height in fraud_check_map:
			fraud_check_list = fraud_check_map[height]
			del fraud_check_map[height]
		map_lock.release()
		if fraud_check_list != None:
			for txo in fraud_check_list:
				if sidechain[thread_id()].gettxout(txo[0], txo[1], False) != None:
					print("NO FRAUD PROOF GENERATED WITHIN CONFIRMATION PERIOD FOR TXO %s" % str(txo))
					sys.exit(1)

		block = sidechain[thread_id()].getblock(sidechain[thread_id()].getblockhash(height))
		for tx in sidechain[thread_id()].batch_([["getrawtransaction", txhash, 1] for txhash in block["tx"]]):
			for outp in tx["vout"]:
				if outp["scriptPubKey"]["type"] == "nulldata":
					map_lock.acquire()
					donated_funds += outp["value"]
					map_lock.release()


def process_confirmed_bitcoin_blockchain(min_height, max_height):
	global donated_funds

	for height in range(min_height, max_height):
		block = bitcoin[thread_id()].getblock(bitcoin[thread_id()].getblockhash(height))
		for tx in bitcoin[thread_id()].batch_([["getrawtransaction", txhash, 1] for txhash in block["tx"]]):
			map_lock.acquire()
			is_withdraw = False
			is_not_withdraw = False
			tx_value = 0

			# First process the inputs, checking if its a withdraw transaction (ie spends from utxos)
			# then remove that utxo, including from ensure-double-spend-sets in outputs_pending
			for inp in tx["vin"]:
				if "coinbase" in inp:
					continue

				txid_pair = (inp["txid"], inp["vout"])
				if txid_pair not in utxos:
					if is_withdraw:
						print("Got transaction that spent both functionary utxos and non-functionary utxos...very confused")
						sys.exit(1)
					is_not_withdraw = True
				else:
					if is_not_withdraw:
						print("Got transaction that spent both functionary utxos and non-functionary utxos...very confused")
						sys.exit(1)
					is_withdraw = True

					utxo = utxos[txid_pair]

					for txid_concat in utxo["spent_by"]:
						if txid_concat in outputs_pending:
							new_spent_from = set()
							output = outputs_pending[txid_concat]
							for inputs_set in output["spent_from"]:
								if txid_pair not in inputs_set:
									new_spent_from.add(inputs_set)
							output["spent_from"] = new_spent_from

					# Calculate donated_funds by re-adding all temporary removals that this invalidated
					total_donated_value = 0
					for txid_set in utxo["donated_map"]:
						donated_value = utxo["donated_map"][txid_set]
						for txid_pair_it in txid_set:
							if txid_pair_it == txid_pair:
								continue

							if utxos[txid_pair_it]["donated_map"][txid_set] != donated_value:
								print("Internal data structure inconsistency")
								sys.exit(1)
							del utxos[txid_pair_it]["donated_map"][txid_set]

						total_donated_value = total_donated_value + donated_value
					donated_funds = donated_funds + total_donated_value

					tx_value = tx_value + utxo["value"]
					del utxos[txid_pair]

			# Then go through outputs, removing them from outputs_pending and warning if
			# we dont know where the money went
			if is_withdraw:
				for outp in tx["vout"]:
					script_asm = outp["scriptPubKey"]["hex"]
					if script_asm in outputs_pending_by_p2sh_hex:
						sys.stdout.write("Successfully completed withdraw for sidechain tx %s in bitcoin tx %s:%d" % (outputs_pending_by_p2sh_hex[script_asm], tx["txid"], outp["n"]))

						del outputs_pending[outputs_pending_by_p2sh_hex[script_asm]]
						del outputs_pending_by_p2sh_hex[script_asm]

						if script_asm in outputs_waiting:
							output = outputs_waiting[script_asm].pop(0)
							outputs_pending[output["txid_concat"]] = output
							outputs_pending_by_p2sh_hex[script_asm] = output["txid_concat"]
							if len(outputs_waiting[script_asm]) == 0:
								del outputs_waiting[script_asm]
							sys.stdout.write("...next output to same address is %s" % output["txid_concat"])

						sys.stdout.write("\n")
						sys.stdout.flush()

					elif outp["scriptPubKey"]["type"] != "scripthash" or outp["scriptPubKey"]["addresses"][0] != settings.redeem_script_address:
						print("MONEY MOVED FROM FUNCTIONARY OUTPUT TO UNKNOWN DESTINATION!!!!")
						print("In transaction %s in output %d" % (tx["txid"], outp["n"]))
						sys.exit(1)

					tx_value = tx_value - outp["value"]

				# Remove fee from donated_funds
				if tx_value > 0:
					donated_funds = donated_funds - tx_value

			map_lock.release()

			# Finally, without map_lock held (we'll grab it again if needed in process_bitcoin_tx_for_utxos),
			# we add any outputs which are to the functionary address to the utxos set.
			process_bitcoin_tx_for_utxos(tx, not is_withdraw)

try:
	print("Doing chain-scan init...")

	print("Step 1. Sidechain blockchain scan for coins in and withdraws...")
	# First do a pass over all existing blocks to collect all utxos
	sidechain_block_count = sidechain[thread_id()].getblockcount()
	process_sidechain_blockchain(1, sidechain_block_count, True)
	process_confirmed_sidechain_blockchain(1, sidechain_block_count - 5)
	print("done")

	print("Step 2. Bitcoin blockchain scan for withdraws completed and coins to functionaries...")
	bitcoin_block_count = bitcoin[thread_id()].getblockcount()
	process_confirmed_bitcoin_blockchain(447000, bitcoin_block_count - 5)
	print("done")

	sys.stdout.write("Step 3. Bitcoin blockchain rescan to load functionary outputs in wallet...")
	sys.stdout.flush()
	bitcoin[thread_id()].importaddress(settings.redeem_script, "", False, True)
	trigger_bitcoin_rescan()
	print("done")

	print("Init done. Joining rotating consensus and watching chain for withdraws...")
	#TODO: Change interval to ~60
	settings.nodes.remove(settings.my_node)
	WatchPeerController(settings.nodes, settings.my_node, port, 10, settings.socks_proxy)

	print("Outputs to be created:")
	for txid_concat in outputs_pending:
		sys.stdout.write(" " + txid_concat)
	print("\nOutputs waiting:")
	for p2sh_hex in outputs_waiting:
		for output in outputs_waiting[p2sh_hex]:
			sys.stdout.write(" " + output["txid_concat"])
	print("")

	while True:
		if not check_reset_connections():
			sleep(1)
			continue

		new_block_count = sidechain[thread_id()].getblockcount()
		process_sidechain_blockchain(sidechain_block_count, new_block_count, False)
		process_confirmed_sidechain_blockchain(sidechain_block_count - 5, new_block_count - 5)
		sidechain_block_count = new_block_count

		if not check_reset_connections():
			sleep(1)
			continue

		new_block_count = bitcoin[thread_id()].getblockcount()
		process_confirmed_bitcoin_blockchain(bitcoin_block_count - 5, new_block_count - 5)
		bitcoin_block_count = new_block_count

		sleep(1)

except JSONRPCException as e:
	print(e.error)
	print(traceback.format_exc())
