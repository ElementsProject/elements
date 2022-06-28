#!/usr/bin/env python3

from test_framework.authproxy import JSONRPCException
from test_framework.daemon import Daemon, sync_all
import argparse

# PSET Swap Tutorial
#
# This script demonstrates how to implement an atomic swap, using a single
# Elements transaction, between two parties, Alice and Carol. Alice has
# ten thousand BTC and Carol has 1000 of a new asset. After the swap, Alice
# will have the new asset and Carol will have the BTC.
#
# This script can be executed in a Python interpreter. The user is encouraged
# to add tracing or debugging code throughout to better understand what is
# going on.
#

# 0. Boilerplate to make the tutorial executable as a script
#
# Skip ahead to step 1 if you are reading
#

# Parse arguments
parser = argparse.ArgumentParser()
parser.add_argument("--elementsd-dir", type=str, default="./src")
parser.add_argument("--no-cleanup", default=False, action="store_true")

args = parser.parse_args()

# Setup daemons
alice = Daemon(
    "Alice",
    "elements",
    args.elementsd_dir + "/elementsd",
    "contrib/assets_tutorial/elements1.conf",
    not args.no_cleanup,
)

carol = Daemon(
    "Carol",
    "elements",
    args.elementsd_dir + "/elementsd",
    "contrib/assets_tutorial/elements2.conf",
    not args.no_cleanup,
)

# 1. Start nodes
print ("1. Start nodes and setup scenario")

# 1a. Turn on both nodes. Disable -validatepegin as we will just swap the
#     initialcoins asset with a newly issued asset. Using the peg would
#     be an inessential distraction.
#
alice.start(["-validatepegin=0"])
carol.start(["-validatepegin=0"])
alice.connect_to(carol)
carol.connect_to(alice)
alice.createwallet("wallet")
carol.createwallet("wallet")
alice.rescanblockchain()

# 1b. Split the initial coins so that both sides have some (but Alice has more)
alice.sendmany("", { alice.getnewaddress(): 10000 for x in range(0, 10) })
alice.sendtoaddress(carol.getnewaddress(), 100000)
alice.generatetoaddress(1, alice.getnewaddress())

# 1c. Issue 1000 units of a new asset. No reissuance tokens. Send them
#     all to the second node.
issue = alice.issueasset(1000, 0)
alice.sendtoaddress(address=carol.getnewaddress(), amount=1000, assetlabel=issue["asset"])
alice.generatetoaddress(1, alice.getnewaddress())
sync_all([alice, carol])

# 1d. Move the coins around on each wallet so that they do not share
#     any wallet transaction. (Otherwise they may fill in each others'
#     UTXO data, which is harmless but makes the tutorial harder to
#     follow.)
alice.sendtoaddress(alice.getnewaddress(), alice.getbalance()["bitcoin"], "", "", True)
carol.sendtoaddress(carol.getnewaddress(), carol.getbalance()["bitcoin"], "", "", True)
carol.sendtoaddress(address=carol.getnewaddress(), amount=1000, assetlabel=issue["asset"])
sync_all([alice, carol])
alice.generatetoaddress(1, alice.getnewaddress())
sync_all([alice, carol])

# Define some variables and continue..
asset_ALT = issue["asset"]
asset_BTC = alice.dumpassetlabels()["bitcoin"]

assert len(alice.listunspent()) > 0
assert len(carol.listunspent()) > 0

# 2. Construct a swap transaction in PSET format
#
# At this point node `alice` has 10.5MM "bitcoin" and node `carol` has 1000 of
# a new asset. We want to do an atomic swap: 2500 BTC for 1000 of
# the new asset.
#
print ("2. Create an unsigned swap transaction in PSET format.")

#
# Although PSBT2 was designed with coinjoining in mind, the RPC interface
# currently does not support iteratively creating a transaction. So we must
# create the coinjoin transaction using the raw transaction API.
#
# Our strategy will be for both parties to create single transactions, then
# we will manually combine them.
#
# This step is fairly complicated and will be significantly simplified by
# future RPC improvements.
#

# First, each party generates a new address
print ("2a. Exchange addresses")
alice_addr = alice.getnewaddress()
carol_addr = carol.getnewaddress()
print ("    Alice: ", alice_addr)
print ("    Carol: ", carol_addr)

# Then they each create and fund (but don't sign!) partial transactions
# which simply send the assets to each other.
print ("2b. Exchange partial transaction data")
raw_tx_a = alice.createrawtransaction(outputs=[{carol_addr: 2500}])
funded_a = alice.fundrawtransaction(raw_tx_a)['hex']

raw_tx_c = carol.createrawtransaction(outputs=[{alice_addr: 1000, "asset": asset_ALT}])
funded_c = carol.fundrawtransaction(raw_tx_c)['hex']

# Each party cross-checks the other's transaction
print ("2c. Check partial transactions")
decoded_a = carol.decoderawtransaction(funded_a)

carol_spk = carol.validateaddress(carol_addr)['scriptPubKey']
found_my_output = False
feerate = None
for output in decoded_a["vout"]:
    if output["scriptPubKey"]["type"] == "fee" and output["asset"] == asset_BTC:
        # Feerate multiplier is 10^8 (btc->sat) / 10^3 (bytes->kb) to get a value in sat/kb
        feerate = 100000.0 * float(output["value"]) / decoded_a["vsize"]
    if output["scriptPubKey"]["type"] == "witness_v0_keyhash" \
       and output["scriptPubKey"]["hex"] == carol_spk \
       and output["asset"] == asset_BTC \
       and output["value"] == 2500:
        found_my_output = True

assert feerate > 0.1 # should probably compare against your own feerate
assert found_my_output

#
# Check that none of the inputs in the counterparty's transaction actually
# belong to us. This is the second-most important check (after making sure
# that your outputs are present :)) and by far the easiest to forget. Do
# not forget this!!!
#

# The way we do this check in Python is by making a set of each
# output the wallet can spend...
my_unspent = { (x["txid"], x["vout"]) for x in carol.listunspent() if x["spendable"] }
# ...then making sure that none of the inputs in the counterparty's
# transaction appear in this set.
for inp in decoded_a["vin"]:
    assert not (inp["txid"], inp["vout"]) in my_unspent

# ...and same on Alice's end. We don't bother repeating the checks
# in this script but they should be done.
decoded_c = alice.decoderawtransaction(funded_c)

print ("2d. Create combined transaction")

#
# Once each party has cross-checked the counterparty's transaction, they can
# just combine the two. There is no need to communicate here since both parties
# will construct the same transaction. To eliminate all ambiguity we sort inputs
# by txid:vout and sort outputs by scriptPubKey.
#

inputs = sorted(
    decoded_a["vin"] + decoded_c["vin"],
    key = lambda vin: vin["txid"] + str(vin["vout"])
)
outputs = sorted(
    decoded_a["vout"] + decoded_c["vout"],
    key = lambda vout: vout["scriptPubKey"]["hex"]
)
# Sorting by scriptPubKey will put the fee outputs first
first_fee = outputs[0]
outputs = outputs[1:]
outputs[0]["value"] += first_fee["value"]

# Determine blinder indices from inputs
alice_idx = None
carol_idx = None
for n, inp in enumerate(inputs):
    if inp in decoded_a["vin"]:
        alice_idx = n
    elif inp in decoded_c["vin"]:
        carol_idx = n

# Convert inputs and outputs to a format needed by `createpsbt`
inputs_createpsbt = [{"txid": x["txid"], "vout": x["vout"], "sequence": 0xffffffff} for x in inputs]
outputs_createpsbt = []

for out in outputs:
    blinder_idx = None
    if out["scriptPubKey"]["type"] == "fee":
        address = "fee"
    else:
        if out in decoded_a["vout"]:
            blinder_idx = alice_idx
        elif out in decoded_c["vout"]:
            blinder_idx = carol_idx

        # The crappy rawtransaction API requires that we reconstruct blinded addresses,
        # which are split between the "addresses" and "nonce" field
        address = out["scriptPubKey"]["addresses"][0]
        if "commitmentnonce" in out:
            address = alice.createblindedaddress(address, out["commitmentnonce"])

    if blinder_idx is None:
        outputs_createpsbt.append({address: out["value"], "asset": out["asset"]})
    else:
        outputs_createpsbt.append({address: out["value"], "asset": out["asset"], "blinder_index": blinder_idx})

alice_pset = alice.createpsbt(inputs_createpsbt, outputs_createpsbt)
carol_pset = alice.createpsbt(inputs_createpsbt, outputs_createpsbt)
assert alice_pset == carol_pset
print ("Created PSET: ", alice_pset)

# Use `analyzepsbt` to see what's happening
analysis = alice.analyzepsbt(alice_pset)
assert analysis["next"] == "updater"
assert not any([x["has_utxo"] for x in analysis["inputs"]])
assert not any([x["is_final"] for x in analysis["inputs"]])
assert all([x["next"] == "updater" for x in analysis["inputs"]])

# 3. Update the PSET
#
# Before blinding can take place, both parties need to provide UTXO data
# for their inputs. They can share this data by either updating the PSET
# in turn, or by both updating their copies and then one party calls
# `combinepsbt` to combine the results.
#
# We will do the latter since `combinepsbt` will automatically check that
# neither party changed the transaction out from under the other.
#

print ("3. Both parties fill in their UTXO data.")
alice_pset = alice.walletprocesspsbt(alice_pset)["psbt"]
carol_pset = carol.walletprocesspsbt(carol_pset)["psbt"]
filled_pset = alice.combinepsbt([alice_pset, carol_pset])

# Use `analyzepsbt` to see what's happening
analysis = alice.analyzepsbt(filled_pset)
assert analysis["next"] == "blinder"
assert all([x["has_utxo"] for x in analysis["inputs"]])
assert not any([x["is_final"] for x in analysis["inputs"]])
assert all([x["next"] == "signer" for x in analysis["inputs"]])

# 4. Blind the PSET
#
# Both parties now blind the PSET. Importantly, the final person to blind must
# have a combined PSET that has everyone else's blinding data included, so that
# they can make the blinding factors add up.
#
# The most straightforward way to implement this is to have each party blind
# the PSET, then pass to the next party, who blinds in-turn. If there are more
# than 2 parties, then you can have all parties but one blind independently,
# `combinepsbt` the results, and give this to the final party to blind.
#
# In the two-party case these are equivalent.
#

# Just for fun, try to have both parties blind independently and combine. This
# will fail because `combinepsbt` needs there to be at least one remaining
# unblinded output.
alice_blinded = alice.walletprocesspsbt(filled_pset)
carol_blinded = carol.walletprocesspsbt(filled_pset)
try:
    alice.combinepsbt([alice_blinded["psbt"], carol_blinded["psbt"]])
except JSONRPCException:
    pass
else:
    raise Exception("combinepsbt should return 'Cannot combine PSETs as the values and blinders would become imbalanced'")

# Ok, back to the tutorial
print ("4. One party blinds the PSET and passes to the other party, who also blinds")
# We set sign=False here, because otherwise carol's `walletprocesspsbt`
# will sign the transaction (since after she does her blinding, the
# transaction will be completely blinded and therefore signable).
# But for this tutorial we want that to happen only in the next step.
alice_blinded = alice.walletprocesspsbt(filled_pset)
# Alice gives `alice_blinded` to Carol, who uses `combinepsbt` to verify
# that Alice blinded honestly (not changing any of the output amounts/assets)
carol.combinepsbt([filled_pset, alice_blinded["psbt"]])
# If this passes (does not throw any exception) she can blind.
carol_blinded = carol.walletprocesspsbt(psbt=alice_blinded["psbt"], sign=False)
# Similarly, Carol passes the result to Alice, who checks it
carol.combinepsbt([alice_blinded["psbt"], carol_blinded["psbt"]])
# Now both parties have a copy of the fully-blinded transaction.
blinded = carol_blinded

# We won't print these out because they're very big now
assert not alice_blinded["complete"]
assert not carol_blinded["complete"]
assert len(blinded["psbt"]) > 5000
assert len(blinded["psbt"]) > 10000

# Use `analyzepsbt` to see what's happening
analysis = alice.analyzepsbt(blinded["psbt"])
assert analysis["next"] == "signer"
assert all([x["has_utxo"] for x in analysis["inputs"]])
assert not any([x["is_final"] for x in analysis["inputs"]])
assert all([x["next"] == "signer" for x in analysis["inputs"]])

# 5. Sign the PSET
#
# When signing, there are a couple options for workflows. Each party can sign
# in turn, like we did when blinding, or they can each sign independently and
# then combine the results with `combinepsbt`. We choose the latter one (a) for
# demonstration purposes.
#

print ("5. Both parties sign the PSET")

alice_signed = alice.walletprocesspsbt(blinded["psbt"])
carol_signed = carol.walletprocesspsbt(blinded["psbt"])
assert not alice_signed["complete"]
assert not carol_signed["complete"]

complete = alice.combinepsbt([alice_signed["psbt"], carol_signed["psbt"]])

# Use `analyzepsbt` to see what's happening
analysis = alice.analyzepsbt(complete)
assert analysis["next"] == "extractor"
assert all([x["has_utxo"] for x in analysis["inputs"]])
assert all([x["is_final"] for x in analysis["inputs"]])
assert all([x["next"] == "extractor" for x in analysis["inputs"]])

print ("6. Finalize and Extract")
x = alice.finalizepsbt(complete, True)
assert x["complete"]
# The complete transaction is in x["hex"] but again we won't print it because
# it's massive.



