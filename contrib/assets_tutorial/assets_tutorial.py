#!/usr/bin/env python3

from test_framework.authproxy import AuthServiceProxy, JSONRPCException
import argparse
import os
import pathlib
import sys
import tempfile
import time
import subprocess
import shutil
from decimal import Decimal

## 0. Boilerplate to make the tutorial executable as a script
#
# Skip ahead to step 1 if you are reading
#

# Parse arguments
parser = argparse.ArgumentParser()
parser.add_argument('--elementsd-dir', type=str, default='./src')
parser.add_argument('--bitcoind-dir', type=str, default='../bitcoin/src')
parser.add_argument('--no-cleanup', default=False, action="store_true")

args = parser.parse_args()

class Daemon():
    """
    A class for representing a bitcoind or elementsd node.

    Wraps the process management, creation and deletion of datadirs, and
    RPC connectivity, into a simple object that will clean itself up on
    exit. The `cleanup_on_exit` parameter can be set to False to prevent
    the node from deleting its datadir on restart (and can be set by
    passing --no-cleanup to the main program).
    """

    def __init__(self, name, daemon, path, conf_path, cleanup_on_exit = True):
        self.name = name
        self.daemon = daemon
        self.conf_path = path
        self.path = path
        self.cleanup_on_exit = cleanup_on_exit
        self.conf_path = conf_path
        self.datadir_path = None
        self.proc = None
        self.rpc = None

        # Parse config
        self.config = {}
        with open(self.conf_path, encoding="utf8") as f:
            for line in f:
                if len(line) == 0 or line[0] == "#" or len(line.split("=")) != 2:
                    continue
                self.config[line.split("=")[0]] = line.split("=")[1].strip()

    def shutdown(self):
        if self.proc is not None:
            print ("Shutting down %s" % self.name)
            self.proc.terminate()
            ## FIXME determine why we need 30+ seconds to shut down with a tiny regtest chain
            self.proc.wait(120)
            self.proc = None

        if self.datadir_path is not None:
            if self.cleanup_on_exit:
                shutil.rmtree(self.datadir_path)
            else:
                print ("Leaving %s datadir at %s." % (self.name, self.datadir_path))

    def start(self, ext_args = None, keep_datadir = False):
        if keep_datadir and self.datadir_path is not None:
            temp = self.datadir_path
            self.datadir_path = None
            self.shutdown()
            self.datadir_path = temp
        else:
            self.shutdown()
            # Create datadir and copy config into place
            self.datadir_path = tempfile.mkdtemp()
            shutil.copyfile(self.conf_path, self.datadir_path + '/' + self.daemon + '.conf')
            print("%s datadir: %s" % (self.name, self.datadir_path))

        # Start process
        print ("Starting %s" % self.name)
        if ext_args is None:
            ext_args = []
        self.proc = subprocess.Popen([self.path, "-datadir=" + self.datadir_path] + ext_args)
        self.rpc = AuthServiceProxy("http://" + self.config["rpcuser"] + ":" + self.config["rpcpassword"] + "@127.0.0.1:" + self.config["rpcport"])

        # Give daemon a moment to start up
        time.sleep(1)

    def connect_to(self, other):
        self.addnode("localhost:%s" % other.config['port'], "onetry")

    def restart(self, ext_args = None, keep_datadir = False):
        self.start(ext_args, keep_datadir)

    def __del__(self):
        self.shutdown()

    def __getattr__(self, name):
        """Dispatches any unrecognised messages to the RPC connection or a CLI instance."""
        return self.rpc.__getattr__(name)

    def __getitem__(self, key):
        """Dispatches any keys to the underlying config file"""
        return self.config[key]

def sync_all(nodes, timeout_sec = 10):
    totalWait = timeout_sec

    stop_time = time.time() + timeout_sec
    while time.time() <= stop_time:
        best_hash = [x.getbestblockhash() for x in nodes]
        if best_hash.count(best_hash[0]) == len(nodes):
            break
        time.sleep(1)
    while time.time() <= stop_time:
        pool = [set(x.getrawmempool()) for x in nodes]
        if pool.count(pool[0]) == len(nodes):
            return
        time.sleep(1)
    raise Exception("Nodes cannot sync blocks or mempool!")

# Setup daemons
bitcoin = Daemon(
    "Bitcoin",
    "bitcoin",
    args.bitcoind_dir + "/bitcoind",
    "contrib/assets_tutorial/bitcoin.conf",
    not args.no_cleanup,
)

e1 = Daemon(
    "Elements1",
    "elements",
    args.elementsd_dir + "/elementsd",
    "contrib/assets_tutorial/elements1.conf",
    not args.no_cleanup,
)

e2 = Daemon(
    "Elements2",
    "elements",
    args.elementsd_dir + "/elementsd",
    "contrib/assets_tutorial/elements2.conf",
    not args.no_cleanup,
)

## 1. Start nodes
print ("1. Start nodes")
#
# 1a. Confirm that we not start an elements node if validatepegin is set and there
#     is no bitcoind. When validatepegin is set, elementsd attempts to connect to
#     bitcoind to check if peg-in transactions are confirmed in the Bitcoin chain.
#
# Alternatively, you can set validatepegin=0 (it defaults to being on) in the
# elementsd config, and run it without a Bitcoin node, but this means that you
# will not be fully validating the two-way peg.
print ("1a. Attempting to start a validatepegin daemon without a bitcoind (will fail)")

assert e1["validatepegin"] == "1"

e1.start()
try:
    e1.getinfo()
    print ("ERROR: was able to start an elementsd without a working bitcoind")
    sys.exit(1)
except:
    pass

# 1b. Start bitcoind, then elementsd. Initially, the bitcoind may be warming up and
#     inaccessible over RPC. elementsd can detect this case and will stall until the
#     bitcoind is warmed up.
print ("1b. Attempting to start validatepegin daemons with a bitcoind (will succeed)")

bitcoin.start()
e1.start()
e2.start()

# Connect the nodes. This can also be accomplished with the `connect=` config
# parameter, but when starting two nodes simultaneously, this is unreliable.
e1.connect_to(e2)
e2.connect_to(e1)

# 1c. Create a wallet on the Elements nodes. This is needed since version 0.21
#     of the daemon; previously a wallet was created by default if one does not
#     already exist.
print ("1c. Creating wallets on all daemons")

# We have configured this regtest chain to start with 21M bitcoins, which are initally
# in a single OP_TRUE output. All Elements wallets recognize OP_TRUE outputs as their
# own (this differs from Bitcoin), so the 21M bitcoins are immediately available for
# use. This can be disabled by setting `anyonecanspend_aremine=0` in the daemon config.
#
# This is useful for testing basic functionality and for blockchains that have no peg,
# since every blockchain needs a default "policy asset". This policy asset is used
# for transaction fees (which are required for anti-DoS purposes). Also, asset
# issuances require some pre-existing asset, since they consume inputs for entropy.
#
# To separate the policy asset (used for fees) from the peg asset, use the `-policyasset`
# configuration value.
#
# In Elements there is no block subsidy. In a production sidechain, `initialfreecoins`
# will likely be set to zero, necessitating peg-in functionality to get a policy asset.

e1.createwallet("wallet1")
e2.createwallet("wallet2")

# Because of https://github.com/ElementsProject/elements/issues/956 we need to run
# `rescanblockchain` after creating the wallets to detect the `TRUE` outputs
assert e1["initialfreecoins"] == "2100000000000000"
assert e1.getwalletinfo()['balance'] == { 'bitcoin': 0 }
e1.rescanblockchain()
e2.rescanblockchain()
assert e1.getwalletinfo()['balance'] == { 'bitcoin': 21000000 }
assert e2.getwalletinfo()['balance'] == { 'bitcoin': 21000000 }
# All the initial coins coins are in one UTXO
assert len(e1.listunspent()) == 1
# ...and both nodes think they own it. This is a common situation when
# using near-empty test chains, so be aware of it.
assert e1.listunspent() == e2.listunspent()

# Generate 10 blocks to demonstrate how block generation work. On our test chain,
# each block has a subsidy of zero (this can be changed with `con_blocksubsidy`)
# and sends the coins to an OP_TRUE output (this script can be changed with
# the `-signblockscript` config).
e1.generatetoaddress(10, e1.getnewaddress())
# The wallet does not recognize zero-valued outputs as being owned
assert len(e1.listunspent()) == 1
assert e1.getwalletinfo()['balance'] == { 'bitcoin': 21000000 }

# Synchronize the chains
sync_all([e1, e2])
assert e1.getblockcount() == 10
assert e1.getbestblockhash() == e2.getbestblockhash()

## 2. Basic wallet usage
print ("")
print ("2. Basic wallet usage")

# 2a. Send all the coins to e1
#     Observe that this address is a confidential address (is much longer
#     than an ordinary address). Using the `validateaddress` RPC, you can
#     see details of the address, including its unconfidential version.
addr = e1.getnewaddress()
print ("2a. Sending all initial coins to e1 (address %s)", addr)
txid1 = e1.sendtoaddress(addr, 21000000, "", "", True)
e1.generatetoaddress(1, e1.getnewaddress())
sync_all([e1, e2])
assert len(e1.listunspent()) == 1  # change output, but no coinbase
assert len(e2.listunspent()) == 0

# 2b. Send half of these to e2
addr = e2.getnewaddress()
print ("2b. Sending half to e2 (address %s)." % addr)
txid2 = e1.sendtoaddress(addr, 10500000, "", "", False)
e1.generatetoaddress(1, e1.getnewaddress())
assert len(e1.listunspent()) == 1  # change output, but no coinbase
e1.generatetoaddress(99, e1.getnewaddress())
assert len(e1.listunspent()) == 2  # change output, and coinbase with fees from first transaction
e1.generatetoaddress(1, e1.getnewaddress())
assert len(e1.listunspent()) == 3  # ...and fees from the second transaction
sync_all([e1, e2])
assert len(e2.listunspent()) == 1

# Funds should now be evenly split between the two wallets. e2 directly
# received 10500000, while e1 has the remainder, less fees (because it
# created the transactions), plus fees (because it created the blocks).
assert e1.getbalance() == e2.getbalance()
assert e1.listunspent() != e2.listunspent()

# 2c. Self-send this half to e2 again
addr = e2.getnewaddress()
print ("2c. Self-sending this half to e2 (address %s)." % addr)
txid3 = e2.sendtoaddress(addr, 10500000, "", "", True)
sync_all([e1, e2])
e1.generatetoaddress(101, e1.getnewaddress())
sync_all([e1, e2])

# New e1 has slightly more coins than e2, because it received the fees
# from the last transaction
assert len(e1.listunspent()) == 4
assert len(e2.listunspent()) == 1
assert e1.getbalance()['bitcoin'] > e2.getbalance()['bitcoin']

# 2d. Analyze transactions
print ("2d. Analyzing transactions.")

# The first transaction is a 1-input-2-output transaction starting from an
# unblinded input and where one output (the fee) must be unblinded. Since
# blinding the remaining output would accomplish nothing, it is unblinded
# even though a confidential address was used.
tx1 = e1.getrawtransaction(txid1, True)
assert len(tx1['vin']) == 1
assert len(tx1['vout']) == 2
assert all(['value' in out for out in tx1['vout']])
# The second transaction though has three outputs, including change. Now
# there is value in blinding, so both the destination output and change
# output are blinded
tx2 = e1.getrawtransaction(txid2, True)
assert len(tx2['vin']) == 1
assert len(tx2['vout']) == 3
assert any(['value-minimum' in out for out in tx2['vout']])
# The third transaction, which set subtractfeefromamount (the `True` passed
# to `sendtoaddress`), will again be a 1-input-2-output transaction, where
# one output is the unblinded fee. But since its input is confidential, the
# output will be too.
tx3 = e1.getrawtransaction(txid3, True)
assert len(tx3['vin']) == 1
assert len(tx3['vout']) == 2
assert any(['value' in out for out in tx3['vout']])
assert any(['value-minimum' in out for out in tx3['vout']])

# Check that these transactions are visible in the correct wallets, with the
# expected effects. Check that they are not visible in the opposing wallet
assert e1.gettransaction(txid1)['amount'] == { 'bitcoin': 0 }
assert e2.gettransaction(txid1)['amount']['bitcoin'] < -20999999 # exact value depends on fee
assert e1.gettransaction(txid2)['amount'] == { 'bitcoin': -10500000 }
assert e2.gettransaction(txid2)['amount'] == { 'bitcoin': 10500000 }
assert e2.gettransaction(txid3)['amount'] == { 'bitcoin': 0 }

# txid3 appears only in e2, not e1
try:
    e1.gettransaction(txid3)
except JSONRPCException:
    pass
else:
    raise Exception("Transaction 3 should not be in wallet 1")

## 3. Confidential assets and keys
print ("")
print ("3. Confidential Keys")
current_e1_balance = e1.getbalance()

# 3a. Import an address's secret key
print ("3a. Import an address's secret key")
# Recall that `addr` was last set to an address owned by e2, and which
# we sent 10.5 million coins to in `tx3`. The public data (mostly hidden)
# is visible with `getrawtransaction`, while the confidential data is
# visible on `e2` (but not `e1`") with `gettransaction`.

# Now let's private import the key to attempt a spend
e1.importprivkey(e2.dumpprivkey(addr))
# Now `gettransaction` no longer triggers an exception, but the confidential
# data is still not available.
assert e1.gettransaction(txid3)['details'] == []
assert e2.gettransaction(txid3)['details'] != []
# Its output won't appear in listunspent, and the wallet balance will be unaffected
assert len(e1.listunspent()) == 4
assert e1.getbalance() == current_e1_balance

# 3a. Import an address's blinding key
print ("3b. Import an address's blinding key")
# Solution: Import blinding key
e1.importblindingkey(addr, e2.dumpblindingkey(addr))

# Check again, funds should show
assert len(e1.listunspent()) == 5
assert e1.getbalance()['bitcoin'] > current_e1_balance['bitcoin']
assert e1.gettransaction(txid3)['details'] != []

# Move funds to fresh addresses to avoid any confusion related to shared
# coins down the line (e.g. conflicting transactions).
e1.sendtoaddress(e1.getnewaddress(), e1.getbalance()['bitcoin'], "", "", True)
e1.sendtoaddress(e2.getnewaddress(), e1.getbalance()['bitcoin'] / 2, "", "", True)
e1.generatetoaddress(1, e1.getnewaddress())
sync_all([e1, e2])

## 4. 2-of-2 multisig
#
# Let's build a blinded 2-of-2 multisig p2sh address
print ("")
print ("4. 2-of-2 multisig")

print ("4a. Create a multisig address.")
# 1) Get unblinded addresses from each participant
addr1 = e1.getaddressinfo(e1.getnewaddress())["unconfidential"]
addr2 = e2.getaddressinfo(e2.getnewaddress())["unconfidential"]

# 2) Get blinding keys, private and public
addrinfo1 = e1.getaddressinfo(e1.getnewaddress())
addrinfo2 = e2.getaddressinfo(addr2)
blindingkey = e1.dumpblindingkey(addrinfo1["address"])
blindingpubkey = addrinfo1["confidential_key"]

# 3) Make multisig address like usual
multisig = e1.createmultisig(2, [addrinfo1["pubkey"], addrinfo2["pubkey"]])

print ("4b. Blind the multisig address (using a blinding key from e1).")
# 4) Blind the address using the blinding pubkey
blinded_addr = e1.createblindedaddress(multisig["address"], blindingpubkey)
e1.importaddress(multisig["redeemScript"], "", True, True) # Make sure p2sh addr is added
e2.importaddress(multisig["redeemScript"], "", True, True)
e1.importaddress(blinded_addr)
e2.importaddress(blinded_addr)

# 5) Now the address can be funded, though e2 will not be able to see values
txid = e1.sendtoaddress(blinded_addr, 1)
sync_all([e1, e2])
assert e1.gettransaction(txid, True)['details'] != []
assert e2.gettransaction(txid, True)['details'] == []

print ("4c. Share the blinding key with e2")
e2.importblindingkey(blinded_addr, blindingkey)
assert e1.gettransaction(txid, True)['details'] != []
assert e2.gettransaction(txid, True)['details'] != []

## 5. Multi-asset support
#
# Many of the RPC calls have added asset type or label arguments, and reveal
# alternative asset information. With no argument all are listed. For example,
# try `getwalletinfo` or `getbalance`. (Notice in the above code our assertions
# have taken forms like {"bitcoin": 100} rather than bare numbers.)
#
# Notice we now see "bitcoin" as an asset. This is the asset label for the hex
# for "bitcoin" which can be discovered using the `dumpassetlabels` RPC. We
# can see more details of each issuance that your wallet knows about with the
# `listissuances` RPC. Initially there is only one asset, "bitcoin", and one
# issuance (the initial issuance).
print ("")
print ("5. Multi-asset support")
print ("Existing assets: ", e1.dumpassetlabels())
assert len(e1.dumpassetlabels()) == 1
assert len(e1.listissuances()) == 1
assert e1.listissuances()[0]['assetlabel'] == "bitcoin"
assert e1.listissuances()[0]['assetamount'] == 21000000  # 21M initial free coins
assert e1.listissuances()[0]['tokenamount'] == 0         # no reissuance tokens
assert e1.dumpassetlabels() == e2.dumpassetlabels()

print ("5a. Issue a new asset, with reissuance token")
# We can also issue our own assets, 1 asset and 1 reissuance token in this case
issue = e1.issueasset(1, 1)
asset = issue["asset"]

# From there you can look at the issuances you have in your wallet
assert len(e1.listissuances()) == 2
assert len(e2.listissuances()) == 1  ## e2 does not recognize this as a wallet issuance
new_issuances = [i for i in e1.listissuances() if 'assetlabel' not in i]
assert len(new_issuances) == 1
assert new_issuances[0]['assetamount'] == 1
assert new_issuances[0]['tokenamount'] == 1

assert len(e2.listissuances()) == 1 ## ANDREW
print ("5b. Reissue the asset using the reissuance token.")
# If you gave `issueasset` a reissuance token argument greater than 0
# you can also reissue the base asset. This will appear as a second issuance
# in `listissuances`.
e1.reissueasset(asset, 1)
new_issuances = [i for i in e1.listissuances() if 'assetlabel' not in i]
assert len(new_issuances) == 2
assert new_issuances[0]['assetamount'] == 1
assert new_issuances[1]['assetamount'] == 1
# The original issuance will show `tokenamount` while the new one will not have
# this field. Python makes it annoying to assert this.

print ("5c. Issue a new asset with only reissuance tokens, no actual asset.")
new_issue = e1.issueasset(0, 1, False) # `False` tells elementsd not to blind the issuance
assert len(e1.listissuances()) == 4
assert len(e2.listissuances()) == 1
issuance = [i for i in e1.listissuances() if i.get('asset') == new_issue['asset']][0]
assert issuance['assetamount'] == -1 # should be 0, see https://github.com/ElementsProject/elements/issues/1035
assert issuance['tokenamount'] == 1

sync_all([e1, e2])
e1.generatetoaddress(1, e1.getnewaddress())
sync_all([e1, e2])

print ("5d. Label a new asset.")
# To label any asset add a new argument like this to your elements.conf file
# then restart your daemon. Remember to reload the wallet after restarting.
# Wallet labels have no consensus meaning, only local node/wallet meaning
assetentry = "-assetdir="+asset+":namedasset"
e1.restart([assetentry], keep_datadir=True)

assert e1.getbestblockhash() == e2.getbestblockhash()  ## sanity check that node remembers the blockchain
e1.connect_to(e2)
e2.connect_to(e1)
e1.loadwallet("wallet1")

# The new label will be reflected in the RPC
assert e1.getwalletinfo()['balance']['namedasset'] == 2
assert e1.getbalance()['namedasset'] == 2

print ("5e. Transfer assets.")
# To send issued assets, add an additional argument to sendtoaddress using the hex or label
e1.sendtoaddress(address=e2.getnewaddress(), amount=1, assetlabel="namedasset")
# Reissuance tokens can also be sent like any other asset
e1.sendtoaddress(address=e2.getnewaddress(), amount=1, assetlabel=issue["token"])
sync_all([e1, e2])
# e2 wallet doesn't know about label, just an unnamed asset
assert e2.getwalletinfo()["unconfirmed_balance"][asset] == 1
assert "namedasset" not in e2.getwalletinfo()["unconfirmed_balance"]
e2.generatetoaddress(1, e2.getnewaddress())
sync_all([e1, e2])

# e2, despite receiving an asset, continues not to know about its issuances
assert len(e2.listissuances()) == 1
# ...and therefore, despite receiving a reissuance token, does not understand
# it and cannot use it to issue
try:
    e2.reissueasset(issue["asset"], 5)
except JSONRPCException:
    pass
else:
    raise Exception("Should not be able to reissue a reissuance token")

print ("5e. Import an address used in an issuance.")
# However, if we import the address used in the issuance transaction and
# rescan, the wallet _will_ learn about the issuance, although it will
# not know about the amounts (which are blinded)
txid = issue["txid"]
addr = e1.gettransaction(txid)["details"][0]["address"]
e2.importaddress(addr)

assert len(e2.listissuances()) == 2
new_issuances = [i for i in e2.listissuances() if 'assetlabel' not in i]
assert len(new_issuances) == 1
assert new_issuances[0]['assetamount'] == -1
assert new_issuances[0]['tokenamount'] == -1

# At this point, e2 knows that its reissuance token is actually a reissuance
# token, and can use it to reissue. Even though it does not know about the
# original issuance.
e2.reissueasset(issue["asset"], 1)

# We need to import the issuance blinding key. We refer to issuances by their txid/vin pair
# as there is only one per input
vin = issue["vin"]
issuekey = e1.dumpissuanceblindingkey(txid, vin)
e2.importissuanceblindingkey(txid, vin, issuekey)

# Now e2 can see issuance amounts and blinds
assert len(e2.listissuances()) == 3
new_issuances = [i for i in e2.listissuances() if 'assetlabel' not in i]
assert len(new_issuances) == 2
assert new_issuances[0]['assetamount'] == 1
assert new_issuances[1]['assetamount'] == 1

# Reissuing reissuance tokens is not supported
try:
    e2.reissueasset(issue["token"], 1)
except JSONRPCException:
    pass
else:
    raise Exception("Should not be able to reissue a reissuance token")

# For de-issuance, we can send assets or issuance tokens to an OP_RETURN output, provably burning them
e2.destroyamount(issue["asset"], 1)

sync_all([e1, e2])
e1.generatetoaddress(1, e1.getnewaddress())
sync_all([e1, e2])

## 6. Blocksigning
#
# Up to now, we have been generating blocks to the default OP_TRUE script. Let's
# make this script more interesting. We'll use a 2-of-2 multisig made from keys
# from our two Elements nodes.
#

print ("")
print ("6. Blocksigning")
print ("6a. Generating 2-of-2 blocksigning script")

# First lets get some keys from both clients to make our block "challenge"
addr1 = e1.getnewaddress()
addr2 = e2.getnewaddress()
valid1 = e1.getaddressinfo(addr1)
pubkey1 = valid1["pubkey"]
valid2 = e2.getaddressinfo(addr2)
pubkey2 = valid2["pubkey"]

key1 = e1.dumpprivkey(addr1)
key2 = e2.dumpprivkey(addr2)

# We need to define a witness script, which defines the 2-of-2 checkmultisig
witness_script = "5221" + pubkey1 + "21" + pubkey2 + "52ae"
extra_args = [
    # We set the signblockscript to the witness script
    "-signblockscript=" + witness_script,
    # To prevent malleability attacks, we must set a maximum signature size. Since
    # we expect to have two ECDSA signatures (each at most 73 bytes), 150 bytes is
    # a sufficient value.
    "-con_max_block_sig_size=150",
    # We also disable dynamic federations, since we are not going to do any
    # dynafed transitions in this tutorial. FIXME we probably should.
    "-con_dyna_deploy_start=0",
]

print ("6b. Restart both nodes")
# Restart both nodes with the new consensus rules
e1.restart(extra_args)
e2.restart(extra_args)
e1.connect_to(e2)
e2.connect_to(e1)

# We cleared the datadirs, but even if we had not, changing the consensus
# rules would have invalidated the past blockchain and required we reset
# anyway. Now we have only the genesis block.
assert e1.getblockcount() == 0
assert e2.getblockcount() == 0
assert e1.getbestblockhash() == e2.getbestblockhash()

print ("6c. Import signing keys")
# Now import signing keys
e1.createwallet("wallet1")
e2.createwallet("wallet2")
e1.importprivkey(key1)
e2.importprivkey(key2)

# Generate no longer works, since neither node has sufficiently
# many keys to sign a block. In fact, even if both keys were
# available, `generatetoaddress` would not work because it does
# not attempt to solve the blocksigning script.
try:
    e1.generatetoaddress(1, e1.getnewaddress())
except JSONRPCException:
    pass
else:
    raise Exception("Generate shouldn't work")

try:
    e1.generatetoaddress(1, e1.getnewaddress())
    raise Exception("Generate shouldn't work")
except JSONRPCException:
    pass

print ("6d. Propose a block")

# Have e1 propose a block for both nodes to sign
blockhex = e1.getnewblockhex()

# Without signing the block, it is not accepted by consensus
# 0 before, 0 after
assert e1.getblockcount() == 0
e1.submitblock(blockhex)
assert e1.getblockcount() == 0

print ("6d. Sign the block")
# Signblock tests validity except block signatures
# This signing step can be outsourced to a HSM signing to enforce business logic of any sort
# See Strong Federations paper
sign1 = e1.signblock(blockhex, witness_script)
sign2 = e2.signblock(blockhex, witness_script)
assert len(sign1) == 1  # both nodes produce one signature
assert len(sign2) == 1

# Obtain signatures from both nodes. Both signatures are required for the block
# to be considered complete.
blockresult = e1.combineblocksigs(blockhex, [sign1[0]])
assert not blockresult["complete"]
blockresult = e1.combineblocksigs(blockhex, [sign2[0]])
assert not blockresult["complete"]
blockresult = e1.combineblocksigs(blockhex, [sign1[0], sign2[0]])
assert blockresult["complete"]

print ("6d. Submit the block")
# Either node may submit the block to the network
e2.submitblock(blockresult["hex"])
sync_all([e1, e2])

# We now have moved forward one block!
assert e1.getblockcount() == 1
assert e2.getblockcount() == 1

## The peg
#
# Everything peg-related can be done inside the Elements daemon directly,
# except for processing pegouts. This is because processing pegouts involves
# moving coins on the Bitcoin blockchain. In a production system, this is
# the most difficult part to get right, and by far the most important, as
# there is no going back if you lose funds on Bitcoin.
#
print ("")
print ("7. Dealing with the peg")
print ("7a. Restart both nodes")

extra_args = [
    # We'll lazily reuse our blocksigning script to handle the peg, and
    # leave the blocksigning script unset (so it will revert to OP_TRUE)
    "-fedpegscript=" + witness_script,
    # Set initial free coins to 0, since we will now use the peg
    "-initialfreecoins=0",
]
# Restart both nodes with the new consensus rules
e1.restart(extra_args)
e2.restart(extra_args)
e1.connect_to(e2)
e2.connect_to(e1)

e1.createwallet("wallet1")
e2.createwallet("wallet2")
e1.rescanblockchain()
e2.rescanblockchain()
assert e1.getwalletinfo()['balance'] == { 'bitcoin': 0 }
assert e2.getwalletinfo()['balance'] == { 'bitcoin': 0 }

# Generate some Elements blocks as we cannot accept pegin claims
# while the blockheight is 0 (this may be unintended behavior).
e1.generatetoaddress(5, e1.getnewaddress())
sync_all([e1, e2])

# Create some mature Bitcoin outputs
bitcoin.createwallet("bwallet")
bitcoin.generatetoaddress(101, bitcoin.getnewaddress())

print ("7b. Create a peg-in address")
# Once there are mature coins on the Bitcoin side, we can peg them in.
# We create a pegin address, which we create with the Elements wallet
# but which is a Bitcoin address.
#
# Internally, this address is computed by generating an Elements address
# then using the underlying script, called a "claim script", to "tweak"
# the peg witness script.
#
# The claim script is provided by the `getpeginaddress` RPC, but it is
# not necessary to keep, for most usecases, because it is also stored
# in the wallet.
peg_in_addr = e1.getpeginaddress()
assert "mainchain_address" in peg_in_addr
assert "claim_script" in peg_in_addr

print ("7c. Send Bitcoin to the pegin address")
txid = bitcoin.sendtoaddress(peg_in_addr["mainchain_address"], 10)

print ("7d. Claim the Bitcoin on the sidechain")
# Once the coins are sent on the Bitcoin side, they will not be recognized
# or accepted by the sidechain until they are buried by 100 confirmations.
# This value may be changed by use of the `-peginconfirmationdepth` config
# setting on the Elements daemon.
#
# Bear in mind that this is a consensus rule and all nodes must agree on it.

# First, try claiming the pegin early. This will fail.
bitcoin.generatetoaddress(1, bitcoin.getnewaddress())

proof = bitcoin.gettxoutproof([txid])
raw = bitcoin.getrawtransaction(txid)
try:
    claimtxid = e1.claimpegin(raw, proof, peg_in_addr["claim_script"])
except JSONRPCException:
    pass
else:
    raise Exception("Should not be able to claim a pegin early")

# After 100 blocks, the claim will work. Note that the original proof will
# work, as long as no reorgs changed which block the pegin transaction was
# included in.
bitcoin.generatetoaddress(100, bitcoin.getnewaddress())
claimtxid = e1.claimpegin(raw, proof, peg_in_addr["claim_script"])
# Mine this from the other node, to confirm that mempool propagation works
sync_all([e1, e2])
e2.generatetoaddress(1, e1.getnewaddress())
sync_all([e1, e2])

assert "confirmations" in e1.getrawtransaction(claimtxid, 1)
sys.exit(0)

print ("7e. Request pegout")
# This burns coins on Liquid using a specially-structured OP_RETURN output.
# In a production network, doing this would trigger the watchman federation
# to send payment to the specified Bitcoin address on the mainchain.
#
# The Bitcoin-side functionality is not supported directly in Elements;
# the watchmen are expected to notice this transaction and send the funds
# from their collective wallet.
e1.sendtomainchain(bitcoin.getnewaddress(), 5)


## Exercise(s)
#
# 1. Implement really dumb/unsafe watchmen to allow pegouts for learning purposes.
#    To custody the coins that users peg in, you need to extract the tweak from
#    the pegin claim, use this tweak to adjust the secret keys, and import the
#    resulting keys to a Core wallet.
#
# 2. Create an alternate peg from testnet to Liquid, using asset issuance and
#    destruction.
#
# 3. Implement a round-robin blocksigner protocol, where each signer takes a turn
#    proposing blocks for the others to sign.
#

print ("")
print ("8. Raw transaction demo")
# RAW API

# Let's create a basic transaction using the raw api, blind it, sign, and send

# Create a transaction with a single destination output to other wallet.
rawtx = e1.createrawtransaction([], [{ e2.getnewaddress(): 100 }])
# Biggest difference compared to Bitcoin is that we have explicit fee outputs,
# which may be set in `createrawtransaction`. These will be added or adjusted
# by `fundrawtransaction` to make the transaction balance.
rawtx2 = e1.createrawtransaction(
    [],
    [{ e2.getnewaddress(): 100 }, { e1.getnewaddress() :5 }, { "fee": Decimal("0.1") }],
)
# Fee outputs are unblinded, with a scriptPubKey of "". On Elements, empty
# scriptPubKeys are unspendable.

# Next we can fund the transaction (and replaces fee with something more appropriate)
fundedtx = e1.fundrawtransaction(rawtx2)

# Blind
blindedtx = e1.blindrawtransaction(fundedtx["hex"])

# In some cases, such as when there is one blinded output but no blinded inputs,
# blinding will fail. The `ignoreblindfails` option to `blindrawtransaction` may
# be set, in which case the transaction will "successfully" not be blinded.
#
# To unconditionally blind a transaction, ensure that it has 2 or more outputs,
# which will ensure that blinding is (a) useful and (b) mathematically possible.

# Sign
signedtx = e1.signrawtransactionwithwallet(blindedtx)

# And send
txid = e1.sendrawtransaction(signedtx["hex"])

print ("Finished!")

