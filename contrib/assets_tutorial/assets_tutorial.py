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
            self.proc.kill()
            self.proc = None

        if self.datadir_path is not None:
            if self.cleanup_on_exit:
                shutil.rmtree(self.datadir_path)
            else:
                print ("Leaving %s datadir at %s." % (self.name, self.datadir_path))

    def start(self, ext_args = None):
        self.shutdown()

        if ext_args is None:
            ext_args = []
        # Create datadir and copy config into place
        self.datadir_path = tempfile.mkdtemp()
        shutil.copyfile(self.conf_path, self.datadir_path + '/' + self.daemon + '.conf')
        print("%s datadir: %s" % (self.name, self.datadir_path))
        # Start process
        self.proc = subprocess.Popen([self.path, "-datadir=" + self.datadir_path] + ext_args, stdout=subprocess.PIPE)
        self.rpc = AuthServiceProxy("http://" + self.config["rpcuser"] + ":" + self.config["rpcpassword"] + "@127.0.0.1:" + self.config["rpcport"])

    def restart(self, ext_args = None):
        self.start(ext_args)

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

    stop_time = time.time() + timeout
    while time.time() <= stop_time:
        best_hash = [x.getbestblockhash() for x in nodes]
        if best_hash.count(best_hash[0]) == len(nodes):
            return
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
#
# 1a. Confirm that we not start an elements node if validatepegin is set and there
#     is no bitcoind. When validatepegin is set, elementsd attempts to connect to
#     bitcoind to check if peg-in transactions are confirmed in the Bitcoin chain.
#
# Alternatively, you can set validatepegin=0 (it defaults to being on) in the
# elementsd config, and run it without a Bitcoin node, but this means that you
# will not be fully validating the two-way peg.

assert e1["validatepegin"] == "1"

e1.start()
time.sleep(1) ## give daemon a moment to start up (or not)
try:
    e1.getinfo()
    print ("ERROR: was able to start an elementsd without a working bitcoind")
    sys.exit(1)
except:
    pass

# 1b. Start bitcoind, then elementsd. Initially, the bitcoind may be warming up and
#     inaccessible over RPC. elementsd can detect this case and will stall until the
#     bitcoind is warmed up.

bitcoin.start()
e1.start()
e2.start()

time.sleep(1) ## give daemons a moment to start up

# 1c. Create a wallet on the Elements nodes. This is needed since version 0.21
#     of the daemon; previously a wallet was created by default if one does not
#     already exist.
e1.createwallet("wallet1")
e2.createwallet("wallet2")

# We have configured this regtest chain to start with 21M bitcoins, which are initally
# in a single OP_TRUE output. All Elements wallets recognize OP_TRUE outputs as their
# own (this differs from Bitcoin), so the 21M bitcoins are immediately available for
# use.
#
# This is useful for testing basic functionality and for blockchains that have no peg,
# since every blockchain needs a default "policy asset". This policy asset is used
# for transaction fees (which are required for anti-DoS purposes). Also, asset
# issuances require some pre-existing asset, since they consume inputs for entropy.
#
# In Elements there is no block subsidy. In a production sidechain, `initialfreecoins`
# will likely be set to zero, necessitating peg-in functionality to get a policy asset.
assert e1["initialfreecoins"] == "2100000000000000"
print (e1.getwalletinfo())

print ("Waiting 2 mins")
time.sleep(120) ## give daemons a moment to start up
sys.exit(0)
# In regtest mining "target" is OP_TRUE since we have not set `-signblockscript` argument
# Generate simply works.
e1.generatetoaddress(101, e1.getnewaddress())
sync_all(e1, e2)

# WALLET

# First, send all anyone-can-spend coins to e1 then split so balances are even
e1.sendtoaddress(e1.getnewaddress(), 21000000, "", "", True)
e1.generatetoaddress(101, e1.getnewaddress())
sync_all(e1, e2)
e1.sendtoaddress(e2.getnewaddress(), 10500000, "", "", False)
e1.generatetoaddress(101, e1.getnewaddress())
sync_all(e1, e2)

# Funds should now be evenly split between the two wallets
e1.getwalletinfo()
e2.getwalletinfo()

# Have e2 send coins to themself using a blinded Elements address
# Blinded addresses start with `CTE`, unblinded `2`
addr = e2.getnewaddress()

# How do we know it's blinded? Check for blinding key, unblinded address.
e2.getaddressinfo(addr)

# Basic blinded send
txid = e2.sendtoaddress(addr, 1)

e2.generatetoaddress(1, e1.getnewaddress())
sync_all(e1, e2)

# Now let's examine the transaction, both in wallet and without

# In-wallet, take a look at blinding information
e2.gettransaction(txid)

# e1 doesn't have in wallet since it's unrelated
try:
    e1.gettransaction(txid)
    raise Exception("Transaction should not be in wallet")
except JSONRPCException:
    pass

# Get public info, see blinded ranges, etc
e1.getrawtransaction(txid, 1)

# Now let's private import the key to attempt a spend
e1.importprivkey(e2.dumpprivkey(addr))

# We can't see output value info though
# and can not send.
e1.gettransaction(txid)

# And it won't show in balance or known outputs
e1.getwalletinfo()
# Amount for transaction is unknown, so it is not shown in listunspent.
e1.listunspent(1, 1)

# Solution: Import blinding key
e1.importblindingkey(addr, e2.dumpblindingkey(addr))

# Check again, funds should show
e1.getwalletinfo()
e1.listunspent(1, 1)
e1.gettransaction(txid)

# Let's build a blinded 2-of-2 multisig p2sh address

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

# 4) Blind the address using the blinding pubkey
blinded_addr = e1.createblindedaddress(multisig["address"], blindingpubkey)
e1.importaddress(multisig["redeemScript"], "", True, True) # Make sure p2sh addr is added
e2.importaddress(multisig["redeemScript"], "", True, True)
e1.importaddress(blinded_addr)
e2.importaddress(blinded_addr)

# 5) Now the address can be funded, though e2 will not be able to see values
txid = e1.sendtoaddress(blinded_addr, 1)
sync_all(e1, e2)
e2.gettransaction(txid, True)

# 6) Import the blinding privkey and decode the values
e2.importblindingkey(blinded_addr, blindingkey)
e2.gettransaction(txid, True)

# ASSETS

# Many of the RPC calls have added asset type or label
# arguments and reveal alternative asset information. With no argument all are listed:
e1.getwalletinfo()

# Notice we now see "bitcoin" as an asset. This is the asset label for the hex for "bitcoin" which can be discovered:
e1.dumpassetlabels()

# We can also issue our own assets, 1 asset and 1 reissuance token in this case
issue = e1.issueasset(1, 1)
asset = issue["asset"]

# From there you can look at the issuances you have in your wallet
e1.listissuances()

# If you gave `issueasset` a reissuance token argument greater than 0
# you can also reissue the base asset
e1.reissueasset(asset, 1)

# or make another different unblinded asset issuance, with only reissuance tokens initially
e1.issueasset(0, 1, False)

# Then two issuances for that particular asset will show
e1.listissuances(asset)

# To label any asset add a new argument like this to your elements.conf file
# then restart your daemon:
assetentry = "-assetdir="+asset+":namedasset"
# Wallet labels have no consensus meaning, only local node/wallet meaning

sync_all(e1, e2)
e1.stop()
time.sleep(5)

# Restart with a new asset label
e1 = startelementsd(e1_datadir, e1conf, [assetentry])
time.sleep(5)

e1.getwalletinfo()

# To send issued assets, add an additional argument to sendtoaddress using the hex or label
e1.sendtoaddress(address=e2.getnewaddress(), amount=1, assetlabel="namedasset")
# Reissuance tokens can also be sent like any other asset
e1.sendtoaddress(address=e2.getnewaddress(), amount=1, assetlabel=issue["token"])
sync_all(e1, e2)
# e2 wallet doesn't know about label, just an unnamed asset
e2.getwalletinfo()["unconfirmed_balance"][asset]
e2.generatetoaddress(1, e2.getnewaddress())
sync_all(e1, e2)

# e2 maybe doesn't know about the issuance for the transaction sending him the new asset
e2.listissuances()

# let's import an associated address(so the wallet captures issuance transaction) and rescan
txid = issue["txid"]
addr = e1.gettransaction(txid)["details"][0]["address"]
e2.importaddress(addr)

# e2 now sees issuance, but doesn't know amounts as they are blinded
e2.listissuances()

# We need to import the issuance blinding key. We refer to issuances by their txid/vin pair
# as there is only one per input
vin = issue["vin"]
issuekey = e1.dumpissuanceblindingkey(txid, vin)

e2.importissuanceblindingkey(txid, vin, issuekey)

# Now e2 can see issuance amounts and blinds
e2.listissuances()

# Since it was also sent a reissuance token, it can reissue the base asset
e2.reissueasset(issue["asset"], 5)


# Reissuing reissuance tokens is currently not supported
try:
    e2.reissueasset(issue["token"], 1)
except JSONRPCException:
    pass

# For de-issuance, we can send assets or issuance tokens to an OP_RETURN output, provably burning them
e2.destroyamount(issue["asset"], 5)

# BLOCKSIGNING

# Recall blocksigning is OP_TRUE
e1.generatetoaddress(1, e1.getnewaddress())
sync_all(e1, e2)

# Let's set it to something more interesting... 2-of-2 multisig

# First lets get some keys from both clients to make our block "challenge"
addr1 = e1.getnewaddress()
addr2 = e2.getnewaddress()
valid1 = e1.getaddressinfo(addr1)
pubkey1 = valid1["pubkey"]
valid2 = e2.getaddressinfo(addr2)
pubkey2 = valid2["pubkey"]

key1 = e1.dumpprivkey(addr1)
key2 = e2.dumpprivkey(addr2)

e1.stop()
e2.stop()
time.sleep(5)

# Now filled with the pubkeys as 2-of-2 checkmultisig
signblockarg="-signblockscript=5221"+pubkey1+"21"+pubkey2+"52ae"
# Anti-DoS argument, custom chain default is ~1 sig so let's make it at least 2 sigs
blocksign_max_size="-con_max_block_sig_size=150"
dyna_deploy_start="-con_dyna_deploy_start=0"
extra_args = [
    signblockarg,
    blocksign_max_size,
    dyna_deploy_start,
]

# Wipe out datadirs, start over
shutil.rmtree(e1_datadir)
shutil.rmtree(e2_datadir)
os.makedirs(e1_datadir)
os.makedirs(e2_datadir)

# Copy back config files
shutil.copyfile("contrib/assets_tutorial/elements1.conf", e1_datadir+"/elements.conf")
shutil.copyfile("contrib/assets_tutorial/elements2.conf", e2_datadir+"/elements.conf")

e1 = startelementsd(e1_datadir, e1conf, extra_args)
e2 = startelementsd(e2_datadir, e2conf, extra_args)
time.sleep(5)
sync_all(e1, e2)

# Now import signing keys
e1.importprivkey(key1)
e2.importprivkey(key2)

# Generate no longer works, even if keys are in wallet
try:
    e1.generatetoaddress(1, e1.getnewaddress())
    raise Exception("Generate shouldn't work")
except JSONRPCException:
    pass

try:
    e1.generatetoaddress(1, e1.getnewaddress())
    raise Exception("Generate shouldn't work")
except JSONRPCException:
    pass

# Let's propose and accept some blocks, e1 is master!
blockhex = e1.getnewblockhex()

# Unsigned is no good
# 0 before, 0 after
e1.getblockcount() == 0

e1.submitblock(blockhex)

# Still 0
e1.getblockcount() == 0


# Signblock tests validity except block signatures
# This signing step can be outsourced to a HSM signing to enforce business logic of any sort
# See Strong Federations paper
sign1 = e1.signblock(blockhex)
sign2 = e2.signblock(blockhex)


# We now can gather signatures any way you want, combine them into a fully signed block
blockresult = e1.combineblocksigs(blockhex, [sign1[0], sign2[0]])

blockresult["complete"] == True

signedblock = blockresult["hex"]

# Now submit the block, doesn't matter who
e2.submitblock(signedblock)
sync_all(e1, e2)

# We now have moved forward one block!
e1.getblockcount() == 1
e2.getblockcount() == 1

e1.stop()
e2.stop()
time.sleep(5)

# Further Exercises:
# - Make a python script that does round-robin consensus

# Pegging

# Everything pegging related can be done inside the Elements daemon directly, except for
# pegging out. This is due to the multisig pool aka Watchmen that controls the bitcoin
# on the Bitcoin blockchain. That is the easiest part to get wrong, and by far the most
# important as there is no going back if you lose the funds.

# Wipe out datadirs, start over
shutil.rmtree(e1_datadir)
shutil.rmtree(e2_datadir)
os.makedirs(e1_datadir)
os.makedirs(e2_datadir)

# Copy back config files
shutil.copyfile("contrib/assets_tutorial/elements1.conf", e1_datadir+"/elements.conf")
shutil.copyfile("contrib/assets_tutorial/elements2.conf", e2_datadir+"/elements.conf")

fedpegarg="-fedpegscript=5221"+pubkey1+"21"+pubkey2+"52ae"

# Back to OP_TRUE blocks, re-using pubkeys for pegin pool instead
# Keys can be the same or different, doesn't matter
e1 = startelementsd(e1_datadir, e1conf, [fedpegarg])
e2 = startelementsd(e2_datadir, e2conf, [fedpegarg])
time.sleep(5)

# Mature some outputs on each side
e1.generatetoaddress(101, e1.getnewaddress())
bitcoin.generatetoaddress(101, bitcoin.getnewaddress())
sync_all(e1, e2)

# Now we can actually start pegging in. Examine the pegin address fields
e1.getpeginaddress()
# Changes each time as it's a new sidechain address as well as new "tweak" for the watchmen keys
# mainchain_address : where you send your bitcoin from Bitcoin network
# sidechain_address : where the bitcoin will end up on the sidechain after pegging in

# Each call of this takes the pubkeys defined in the config file, adds a random number to them
# that is essetially the hash of the sidechain_address and other information,
# then creates a new P2SH Bitcoin address from that. We reveal that "tweak" to the functionaries
# during `claimpegin`, then they are able to calculate the necessary private key and control
# funds.
addrs = e1.getpeginaddress()

#Send funds to unique watchmen P2SH address
txid = bitcoin.sendtoaddress(addrs["mainchain_address"], 1)

# Confirmations in Bitcoin are what protects the
# sidechain from becoming fractional reserve during reorgs.
bitcoin.generatetoaddress(101, bitcoin.getnewaddress())
proof = bitcoin.gettxoutproof([txid])
raw = bitcoin.getrawtransaction(txid)

# Attempt claim!
claimtxid = e1.claimpegin(raw, proof, addrs["claim_script"])
sync_all(e1, e2)

# Other node should accept to mempool and mine
e2.generatetoaddress(1, e1.getnewaddress())
sync_all(e1, e2)

# Should see confirmations
"confirmations" in e1.getrawtransaction(claimtxid, 1)

# Pegging Out

# This command would trigger watchmen to send payment to Bitcoin address on mainchain
# The Bitcoin-side functionality is not supported directly in Elements.
# The watchmen will notice this transaction and send the funds from their collective
# wallet.
e1.sendtomainchain(bitcoin.getnewaddress(), 10)

#Exercise(s)
#1. Implement really dumb/unsafe watchmen to allow pegouts for learning purposes
# Recover tweak from pegin, add to privkey, combined tweaked pubkeys into a redeemscript, add to Core wallet

# RAW API

# Let's create a basic transaction using the raw api, blind it, sign, and send

# Create a transaction with a single destination output to other wallet
rawtx = e1.createrawtransaction([], {e2.getnewaddress():100})
# Biggest difference compared to Bitcoin is that we have explicit fee outputs
rawtx2 = e1.createrawtransaction([], {e2.getnewaddress():100, e1.getnewaddress():5, "fee":Decimal("0.1")})
# Fee outputs are unblinded, with a scriptPubKey of "", in other words ""
# scriptPubKeys are unspendable

# Next we can fund the transaction (and replaces fee with something more appropriate)
fundedtx = e1.fundrawtransaction(rawtx2)

# Blind
blindedtx = e1.blindrawtransaction(fundedtx["hex"])
# *Warning*: Raw blinding logic can be quite complicated, requiring the use of `ignoreblindfails`
# to avoid having calls fail without manually inspecting transactions in great detail.
# In general any transaction with 2 or more outputs to blind should succeed, so adding additional
# is one strategy to resolve this.

# Sign
signedtx = e1.signrawtransactionwithwallet(blindedtx)

# And send
txid = e1.sendrawtransaction(signedtx["hex"])

sync_all(e1, e2)

e2.gettransaction(txid)

# ADVANCED OPTIONS
# rawblindrawtransaction : blind a raw transaction with no access to a wallet
# -policyasset=<hex> : set network fee asset type to something other than BTC

bitcoin.stop()
e1.stop()
e2.stop()
time.sleep(2)
shutil.rmtree(e1_datadir)
shutil.rmtree(e2_datadir)

