#!/usr/bin/env python3

from test_framework.authproxy import AuthServiceProxy, JSONRPCException
import os
import random
import sys
import time
import subprocess
import shutil
from decimal import *
from pdb import set_trace
OCEANPATH=""
BITCOINPATH=""

if len(sys.argv) == 2:
    OCEANPATH=sys.argv[0]
    BITCOINPATH=sys.argv[1]
else:
    OCEANPATH="./src"
    BITCOINPATH="./../bitcoin/src"

def startbitcoind(datadir, conf, args=""):
    subprocess.Popen((BITCOINPATH+"/bitcoind -datadir="+datadir+" "+args).split(), stdout=subprocess.PIPE)
    return AuthServiceProxy("http://"+conf["rpcuser"]+":"+conf["rpcpassword"]+"@127.0.0.1:"+conf["rpcport"])

def startoceand(datadir, conf, args=""):
    subprocess.Popen((OCEANPATH+"/oceand  -datadir="+datadir+" "+args).split(), stdout=subprocess.PIPE)
    return AuthServiceProxy("http://"+conf["rpcuser"]+":"+conf["rpcpassword"]+"@127.0.0.1:"+conf["rpcport"])

def loadConfig(filename):
    conf = {}
    with open(filename) as f:
        for line in f:
            if len(line) == 0 or line[0] == "#" or len(line.split("=")) != 2:
                continue
            conf[line.split("=")[0]] = line.split("=")[1].strip()
    conf["filename"] = filename
    return conf

def sync_all(e1, e2):
    totalWait = 10
    while e1.getblockcount() != e2.getblockcount() or len(e1.getrawmempool()) != len(e2.getrawmempool()):
        totalWait -= 1
        if totalWait == 0:
            raise Exception("Nodes cannot sync blocks or mempool!")
        time.sleep(1)
    return

## Preparations

# Make data directories for each daemon
b_datadir="/tmp/"+''.join(random.choice('0123456789ABCDEF') for i in range(5))
e1_datadir="/tmp/"+''.join(random.choice('0123456789ABCDEF') for i in range(5))
e2_datadir="/tmp/"+''.join(random.choice('0123456789ABCDEF') for i in range(5))

os.makedirs(b_datadir)
os.makedirs(e1_datadir)
os.makedirs(e2_datadir)

# Also configure the nodes by copying the configuration files from
# this directory (and read them back for arguments):
shutil.copyfile("contrib/assets_tutorial/bitcoin.conf", b_datadir+"/bitcoin.conf")
shutil.copyfile("contrib/assets_tutorial/ocean1.conf", e1_datadir+"/ocean.conf")
shutil.copyfile("contrib/assets_tutorial/ocean2.conf", e2_datadir+"/ocean.conf")

bconf = loadConfig("contrib/assets_tutorial/bitcoin.conf")
e1conf = loadConfig("contrib/assets_tutorial/ocean1.conf")
e2conf = loadConfig("contrib/assets_tutorial/ocean2.conf")

## Startup

# Can not start since bitcoind isn't running and validatepegin is set
# oceand attempts to connect to bitcoind to check if peg-in transactions
# are confirmed in the Bitcoin chain.
e1 = startoceand(e1_datadir, e1conf)
time.sleep(2)
try:
    e1.getinfo()
    raise AssertionError("This should fail unless working bitcoind can be reached via JSON RPC")
except:
    pass

# Start bitcoind, then oceand. As long as bitcoind is in RPC warmup, oceand will connect
bitcoin = startbitcoind(b_datadir, bconf)
e1 = startoceand(e1_datadir, e1conf)
e2 = startoceand(e2_datadir, e2conf)

time.sleep(3)

# Alternatively, you can set validatepegin=0 in their configs and not
# run the bitcoin node, but it is necessary for fully validating the two way peg.

# Regtest chain starts with 21M bitcoins as OP_TRUE which the wallet
# understands. This is useful for testing basic functionality and for
# blockchains that have no pegging functionality. A fee currency is required
# for anti-DoS purposes as well as asset issuance, which consumes inputs for entropy.
# In Ocean there is no block subsidy. In a production sidechain it can
# be configured to start with no outputs, necessitating peg-in functionality
# for asset issuance.
e1.getwalletinfo()

# In regtest mining "target" is OP_TRUE since we have not set `-signblockscript` argument
# Generate simply works.
e1.generate(101)
sync_all(e1, e2)

######## WALLET ###########

# First, send coins to two different wallets so balances are not shared
e1.sendtoaddress(e1.getnewaddress(), 10500000, "", "", True)
e1.generate(101)
sync_all(e1, e2)
e2.sendtoaddress(e2.getnewaddress(), 10500000, "", "", True)
e2.generate(101)
sync_all(e1, e2)

# Funds should now be evenly split between the two wallets
e1.getwalletinfo()
e2.getwalletinfo()

# Have e2 send coins to themself using a blinded Ocean address
# Blinded addresses start with `CTE`, unblinded `2`
addr = e2.getnewaddress()

# How do we know it's blinded? Check for blinding key, unblinded address.
e2.validateaddress(addr)

# Basic blinded send
txid = e2.sendtoaddress(addr, 1)

e2.generate(1)
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

## Let's build a blinded 2-of-2 multisig p2sh address

# 1) Get unblinded addresses from each participant
addr1 = e1.validateaddress(e1.getnewaddress())["unconfidential"]
addr2 = e2.validateaddress(e2.getnewaddress())["unconfidential"]

# 2) Get blinding keys, private and public
addrinfo1 = e1.validateaddress(e1.getnewaddress())
addrinfo2 = e2.validateaddress(addr2)
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

###### ASSETS #######

# Many of the RPC calls have added asset type or label 
# arguments and reveal alternative asset information. With no argument all are listed:
e1.getwalletinfo()

# Notice we now see "bitcoin" as an asset. This is the asset label for the hex for "bitcoin" which can be discovered:
e1.dumpassetlabels()

# You can also filter calls using specific asset hex or labels:
e1.getwalletinfo("bitcoin")
# bitcoin's hex asset type
e1.getwalletinfo("b2e15d0d7a0c94e4e2ce0fe6e8691b9e451377f6e46e8045a86f7c4b5d4f0f23")

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

# To label any asset add a new argument like this to your ocean.conf file
# then restart your daemon:
assetentry = "-assetdir="+asset+":namedasset"
# Wallet labels have no consensus meaning, only local node/wallet meaning

sync_all(e1, e2)
e1.stop()
time.sleep(5)

# Restart with a new asset label
e1 = startoceand(e1_datadir, e1conf, assetentry)
time.sleep(5)

e1.getwalletinfo()

# To send issued assets, add an additional argument to sendtoaddress using the hex or label
e1.sendtoaddress(e2.getnewaddress(), 1, "", "", False, "namedasset")
# Reissuance tokens can also be sent like any other asset
e1.sendtoaddress(e2.getnewaddress(), 1, "", "", False, issue["token"])
sync_all(e1, e2)
# e2 wallet doesn't know about label, just an unnamed asset
e2.getwalletinfo(asset)
e2.generate(1)
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

###### BLOCKSIGNING #######

# Recall blocksigning is OP_TRUE
e1.generate(1)
sync_all(e1, e2)

# Let's set it to something more interesting... 2-of-2 multisig

# First lets get some keys from both clients to make our block "challenge"
addr1 = e1.getnewaddress()
addr2 = e2.getnewaddress()
valid1 = e1.validateaddress(addr1)
pubkey1 = valid1["pubkey"]
valid2 = e2.validateaddress(addr2)
pubkey2 = valid2["pubkey"]

key1 = e1.dumpprivkey(addr1)
key2 = e2.dumpprivkey(addr2)

e1.stop()
e2.stop()
time.sleep(5)

# Now filled with the pubkeys as 2-of-2 checkmultisig
signblockarg="-signblockscript=5221"+pubkey1+"21"+pubkey2+"52ae"

# Wipe out datadirs, start over
shutil.rmtree(e1_datadir)
shutil.rmtree(e2_datadir)
os.makedirs(e1_datadir)
os.makedirs(e2_datadir)

# Copy back config files
shutil.copyfile("contrib/assets_tutorial/ocean1.conf", e1_datadir+"/ocean.conf")
shutil.copyfile("contrib/assets_tutorial/ocean2.conf", e2_datadir+"/ocean.conf")

e1 = startoceand(e1_datadir, e1conf, signblockarg)
e2 = startoceand(e2_datadir, e2conf, signblockarg)
time.sleep(5)
sync_all(e1, e2)

# Now import signing keys
e1.importprivkey(key1)
e2.importprivkey(key2)

# Generate no longer works, even if keys are in wallet
try:
    e1.generate(1)
    raise Exception("Generate shouldn't work")
except JSONRPCException:
    pass

try:
    e2.generate(1)
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

####
# Signblock tests validity except block signatures
# This signing step can be outsourced to a HSM signing to enforce business logic of any sort
# See Strong Federations paper
sign1 = e1.signblock(blockhex)
sign2 = e2.signblock(blockhex)
####

# We now can gather signatures any way you want, combine them into a fully signed block
blockresult = e1.combineblocksigs(blockhex, [sign1, sign2])

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

######## Pegging #######

# Everything pegging related can be done inside the Ocean daemon directly, except for
# pegging out. This is due to the multisig pool aka Watchmen that controls the bitcoin
# on the Bitcoin blockchain. That is the easiest part to get wrong, and by far the most
# important as there is no going back if you lose the funds.

# Wipe out datadirs, start over
shutil.rmtree(e1_datadir)
shutil.rmtree(e2_datadir)
os.makedirs(e1_datadir)
os.makedirs(e2_datadir)

# Copy back config files
shutil.copyfile("contrib/assets_tutorial/ocean1.conf", e1_datadir+"/ocean.conf")
shutil.copyfile("contrib/assets_tutorial/ocean2.conf", e2_datadir+"/ocean.conf")

fedpegarg="-fedpegscript=5221"+pubkey1+"21"+pubkey2+"52ae"

# Back to OP_TRUE blocks, re-using pubkeys for pegin pool instead
# Keys can be the same or different, doesn't matter
e1 = startoceand(e1_datadir, e1conf, fedpegarg)
e2 = startoceand(e2_datadir, e2conf, fedpegarg)
time.sleep(5)

# Mature some outputs on each side
e1.generate(101)
bitcoin.generate(101)
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
bitcoin.generate(101)
proof = bitcoin.gettxoutproof([txid])
raw = bitcoin.getrawtransaction(txid)

# Attempt claim!
claimtxid = e1.claimpegin(raw, proof, addrs["claim_script"])
sync_all(e1, e2)

# Other node should accept to mempool and mine
e2.generate(1)
sync_all(e1, e2)

# Should see confirmations
"confirmations" in e1.getrawtransaction(claimtxid, 1)

#### Pegging Out ####

# This command would trigger watchmen to send payment to Bitcoin address on mainchain
# The Bitcoin-side functionality is not supported directly in Ocean.
# The watchmen will notice this transaction and send the funds from their collective
# wallet.
e1.sendtomainchain(bitcoin.getnewaddress(), 10)

#Exercise(s)
#1. Implement really dumb/unsafe watchmen to allow pegouts for learning purposes
# Recover tweak from pegin, add to privkey, combined tweaked pubkeys into a redeemscript, add to Core wallet

#### RAW API ####

## Let's create a basic transaction using the raw api, blind it, sign, and send

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
signedtx = e1.signrawtransaction(blindedtx)

# And send
txid = e1.sendrawtransaction(signedtx["hex"])

sync_all(e1, e2)

e2.gettransaction(txid)

#### ADVANCED OPTIONS ####
# rawblindrawtransaction : blind a raw transaction with no access to a wallet
# -policyasset=<hex> : set network fee asset type to something other than BTC 

bitcoin.stop()
e1.stop()
e2.stop()
time.sleep(2)
shutil.rmtree(e1_datadir)
shutil.rmtree(e2_datadir)

