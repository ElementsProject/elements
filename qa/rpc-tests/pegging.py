#!/usr/bin/env python2

from test_framework.authproxy import AuthServiceProxy, JSONRPCException
import os
import random
import sys
import time
import subprocess
import shutil
from decimal import *

if len(sys.argv) < 2:
    print("path to bitcoind must be included as argument")
    sys.exit(0)
bitcoin_bin_path = sys.argv[1]
sidechain_bin_path = os.path.normpath(os.path.dirname(os.path.realpath(__file__))+"/../../src")
if len(sys.argv) > 2:
    sidechain_bin_path = sys.argv[2]

print(bitcoin_bin_path)
print(sidechain_bin_path)

# Sync mempool, make a block, sync blocks
def sync_all(sidechain, sidechain2):
    timeout = 20
    while len(sidechain.getrawmempool()) != len(sidechain2.getrawmempool()):
        time.sleep(1)
        timeout -= 1
        if timeout == 0:
            raise Exception("Peg-in has failed to propagate.")
    block = sidechain2.generate(1)
    while sidechain.getblockcount() != sidechain2.getblockcount():
        time.sleep(1)
        timeout -= 1
        if timeout == 0:
            raise Exception("Blocks are not propagating.")
    return block

fedpeg_key="cPxqWyf1HDGpGFH1dnfjz8HbiWxvwG8WXyetbuAiw4thKXUdXLpR"
fedpeg_pubkey="512103dff4923d778550cc13ce0d887d737553b4b58f4e8e886507fc39f5e447b2186451ae"

bitcoin_datadir="/tmp/"+''.join(random.choice('0123456789ABCDEF') for i in range(5))
bitcoin_pass=''.join(random.choice('0123456789ABCDEF') for i in range(10))
sidechain_datadir="/tmp/"+''.join(random.choice('0123456789ABCDEF') for i in range(5))
sidechain_pass=''.join(random.choice('0123456789ABCDEF') for i in range(10))
sidechain2_datadir="/tmp/"+''.join(random.choice('0123456789ABCDEF') for i in range(5))
sidechain2_pass=''.join(random.choice('0123456789ABCDEF') for i in range(10))

bitcoin_port = 8000 + os.getpid()%999
sidechain_port = bitcoin_port + 1
sidechain2_port = bitcoin_port + 2
sidechain1_p2p_port = bitcoin_port + 3
sidechain2_p2p_port = bitcoin_port + 4

os.makedirs(bitcoin_datadir)
os.makedirs(sidechain_datadir)
os.makedirs(sidechain2_datadir)

with open(os.path.join(bitcoin_datadir, "bitcoin.conf"), 'w') as f:
        f.write("regtest=1\n")
        f.write("rpcuser=bitcoinrpc\n")
        f.write("rpcpassword="+bitcoin_pass+"\n")
        f.write("rpcport="+str(bitcoin_port)+"\n")
        f.write("discover=0\n")
        f.write("listen=0\n")
        f.write("testnet=0\n")
        f.write("txindex=1\n")
        f.write("daemon=1\n")
        f.write("listen=0\n")

with open(os.path.join(sidechain_datadir, "elements.conf"), 'w') as f:
        f.write("regtest=1\n")
        f.write("rpcuser=sidechainrpc\n")
        f.write("rpcpassword="+sidechain_pass+"\n")
        f.write("rpcport="+str(sidechain_port)+"\n")
        f.write("discover=0\n")
        f.write("testnet=0\n")
        f.write("txindex=1\n")
        f.write("fedpegscript="+fedpeg_pubkey+"\n")
        f.write("daemon=1\n")
        f.write("mainchainrpchost=127.0.0.1\n")
        f.write("mainchainrpcport="+str(bitcoin_port)+"\n")
        f.write("mainchainrpcuser=bitcoinrpc\n")
        f.write("mainchainrpcpassword="+bitcoin_pass+"\n")
        f.write("validatepegin=1\n")
        f.write("validatepegout=0\n")
        f.write("port="+str(sidechain1_p2p_port)+"\n")
        f.write("connect=localhost:"+str(sidechain2_p2p_port)+"\n")
        f.write("listen=1\n")

with open(os.path.join(sidechain2_datadir, "elements.conf"), 'w') as f:
        f.write("regtest=1\n")
        f.write("rpcuser=sidechainrpc2\n")
        f.write("rpcpassword="+sidechain2_pass+"\n")
        f.write("rpcport="+str(sidechain2_port)+"\n")
        f.write("discover=0\n")
        f.write("testnet=0\n")
        f.write("txindex=1\n")
        f.write("fedpegscript="+fedpeg_pubkey+"\n")
        f.write("daemon=1\n")
        f.write("mainchainrpchost=127.0.0.1\n")
        f.write("mainchainrpcport="+str(bitcoin_port)+"\n")
        f.write("mainchainrpcuser=bitcoinrpc\n")
        f.write("mainchainrpcpassword="+bitcoin_pass+"\n")
        f.write("validatepegin=1\n")
        f.write("validatepegout=0\n")
        f.write("port="+str(sidechain2_p2p_port)+"\n")
        f.write("connect=localhost:"+str(sidechain1_p2p_port)+"\n")
        f.write("listen=1\n")

try:

    # Default is 8, meaning 8+2 confirms for wallet acceptance normally
    # this will require 10+2.
    sidechain_args = " -peginconfirmationdepth=10 "

    # Start daemons
    print("Starting daemons at "+bitcoin_datadir+", "+sidechain_datadir+" and "+sidechain2_datadir)
    bitcoindstart = bitcoin_bin_path+"/bitcoind -datadir="+bitcoin_datadir
    subprocess.Popen(bitcoindstart.split(), stdout=subprocess.PIPE)

    sidechainstart = sidechain_bin_path+"/elementsd -datadir="+sidechain_datadir + sidechain_args
    subprocess.Popen(sidechainstart.split(), stdout=subprocess.PIPE)

    sidechain2start = sidechain_bin_path+"/elementsd -datadir="+sidechain2_datadir + sidechain_args
    subprocess.Popen(sidechain2start.split(), stdout=subprocess.PIPE)

    print("Daemons started")
    time.sleep(3)

    bitcoin = AuthServiceProxy("http://bitcoinrpc:"+bitcoin_pass+"@127.0.0.1:"+str(bitcoin_port))
    sidechain = AuthServiceProxy("http://sidechainrpc:"+sidechain_pass+"@127.0.0.1:"+str(sidechain_port))
    sidechain2 = AuthServiceProxy("http://sidechainrpc2:"+sidechain2_pass+"@127.0.0.1:"+str(sidechain2_port))
    print("Daemons started, making blocks to get funds")

    bitcoin.generate(102)
    sidechain.generate(101)

    addr = bitcoin.getnewaddress()
    addrs = sidechain.getpeginaddress()
    # Enough value to create 3 outputs, 2 of which are max hidden size at 32 bits of hiding
    txid1 = bitcoin.sendtoaddress(addrs["mainchain_address"], 99)
    # 10+2 confirms required to get into mempool and confirm
    bitcoin.generate(11)
    time.sleep(2)
    proof = bitcoin.gettxoutproof([txid1])
    raw = bitcoin.getrawtransaction(txid1)

    print("Attempting peg-in")
    try:
        pegtxid = sidechain.claimpegin(raw, proof)
        raise Exception("Peg-in should not mature enough yet, need another block.")
    except JSONRPCException as e:
        assert("Peg-in Bitcoin transaction needs more confirmations to be sent." in e.error["message"])
        pass

    # Should fail due to non-matching wallet address
    try:
        pegtxid = sidechain.claimpegin(raw, proof, sidechain.getnewaddress())
        raise Exception("Peg-in with non-matching claim_script should fail.")
    except JSONRPCException as e:
        assert("Given claim_script does not match the given Bitcoin transaction." in e.error["message"])
        pass

    # 12 confirms allows in mempool
    bitcoin.generate(1)
    # Should succeed via wallet lookup for address match, and when given
    pegtxid1 = sidechain.claimpegin(raw, proof)

    # This transaction should have 4 outputs, first 3 of which are payments to self
    # all if which are below 2^32 - 1 in satoshis
    raw_peg_details = sidechain.getrawtransaction(pegtxid1, 1)
    assert(len(raw_peg_details["vout"]) == 4)
    for i in range(3):
            assert(raw_peg_details["vout"][i]["value"] <= Decimal('42.94967295'))

    # Will invalidate the block that confirms this transaction later
    blockhash = sync_all(sidechain, sidechain2)
    sidechain.generate(5)

    tx1 = sidechain.gettransaction(pegtxid1)

    if "confirmations" in tx1 and tx1["confirmations"] == 6:
        print("Peg-in is confirmed: Success!")
    else:
        raise Exception("Peg-in confirmation has failed.")

    # Look at pegin fields
    decoded = sidechain.decoderawtransaction(tx1["hex"])
    assert decoded["vin"][0]["is_pegin"] == True
    assert len(decoded["vin"][0]["pegin_witness"]) > 0

    # Quick reorg checks of pegs
    sidechain.invalidateblock(blockhash[0])
    if sidechain.gettransaction(pegtxid1)["confirmations"] != 0:
        raise Exception("Peg-in didn't unconfirm after invalidateblock call.")
    # Re-enters block
    sidechain.generate(1)
    if sidechain.gettransaction(pegtxid1)["confirmations"] != 1:
        raise Exception("Peg-in should have one confirm on side block.")
    sidechain.reconsiderblock(blockhash[0])
    if sidechain.gettransaction(pegtxid1)["confirmations"] != 6:
        raise Exception("Peg-in should be back to 6 confirms.")

    # Do many claims in mempool
    n_claims = 100

    print("Flooding mempool with many small claims")
    pegtxs = []
    sidechain.generate(101)

    for i in range(n_claims):
        addrs = sidechain.getpeginaddress()
        txid = bitcoin.sendtoaddress(addrs["mainchain_address"], 1)
        bitcoin.generate(12)
        proof = bitcoin.gettxoutproof([txid])
        raw = bitcoin.getrawtransaction(txid)
        pegtxs += [sidechain.claimpegin(raw, proof)]

    sync_all(sidechain, sidechain2)

    sidechain2.generate(1)
    for pegtxid in pegtxs:
        tx = sidechain.gettransaction(pegtxid)
        if "confirmations" not in tx or tx["confirmations"] == 0:
            raise Exception("Peg-in confirmation has failed.")

    print("Success!")

except JSONRPCException as e:
        print("Pegging testing failed, aborting:")
        print(e.error)
except Exception as e:
        print("Pegging testing failed, aborting:")
        print(e)

print("Stopping daemons and cleaning up")
bitcoin.stop()
sidechain.stop()

time.sleep(5)

shutil.rmtree(sidechain_datadir)
shutil.rmtree(bitcoin_datadir)
