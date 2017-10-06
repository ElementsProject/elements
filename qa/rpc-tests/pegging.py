#!/usr/bin/env python2

from test_framework.authproxy import AuthServiceProxy, JSONRPCException
import os
import random
import sys
import time
import subprocess
import shutil

if len(sys.argv) != 3:
    print("paths to bitcoind and sidechain daemon must be included as arguments")
    sys.exit(0)
print(sys.argv[1])
print(sys.argv[2])

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

    # Default is 8, meaning 8+2 confirms for mempool acceptance normally
    # this will require 10+2.
    sidechain_args = " -peginconfirmationdepth=10 "

    # Start daemons
    print("Starting daemons at "+bitcoin_datadir+", "+sidechain_datadir+" and "+sidechain2_datadir)
    bitcoindstart = sys.argv[1]+"/bitcoind -datadir="+bitcoin_datadir
    subprocess.Popen(bitcoindstart.split(), stdout=subprocess.PIPE)

    sidechainstart = sys.argv[2]+"/elementsd -datadir="+sidechain_datadir + sidechain_args
    subprocess.Popen(sidechainstart.split(), stdout=subprocess.PIPE)

    sidechain2start = sys.argv[2]+"/elementsd -datadir="+sidechain2_datadir + sidechain_args
    subprocess.Popen(sidechain2start.split(), stdout=subprocess.PIPE)

    print("Daemons started")
    time.sleep(3)

    bitcoin = AuthServiceProxy("http://bitcoinrpc:"+bitcoin_pass+"@127.0.0.1:"+str(bitcoin_port))
    sidechain = AuthServiceProxy("http://sidechainrpc:"+sidechain_pass+"@127.0.0.1:"+str(sidechain_port))
    sidechain2 = AuthServiceProxy("http://sidechainrpc2:"+sidechain2_pass+"@127.0.0.1:"+str(sidechain2_port))
    print("Daemons started, making blocks to get funds")

    bitcoin.generate(101)
    sidechain.generate(101)

    addr = bitcoin.getnewaddress()

    # Lockup some funds to unlock later
    sidechain.sendtomainchain(addr, 50)
    # Tests withdrawlock tracking in database
    sidechain.generate(1)
    # Tests withdrawlock in mempool
    sidechain.sendtomainchain(addr, 50)

    addrs = sidechain.getpeginaddress()
    txid1 = bitcoin.sendtoaddress(addrs["mainchain_address"], 24)
    txid2 = bitcoin.sendtoaddress(addrs["mainchain_address"], 24)
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
        assert("Withdraw proof validation failed" in e.error["message"])
        pass

    # Should fail due to non-matching wallet address
    try:
        pegtxid = sidechain.claimpegin(raw, proof, sidechain.getnewaddress())
        raise Exception("Peg-in with non-matching address should fail.")
    except JSONRPCException as e:
        assert("Failed to find output in bitcoinTx to the mainchain_address" in e.error["message"])
        pass

    # 12 confirms allows in mempool
    bitcoin.generate(1)

    timeout = 20
    # Both should succeed via wallet lookup for address match, and when given
    pegtxid1 = sidechain.claimpegin(raw, proof)

    proof = bitcoin.gettxoutproof([txid2])
    raw = bitcoin.getrawtransaction(txid2)
    pegtxid2 = sidechain.claimpegin(raw, proof, addrs["sidechain_address"])

    while len(sidechain.getrawmempool()) != len(sidechain2.getrawmempool()):
        time.sleep(1)
        timeout -= 1
        if timeout == 0:
            raise Exception("Peg-in has failed to propagate.")
    sidechain2.generate(1)
    while sidechain.getblockcount() != sidechain2.getblockcount():
        time.sleep(1)
        timeout -= 1
        if timeout == 0:
            raise Exception("Blocks are not propagating.")


    tx1 = sidechain.gettransaction(pegtxid1)
    tx2 = sidechain.gettransaction(pegtxid2)

    if "confirmations" in tx1 and tx1["confirmations"] > 0 and "confirmations" in tx2 and tx2["confirmations"] > 0:
        print("Peg-in is confirmed: Success!")
    else:
        raise Exception("Peg-in confirmation has failed.")

    # Make a few large locks, then do many claims in mempool
    n_locks = 10
    n_claims = 30

    print("Flooding mempool with many small claims")
    pegtxs = []
    for i in range(n_locks):
        # Lockup some funds to unlock later
        sidechain.sendtomainchain(addr, 50)
        sidechain.generate(1)
    sidechain.generate(101)

    for i in range(n_claims):
        addrs = sidechain.getpeginaddress()
        txid = bitcoin.sendtoaddress(addrs["mainchain_address"], 1)
        bitcoin.generate(12)
        proof = bitcoin.gettxoutproof([txid])
        raw = bitcoin.getrawtransaction(txid)
        pegtxs += [sidechain.claimpegin(raw, proof)]

    sidechain.generate(1)
    for pegtxid in pegtxs:
        tx = sidechain.gettransaction(pegtxid)
        if "confirmations" not in tx or tx["confirmations"] == 0:
            raise Exception("Peg-in confirmation has failed.")

    print("Success!")

    # Testing sidechain info RPC
    sideinfo = sidechain.getsidechaininfo()
    assert sideinfo["fedpegscript"] == fedpeg_pubkey
    assert sideinfo["pegged_asset"] == sidechain.dumpassetlabels()["bitcoin"]
    assert sideinfo["min_peg_diff"] == "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
    assert sideinfo["parent_blockhash"] == "0f9188f13cb7b2c71f2a335e3a4fc328bf5beb436012afca590b1a11466e2206"

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
