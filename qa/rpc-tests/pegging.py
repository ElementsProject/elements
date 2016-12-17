#!/usr/bin/env python2

from test_framework.authproxy import AuthServiceProxy
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

pak_key_1="cPrpBrgbpmkNGYayVBkNNrRsjyWqJK61W7yC2EnJNob98ZhAzuFm"
pak_pubkey_1="03701c7d314219f76d193c8762be96a2f68c1b387e3cc00dcc7020e13b1670bfdb"

pak_key_2="cW2b8y2Vp1QD3YkrQL1bpT589DQbaRBMjRZgmz6R8ykzFni7cocX"
pak_pubkey_2="03b86dae93129f64dfc3ae5eeca0be0cb9e439b9d23d18c08c8f7358136c0d8ce4"

bitcoin_datadir="/tmp/"+''.join(random.choice('0123456789ABCDEF') for i in range(5))
bitcoin_pass=''.join(random.choice('0123456789ABCDEF') for i in range(10))
sidechain_datadir="/tmp/"+''.join(random.choice('0123456789ABCDEF') for i in range(5))
sidechain_pass=''.join(random.choice('0123456789ABCDEF') for i in range(10))

bitcoin_port = 8000 + os.getpid()%999
sidechain_port = bitcoin_port + 1

os.makedirs(bitcoin_datadir)
os.makedirs(sidechain_datadir)

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

with open(os.path.join(sidechain_datadir, "elements.conf"), 'w') as f:
        f.write("regtest=1\n")
        f.write("rpcuser=sidechainrpc\n")
        f.write("rpcpassword="+sidechain_pass+"\n")
        f.write("rpcport="+str(sidechain_port)+"\n")
        f.write("discover=0\n")
        f.write("listen=0\n")
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

# Start daemons
print("Starting daemons at "+bitcoin_datadir+" and "+sidechain_datadir)
bitcoindstart = sys.argv[1]+"/bitcoind -datadir="+bitcoin_datadir
subprocess.Popen(bitcoindstart.split(), stdout=subprocess.PIPE)

sidechainstart = sys.argv[2]+"/elementsd -datadir="+sidechain_datadir
subprocess.Popen(sidechainstart.split(), stdout=subprocess.PIPE)

print("Daemons started")
time.sleep(2)

bitcoin = AuthServiceProxy("http://bitcoinrpc:"+bitcoin_pass+"@127.0.0.1:"+str(bitcoin_port))
sidechain = AuthServiceProxy("http://sidechainrpc:"+sidechain_pass+"@127.0.0.1:"+str(sidechain_port))
print("Daemons started, making blocks to get funds")

bitcoin.generate(101)
sidechain.generate(101)

addr = bitcoin.getnewaddress()

# Lockup some funds to unlock later
sidechain.sendtomainchain(addr, 50)
sidechain.generate(101)

addrs = sidechain.getpeginaddress()
txid = bitcoin.sendtoaddress(addrs["mainchain_address"], 49)
bitcoin.generate(10)
proof = bitcoin.gettxoutproof([txid])
raw = bitcoin.getrawtransaction(txid)

print("Attempting peg-in")
pegtxid = sidechain.claimpegin(addrs["sidechain_address"], raw, proof)
sidechain.generate(1)

tx = sidechain.gettransaction(pegtxid)

if "confirmations" in tx and tx["confirmations"] > 0:
    print("Peg-in is confirmed: Success!")
else:
    print("Peg-in has failed.")



print("Stopping daemons and cleaning up")
bitcoin.stop()
sidechain.stop()

time.sleep(5)

shutil.rmtree(sidechain_datadir)
shutil.rmtree(bitcoin_datadir)
