#!/usr/bin/env python2

from test_framework.authproxy import AuthServiceProxy, JSONRPCException
import os
import random
import sys
import time
import subprocess
import shutil
from decimal import Decimal

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
def sync_all(sidechain, sidechain2, makeblock=True):
    block = ""
    timeout = 20
    while len(sidechain.getrawmempool()) != len(sidechain2.getrawmempool()):
        time.sleep(1)
        timeout -= 1
        if timeout == 0:
            raise Exception("Peg-in has failed to propagate.")
    if makeblock:
        block = sidechain2.generate(1)
    while sidechain.getblockcount() != sidechain2.getblockcount():
        time.sleep(1)
        timeout -= 1
        if timeout == 0:
            raise Exception("Blocks are not propagating.")
    return block

fedpeg_key="cPxqWyf1HDGpGFH1dnfjz8HbiWxvwG8WXyetbuAiw4thKXUdXLpR"
fedpeg_pubkey="512103dff4923d778550cc13ce0d887d737553b4b58f4e8e886507fc39f5e447b2186451ae"

def get_pseudorandom_str(str_length=10):
    return ''.join(random.choice('0123456789ABCDEF') for i in range(str_length))

def get_temp_dir(nodename):
    return "/tmp/%s_%s" % (nodename, get_pseudorandom_str())

bitcoin_datadir = get_temp_dir('bitcoin')
bitcoin_pass = get_pseudorandom_str()
sidechain_datadir = get_temp_dir('sidechain')
sidechain_pass = get_pseudorandom_str()
sidechain2_datadir = get_temp_dir('sidechain2')
sidechain2_pass = get_pseudorandom_str()
bitcoin2_datadir = get_temp_dir('bitcoin2')
bitcoin2_rpccookiefile = bitcoin2_datadir + '/regtest/.cookie'

bitcoin_port = 8000 + os.getpid()%999
sidechain_port = bitcoin_port + 1
sidechain2_port = bitcoin_port + 2
sidechain1_p2p_port = bitcoin_port + 3
sidechain2_p2p_port = bitcoin_port + 4
bitcoin2_port = bitcoin_port + 5
bitcoin2_p2p_port = bitcoin_port + 6
bitcoin_p2p_port = bitcoin_port + 7

bitcoin = None
bitcoin2 = None
sidechain = None
sidechain2 = None

os.makedirs(bitcoin_datadir)
os.makedirs(sidechain_datadir)
os.makedirs(sidechain2_datadir)
os.makedirs(bitcoin2_datadir)

def write_bitcoin_conf(datadir, rpcport, rpcpass=None, p2p_port=None, connect_port=None):
    with open(os.path.join(datadir, "bitcoin.conf"), 'w') as f:
        f.write("regtest=1\n")
        if p2p_port:
            f.write("port="+str(p2p_port)+"\n")
        if rpcpass:
            f.write("rpcuser=bitcoinrpc\n")
            f.write("rpcpassword="+rpcpass+"\n")
        f.write("rpcport="+str(rpcport)+"\n")
        f.write("discover=0\n")
        f.write("testnet=0\n")
        f.write("txindex=1\n")
        f.write("daemon=1\n")
        # To make sure bitcoind gives back p2pkh no matter version
        f.write("addresstype=legacy\n")
        if connect_port:
            f.write("connect=localhost:"+str(connect_port)+"\n")
            f.write("listen=1\n")
        else:
            f.write("listen=0\n")

write_bitcoin_conf(bitcoin_datadir, bitcoin_port, bitcoin_pass, p2p_port=bitcoin_p2p_port, connect_port=bitcoin2_p2p_port)
write_bitcoin_conf(bitcoin2_datadir, bitcoin2_port, rpcpass=None, p2p_port=bitcoin2_p2p_port, connect_port=bitcoin_p2p_port)

with open(os.path.join(sidechain_datadir, "ocean.conf"), 'w') as f:
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
        f.write("port="+str(sidechain1_p2p_port)+"\n")
        f.write("connect=localhost:"+str(sidechain2_p2p_port)+"\n")
        f.write("listen=1\n")
        f.write("fallbackfee=0.0001\n")
        f.write("initialfreecoins=2100000000000000\n")

with open(os.path.join(sidechain2_datadir, "ocean.conf"), 'w') as f:
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
        f.write("mainchainrpcport="+str(bitcoin2_port)+"\n")
        f.write("mainchainrpccookiefile=%s\n" % bitcoin2_rpccookiefile)
        f.write("validatepegin=1\n")
        f.write("port="+str(sidechain2_p2p_port)+"\n")
        f.write("connect=localhost:"+str(sidechain1_p2p_port)+"\n")
        f.write("listen=1\n")
        f.write("fallbackfee=0.0001\n")
        f.write("initialfreecoins=2100000000000000\n")

def test_pegout(parent_chain_addr, sidechain):
    pegout_txid = sidechain.sendtomainchain(parent_chain_addr, 1)
    raw_pegout = sidechain.getrawtransaction(pegout_txid, True)
    assert 'vout' in raw_pegout and len(raw_pegout['vout']) > 0
    pegout_tested = False
    for output in raw_pegout['vout']:
        scriptPubKey = output['scriptPubKey']
        if 'type' in scriptPubKey and scriptPubKey['type'] == 'nulldata':
            assert ('pegout_hex' in scriptPubKey and 'pegout_asm' in scriptPubKey and 'pegout_type' in scriptPubKey and
                    'pegout_chain' in scriptPubKey and 'pegout_reqSigs' in scriptPubKey and 'pegout_addresses' in scriptPubKey)
            assert scriptPubKey['pegout_chain'] == '0f9188f13cb7b2c71f2a335e3a4fc328bf5beb436012afca590b1a11466e2206' #testnet3
            assert scriptPubKey['pegout_reqSigs'] == 1
            assert parent_chain_addr in scriptPubKey['pegout_addresses']
            pegout_tested = True
            break
    assert pegout_tested

try:

    # Default is 8, meaning 8+2 confirms for wallet acceptance normally
    # this will require 10+2.
    sidechain_args = " -peginconfirmationdepth=10 "

    # Start daemons
    print("Starting daemons at "+bitcoin_datadir+", "+bitcoin2_datadir+", "+sidechain_datadir+" and "+sidechain2_datadir)
    bitcoindstart = bitcoin_bin_path+"/bitcoind -datadir="+bitcoin_datadir
    subprocess.Popen(bitcoindstart.split(), stdout=subprocess.PIPE)

    bitcoind2start = bitcoin_bin_path+"/bitcoind -datadir="+bitcoin2_datadir
    subprocess.Popen(bitcoind2start.split(), stdout=subprocess.PIPE)

    sidechainstart = sidechain_bin_path+"/oceand -datadir="+sidechain_datadir + sidechain_args
    subprocess.Popen(sidechainstart.split(), stdout=subprocess.PIPE)

    sidechain2start = sidechain_bin_path+"/oceand -datadir="+sidechain2_datadir + sidechain_args
    subprocess.Popen(sidechain2start.split(), stdout=subprocess.PIPE)

    print("Daemons started")
    time.sleep(3)

    with open(bitcoin2_rpccookiefile, 'r') as f:
        bitcoin2_rpccookie = f.readline()

    bitcoin = AuthServiceProxy("http://bitcoinrpc:"+bitcoin_pass+"@127.0.0.1:"+str(bitcoin_port))
    bitcoin2 = AuthServiceProxy("http://"+ bitcoin2_rpccookie +"@127.0.0.1:"+str(bitcoin2_port))
    sidechain = AuthServiceProxy("http://sidechainrpc:"+sidechain_pass+"@127.0.0.1:"+str(sidechain_port))
    sidechain2 = AuthServiceProxy("http://sidechainrpc2:"+sidechain2_pass+"@127.0.0.1:"+str(sidechain2_port))
    print("Daemons started, making blocks to get funds")

    bitcoin.generate(101)
    sidechain.generate(101)

    addr = bitcoin.getnewaddress()

    # First, blackhole all 21M bitcoin that already exist(and test subtractfrom)
    assert(sidechain.getwalletinfo()["balance"]["bitcoin"] == 21000000)
    sidechain.sendtomainchain(addr, 21000000, True)
    assert("bitcoin" not in sidechain.getwalletinfo()["balance"])

    sidechain.generate(101)

    addrs = sidechain.getpeginaddress()
    txid1 = bitcoin.sendtoaddress(addrs["mainchain_address"], 24)
    # 10+2 confirms required to get into mempool and confirm
    bitcoin.generate(1)
    time.sleep(2)
    proof = bitcoin.gettxoutproof([txid1])
    raw = bitcoin.getrawtransaction(txid1)

    print("Attempting peg-in")
    # First attempt fails the consensus check but gives useful result
    try:
        pegtxid = sidechain.claimpegin(raw, proof)
        raise Exception("Peg-in should not be mature enough yet, need another block.")
    except JSONRPCException as e:
        assert("Peg-in Bitcoin transaction needs more confirmations to be sent." in e.error["message"])
        pass

    # Second attempt simply doesn't hit mempool bar
    bitcoin.generate(10)
    try:
        pegtxid = sidechain.claimpegin(raw, proof)
        raise Exception("Peg-in should not be mature enough yet, need another block.")
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

    # Will invalidate the block that confirms this transaction later
    sync_all(bitcoin, bitcoin2)
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
    # Check that there's sufficient fee for the peg-in
    vsize = decoded["vsize"]
    fee_output = decoded["vout"][1]
    fallbackfee_pervbyte = Decimal("0.00001")/Decimal("1000")
    assert fee_output["scriptPubKey"]["type"] == "fee"
    assert fee_output["value"] >= fallbackfee_pervbyte*vsize

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
    n_claims = 5

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

    sync_all(bitcoin, bitcoin2)
    sync_all(sidechain, sidechain2)

    sidechain2.generate(1)
    for pegtxid in pegtxs:
        tx = sidechain.gettransaction(pegtxid)
        if "confirmations" not in tx or tx["confirmations"] == 0:
            raise Exception("Peg-in confirmation has failed.")

    print("Test pegout")
    test_pegout(bitcoin.getnewaddress(), sidechain)

    print("Test pegout P2SH")
    parent_chain_addr = bitcoin.getnewaddress()
    parent_pubkey = bitcoin.validateaddress(parent_chain_addr)["pubkey"]
    parent_chain_p2sh_addr = bitcoin.createmultisig(1, [parent_pubkey])["address"]
    test_pegout(parent_chain_p2sh_addr, sidechain)

    print("Test pegout Garbage")
    parent_chain_addr = "garbage"
    try:
        test_pegout(parent_chain_addr, sidechain)
        raise Exception("A garbage address should fail.")
    except JSONRPCException as e:
        assert("Invalid Bitcoin address" in e.error["message"])
        pass

    print("Test pegout Garbage valid")
    prev_txid = sidechain.sendtoaddress(sidechain.getnewaddress(), 1)
    sidechain.generate(1)
    pegout_chain = 'a' * 64
    pegout_hex = 'b' * 500
    inputs = [{"txid": prev_txid, "vout": 0}]
    outputs = {"vdata": [pegout_chain, pegout_hex]}
    rawtx = sidechain.createrawtransaction(inputs, outputs)
    raw_pegout = sidechain.decoderawtransaction(rawtx)

    assert 'vout' in raw_pegout and len(raw_pegout['vout']) > 0
    pegout_tested = False
    for output in raw_pegout['vout']:
        scriptPubKey = output['scriptPubKey']
        if 'type' in scriptPubKey and scriptPubKey['type'] == 'nulldata':
            assert ('pegout_hex' in scriptPubKey and 'pegout_asm' in scriptPubKey and 'pegout_type' in scriptPubKey and
                    'pegout_chain' in scriptPubKey and 'pegout_reqSigs' not in scriptPubKey and 'pegout_addresses' not in scriptPubKey)
            assert scriptPubKey['pegout_type'] == 'nonstandard'
            assert scriptPubKey['pegout_chain'] == pegout_chain
            assert scriptPubKey['pegout_hex'] == pegout_hex
            pegout_tested = True
            break
    assert pegout_tested

    print ("Now test failure to validate peg-ins based on intermittant bitcoind rpc failure")
    bitcoin2.stop()
    # give bitcoin2 time to stop
    time.sleep(1)
    txid = bitcoin.sendtoaddress(addrs["mainchain_address"], 1)
    bitcoin.generate(12)
    proof = bitcoin.gettxoutproof([txid])
    raw = bitcoin.getrawtransaction(txid)
    stuck_peg = sidechain.claimpegin(raw, proof)
    sidechain.generate(1)
    print("Waiting to ensure block is being rejected by sidechain2")
    time.sleep(5)

    assert(sidechain.getblockcount() != sidechain2.getblockcount())

    bitcoind2start = bitcoin_bin_path+"/bitcoind -datadir="+bitcoin2_datadir
    subprocess.Popen(bitcoind2start.split(), stdout=subprocess.PIPE)
    print("Restarting bitcoind2")
    time.sleep(5)
    with open(bitcoin2_rpccookiefile, 'r') as f:
        bitcoin2_rpccookie = f.readline()
    bitcoin2 = AuthServiceProxy("http://"+ bitcoin2_rpccookie +"@127.0.0.1:"+str(bitcoin2_port))

    # Don't make a block, race condition when pegin-invalid block
    # is awaiting further validation, nodes reject subsequent blocks
    # even ones they create
    sync_all(sidechain, sidechain2, False)
    print("Now send funds out in two stages, partial, and full")
    some_btc_addr = bitcoin.getnewaddress()
    bal_1 = sidechain.getwalletinfo()["balance"]["bitcoin"]
    try:
        sidechain.sendtomainchain(some_btc_addr, bal_1 + 1)
        raise Exception("Sending out too much; should have failed")
    except JSONRPCException as e:
        assert("Insufficient funds" in e.error["message"])
        pass

    assert(sidechain.getwalletinfo()["balance"]["bitcoin"] == bal_1)
    try:
        sidechain.sendtomainchain(some_btc_addr+"b", bal_1 - 1)
        raise Exception("Sending to invalid address; should have failed")
    except JSONRPCException as e:
        assert("Invalid Bitcoin address" in e.error["message"])
        pass

    assert(sidechain.getwalletinfo()["balance"]["bitcoin"] == bal_1)
    try:
        sidechain.sendtomainchain("1Nro9WkpaKm9axmcfPVp79dAJU1Gx7VmMZ", bal_1 - 1)
        raise Exception("Sending to mainchain address when should have been testnet; should have failed")
    except JSONRPCException as e:
        assert("Invalid Bitcoin address" in e.error["message"])
        pass

    assert(sidechain.getwalletinfo()["balance"]["bitcoin"] == bal_1)

    peg_out_txid = sidechain.sendtomainchain(some_btc_addr, 1)

    peg_out_details = sidechain.decoderawtransaction(sidechain.getrawtransaction(peg_out_txid))
    # peg-out, change
    assert(len(peg_out_details["vout"]) == 3)
    found_pegout_value = False
    for output in peg_out_details["vout"]:
        if "value" in output and output["value"] == 1:
            found_pegout_value = True
    assert(found_pegout_value)

    bal_2 = sidechain.getwalletinfo()["balance"]["bitcoin"]
    # Make sure balance went down
    assert(bal_2 + 1 < bal_1)

    sidechain.sendtomainchain(some_btc_addr, bal_2, True)

    assert("bitcoin" not in sidechain.getwalletinfo()["balance"])

    print("Success!")

except JSONRPCException as e:
        print("Pegging testing failed, aborting:")
        print(e.error)
except Exception as e:
        print("Pegging testing failed, aborting:")
        print(e)

print("Stopping daemons and cleaning up")
if bitcoin is not None:
    bitcoin.stop()
if bitcoin2 is not None:
    bitcoin2.stop()
if sidechain is not None:
    sidechain.stop()
if sidechain2 is not None:
    sidechain2.stop()

time.sleep(5)

shutil.rmtree(bitcoin2_datadir)
shutil.rmtree(sidechain2_datadir)
shutil.rmtree(sidechain_datadir)
shutil.rmtree(bitcoin_datadir)
