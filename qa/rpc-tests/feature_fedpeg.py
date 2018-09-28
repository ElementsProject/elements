#!/usr/bin/env python3

from decimal import Decimal
import os
import json
import time

from test_framework.authproxy import JSONRPCException
from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import (
    connect_nodes_bi,
    rpc_auth_pair,
    rpc_port,
    p2p_port,
    start_node,
    stop_node,
)

def get_new_unconfidential_address(node):
    addr = node.getnewaddress()
    val_addr = node.validateaddress(addr)
    if 'unconfidential' in val_addr:
        return val_addr['unconfidential']
    return val_addr['address']

class FedPegTest(BitcoinTestFramework):

    def __init__(self):
        super().__init__()
        self.setup_clean_chain = True
        self.num_nodes = 4

    def add_options(self, parser):
        parser.add_option("--parent_binpath", dest="parent_binpath", default="",
                          help="Use a different binary for launching nodes")
        parser.add_option("--parent_bitcoin", dest="parent_bitcoin", default=False, action="store_true",
                          help="Parent nodes are Bitcoin")

    def setup_network(self, split=False):
        if self.options.parent_bitcoin and self.options.parent_binpath == "":
            raise Exception("Can't run with --parent_bitcoin without specifying --parent_binpath")
        self.nodes = []
        self.extra_args = []
        # Parent chain args
        for n in range(2):
            # We want to test the rpc cookie method so we force the use of a
            # dummy conf file to avoid loading rpcuser/rpcpassword lines
            use_cookie_auth = n==1
            rpc_u, rpc_p = rpc_auth_pair(n)
            if self.options.parent_bitcoin:
                self.parent_chain = 'regtest'
                self.extra_args.append([
                    "-conf=dummy",
                    "-printtoconsole=0",
                    "-addresstype=legacy", # To make sure bitcoind gives back p2pkh no matter version
                    "-deprecatedrpc=validateaddress",
                    "-port="+str(p2p_port(n)),
                    "-rpcport="+str(rpc_port(n))
                ])
            else:
                self.parent_chain = 'parent'
                self.extra_args.append([
                    "-conf=dummy",
                    "-printtoconsole=0",
                    '-validatepegin=0',
                    '-anyonecanspendaremine',
                    '-initialfreecoins=2100000000000000',
                    "-port="+str(p2p_port(n)),
                    "-rpcport="+str(rpc_port(n))
                ])
            # Only first parent uses name/password, the 2nd uses cookie auth
            if not use_cookie_auth:
                self.extra_args[n].extend(["-rpcuser="+rpc_u, "-rpcpassword="+rpc_p])

            self.binary = self.options.parent_binpath if self.options.parent_binpath != "" else None
            self.nodes.append(start_node(n, self.options.tmpdir, self.extra_args[n], binary=self.binary, chain=self.parent_chain, cookie_auth=use_cookie_auth))

        connect_nodes_bi(self.nodes, 0, 1)
        self.parentgenesisblockhash = self.nodes[0].getblockhash(0)
        print('parentgenesisblockhash', self.parentgenesisblockhash)
        if not self.options.parent_bitcoin:
            parent_pegged_asset = self.nodes[0].getsidechaininfo()['pegged_asset']

        # Sidechain args
        self.fedpeg_script = "512103dff4923d778550cc13ce0d887d737553b4b58f4e8e886507fc39f5e447b2186451ae"
        parent_chain_signblockscript = '51'
        for n in range(2):
            used_cookie_auth = n==1
            rpc_u, rpc_p = rpc_auth_pair(n)
            args = [
                "-printtoconsole=0",
                '-parentgenesisblockhash=%s' % self.parentgenesisblockhash,
                '-validatepegin=1',
                '-fedpegscript=%s' % self.fedpeg_script,
                '-anyonecanspendaremine=0',
                '-initialfreecoins=0',
                '-peginconfirmationdepth=10',
                '-mainchainrpchost=127.0.0.1',
                '-mainchainrpcport=%s' % rpc_port(n),
                '-recheckpeginblockinterval=15', # Long enough to allow failure and repair before timeout
            ]
            if not self.options.parent_bitcoin:
                args.extend([
                    '-parentpubkeyprefix=235',
                    '-parentscriptprefix=75',
                    '-con_parent_chain_signblockscript=%s' % parent_chain_signblockscript,
                    '-con_parent_pegged_asset=%s' % parent_pegged_asset,
                ])

            if used_cookie_auth:
                # Need to specify where to find parent cookie file
                datadir = os.path.join(self.options.tmpdir, "node"+str(n))
                args.append('-mainchainrpccookiefile='+datadir+"/" + self.parent_chain + "/.cookie")
            else:
                args.extend([
                    '-mainchainrpcuser=%s' % rpc_u,
                    '-mainchainrpcpassword=%s' % rpc_p,
                ])

            self.extra_args.append(args)
            self.nodes.append(start_node(n + 2, self.options.tmpdir, self.extra_args[n + 2], chain='sidechain'))

        # We only connect the same-chain nodes, so sync_all works correctly
        connect_nodes_bi(self.nodes, 2, 3)
        self.is_network_split = True
        self.sync_all()

    def test_pegout(self, parent_chain_addr, sidechain):
        pegout_txid = sidechain.sendtomainchain(parent_chain_addr, 1)
        raw_pegout = sidechain.getrawtransaction(pegout_txid, True)
        assert 'vout' in raw_pegout and len(raw_pegout['vout']) > 0
        pegout_tested = False
        for output in raw_pegout['vout']:
            scriptPubKey = output['scriptPubKey']
            if 'type' in scriptPubKey and scriptPubKey['type'] == 'nulldata':
                assert ('pegout_hex' in scriptPubKey and 'pegout_asm' in scriptPubKey and 'pegout_type' in scriptPubKey and
                        'pegout_chain' in scriptPubKey and 'pegout_reqSigs' in scriptPubKey and 'pegout_addresses' in scriptPubKey)
                assert scriptPubKey['pegout_chain'] == self.parentgenesisblockhash
                assert scriptPubKey['pegout_reqSigs'] == 1
                assert parent_chain_addr in scriptPubKey['pegout_addresses']
                pegout_tested = True
                break
        assert pegout_tested

    def run_test(self):
        parent = self.nodes[0]
        parent2 = self.nodes[1]
        sidechain = self.nodes[2]
        sidechain2 = self.nodes[3]

        parent.generate(101)
        sidechain.generate(101)

        addrs = sidechain.getpeginaddress()
        addr = addrs["mainchain_address"]
        print('addrs', addrs)
        print(parent.validateaddress(addr))
        txid1 = parent.sendtoaddress(addr, 24)
        # 10+2 confirms required to get into mempool and confirm
        parent.generate(1)
        time.sleep(2)
        proof = parent.gettxoutproof([txid1])

        raw = parent.getrawtransaction(txid1)
        print('raw', parent.getrawtransaction(txid1, True))

        print("Attempting peg-in")
        # First attempt fails the consensus check but gives useful result
        try:
            pegtxid = sidechain.claimpegin(raw, proof)
            raise Exception("Peg-in should not be mature enough yet, need another block.")
        except JSONRPCException as e:
            print('RPC ERROR:', e.error['message'])
            assert("Peg-in Bitcoin transaction needs more confirmations to be sent." in e.error["message"])

        # Second attempt simply doesn't hit mempool bar
        parent.generate(10)
        try:
            pegtxid = sidechain.claimpegin(raw, proof)
            raise Exception("Peg-in should not be mature enough yet, need another block.")
        except JSONRPCException as e:
            print('RPC ERROR:', e.error['message'])
            assert("Peg-in Bitcoin transaction needs more confirmations to be sent." in e.error["message"])

        try:
            pegtxid = sidechain.createrawpegin(raw, proof, 'AEIOU')
            raise Exception("Peg-in with non-hex claim_script should fail.")
        except JSONRPCException as e:
            print('RPC ERROR:', e.error['message'])
            assert("Given claim_script is not hex." in e.error["message"])

        # Should fail due to non-matching wallet address
        try:
            scriptpubkey = sidechain.validateaddress(get_new_unconfidential_address(sidechain))["scriptPubKey"]
            pegtxid = sidechain.claimpegin(raw, proof, scriptpubkey)
            raise Exception("Peg-in with non-matching claim_script should fail.")
        except JSONRPCException as e:
            print('RPC ERROR:', e.error['message'])
            assert("Given claim_script does not match the given Bitcoin transaction." in e.error["message"])

        # 12 confirms allows in mempool
        parent.generate(1)
        # Should succeed via wallet lookup for address match, and when given
        pegtxid1 = sidechain.claimpegin(raw, proof)

        # Will invalidate the block that confirms this transaction later
        self.sync_all()
        blockhash = sidechain2.generate(1)
        self.sync_all()
        sidechain.generate(5)

        tx1 = sidechain.gettransaction(pegtxid1)

        print('tx1', tx1)
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
            txid = parent.sendtoaddress(addrs["mainchain_address"], 1)
            parent.generate(12)
            proof = parent.gettxoutproof([txid])
            raw = parent.getrawtransaction(txid)
            pegtxs += [sidechain.claimpegin(raw, proof)]

        self.sync_all()
        sidechain2.generate(1)
        for pegtxid in pegtxs:
            tx = sidechain.gettransaction(pegtxid)
            if "confirmations" not in tx or tx["confirmations"] == 0:
                raise Exception("Peg-in confirmation has failed.")

        print("Test pegout")
        self.test_pegout(get_new_unconfidential_address(parent), sidechain)

        print("Test pegout P2SH")
        parent_chain_addr = get_new_unconfidential_address(parent)
        parent_pubkey = parent.validateaddress(parent_chain_addr)["pubkey"]
        parent_chain_p2sh_addr = parent.createmultisig(1, [parent_pubkey])["address"]
        self.test_pegout(parent_chain_p2sh_addr, sidechain)

        print("Test pegout Garbage")
        parent_chain_addr = "garbage"
        try:
            self.test_pegout(parent_chain_addr, sidechain)
            raise Exception("A garbage address should fail.")
        except JSONRPCException as e:
            assert("Invalid Bitcoin address" in e.error["message"])

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
        stop_node(self.nodes[1], 1)
        txid = parent.sendtoaddress(addr, 1)
        parent.generate(12)
        proof = parent.gettxoutproof([txid])
        raw = parent.getrawtransaction(txid)
        stuck_peg = sidechain.claimpegin(raw, proof)
        sidechain.generate(1)
        print("Waiting to ensure block is being rejected by sidechain2")
        time.sleep(5)

        assert(sidechain.getblockcount() != sidechain2.getblockcount())

        print("Restarting parent2")
        self.nodes[1] = start_node(1, self.options.tmpdir, self.extra_args[1], binary=self.binary, chain=self.parent_chain, cookie_auth=True)
        parent2 = self.nodes[1]
        connect_nodes_bi(self.nodes, 0, 1)

        # Don't make a block, race condition when pegin-invalid block
        # is awaiting further validation, nodes reject subsequent blocks
        # even ones they create
        print("Now waiting for node to re-evaluate peg-in witness failed block... should take a few seconds")
        self.sync_all()
        print("Completed!\n")
        print("Now send funds out in two stages, partial, and full")
        some_btc_addr = get_new_unconfidential_address(parent)
        bal_1 = sidechain.getwalletinfo()["balance"]["bitcoin"]
        try:
            sidechain.sendtomainchain(some_btc_addr, bal_1 + 1)
            raise Exception("Sending out too much; should have failed")
        except JSONRPCException as e:
            assert("Insufficient funds" in e.error["message"])

        assert(sidechain.getwalletinfo()["balance"]["bitcoin"] == bal_1)
        try:
            sidechain.sendtomainchain(some_btc_addr+"b", bal_1 - 1)
            raise Exception("Sending to invalid address; should have failed")
        except JSONRPCException as e:
            assert("Invalid Bitcoin address" in e.error["message"])

        assert(sidechain.getwalletinfo()["balance"]["bitcoin"] == bal_1)
        try:
            sidechain.sendtomainchain("1Nro9WkpaKm9axmcfPVp79dAJU1Gx7VmMZ", bal_1 - 1)
            raise Exception("Sending to mainchain address when should have been testnet; should have failed")
        except JSONRPCException as e:
            assert("Invalid Bitcoin address" in e.error["message"])

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

        print('Success!')

if __name__ == '__main__':
    FedPegTest().main()
