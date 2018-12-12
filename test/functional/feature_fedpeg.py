#!/usr/bin/env python3

import time

from test_framework.authproxy import JSONRPCException
from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import (
    connect_nodes_bi,
    get_auth_cookie,
    get_datadir_path,
    rpc_port,
    p2p_port,
)

def get_new_unconfidential_address(node):
    addr = node.getnewaddress()
    val_addr = node.getaddressinfo(addr)
    if 'unconfidential' in val_addr:
        return val_addr['unconfidential']
    return val_addr['address']

class FedPegTest(BitcoinTestFramework):

    def set_test_params(self):
        self.setup_clean_chain = True
        self.num_nodes = 4

    def add_options(self, parser):
        parser.add_argument("--parent_binpath", dest="parent_binpath", default="",
                            help="Use a different binary for launching nodes")
        parser.add_argument("--parent_bitcoin", dest="parent_bitcoin", default=False, action="store_true",
                            help="Parent nodes are Bitcoin")

    def setup_network(self, split=False):
        if self.options.parent_bitcoin and self.options.parent_binpath == "":
            raise Exception("Can't run with --parent_bitcoin without specifying --parent_binpath")

        self.nodes = []
        # Setup parent nodes
        parent_chain = "regtest" if self.options.parent_bitcoin else "parent"
        parent_binary = [self.options.parent_binpath] if self.options.parent_binpath != "" else None
        for n in range(2):
            extra_args = [
                "-printtoconsole=0",
                "-port="+str(p2p_port(n)),
                "-rpcport="+str(rpc_port(n))
            ]
            if self.options.parent_bitcoin:
                extra_args.extend([
                    "-addresstype=legacy", # To make sure bitcoind gives back p2pkh no matter version
                ])
            else:
                extra_args.extend([
                    "-validatepegin=0",
                    "-initialfreecoins=2100000000000000",
                    "-anyonecanspendaremine",
                    "-signblockscript=51", # OP_TRUE
                ])

            self.add_nodes(1, [extra_args], chain=[parent_chain], binary=parent_binary)
            self.start_node(n)
            print("Node {} started".format(n))

        connect_nodes_bi(self.nodes, 0, 1)
        self.parentgenesisblockhash = self.nodes[0].getblockhash(0)
        print('parentgenesisblockhash', self.parentgenesisblockhash)
        #TODO(rebase) CA
        #if not self.options.parent_bitcoin:
        #    parent_pegged_asset = self.nodes[0].getsidechaininfo()['pegged_asset']

        # Setup sidechain nodes
        self.fedpeg_script = "512103dff4923d778550cc13ce0d887d737553b4b58f4e8e886507fc39f5e447b2186451ae"
        for n in range(2):
            extra_args = [
                "-printtoconsole=0",
                "-port="+str(p2p_port(2+n)),
                "-rpcport="+str(rpc_port(2+n)),
                '-parentgenesisblockhash=%s' % self.parentgenesisblockhash,
                '-validatepegin=1',
                '-fedpegscript=%s' % self.fedpeg_script,
                '-anyonecanspendaremine=0',
                '-minrelaytxfee=0',
                '-blockmintxfee=0',
                '-initialfreecoins=0',
                '-peginconfirmationdepth=10',
                '-mainchainrpchost=127.0.0.1',
                '-mainchainrpcport=%s' % rpc_port(n),
                '-recheckpeginblockinterval=15', # Long enough to allow failure and repair before timeout
            ]
            if not self.options.parent_bitcoin:
                extra_args.extend([
                    #TODO(rebase) should the defaults be put back to elements-specific ones?
                    #'-parentpubkeyprefix=235',
                    #'-parentscriptprefix=75',
                    '-parentpubkeyprefix=111',
                    '-parentscriptprefix=196',
                    '-con_parent_chain_signblockscript=51',
                    #TODO(rebase) CA
                    #'-con_parent_pegged_asset=%s' % parent_pegged_asset,
                ])

            # Use rpcuser auth only for first parent.
            if n==0:
                # Extract username and password from cookie file and use directly.
                datadir = get_datadir_path(self.options.tmpdir, n)
                rpc_u, rpc_p = get_auth_cookie(datadir, parent_chain)
                extra_args.extend([
                    '-mainchainrpcuser=%s' % rpc_u,
                    '-mainchainrpcpassword=%s' % rpc_p,
                ])
            else:
                # Need to specify where to find parent cookie file
                datadir = get_datadir_path(self.options.tmpdir, n)
                extra_args.append('-mainchainrpccookiefile='+datadir+"/" + parent_chain + "/.cookie")

            self.add_nodes(1, [extra_args], chain=["sidechain"])
            self.start_node(2+n)
            print("Node {} started".format(2+n))

        # We only connect the same-chain nodes, so sync_all works correctly
        connect_nodes_bi(self.nodes, 2, 3)
        self.node_groups = [[self.nodes[0], self.nodes[1]], [self.nodes[2], self.nodes[3]]]
        self.sync_all(self.node_groups)
        print("Setting up network done")

    def test_pegout(self, parent_chain_addr, sidechain):
        pegout_txid = sidechain.sendtomainchain(parent_chain_addr, 1)
        raw_pegout = sidechain.getrawtransaction(pegout_txid, True)
        assert 'vout' in raw_pegout and len(raw_pegout['vout']) > 0
        pegout_tested = False
        for output in raw_pegout['vout']:
            scriptPubKey = output['scriptPubKey']
            if 'type' in scriptPubKey and scriptPubKey['type'] == 'nulldata':
                assert ('pegout_hex' in scriptPubKey and 'pegout_asm' in scriptPubKey and 'pegout_type' in scriptPubKey)
                assert ('pegout_chain' in scriptPubKey and 'pegout_reqSigs' in scriptPubKey and 'pegout_addresses' in scriptPubKey)
                assert scriptPubKey['pegout_chain'] == self.parentgenesisblockhash
                assert scriptPubKey['pegout_reqSigs'] == 1
                assert parent_chain_addr in scriptPubKey['pegout_addresses']
                pegout_tested = True
                break
        assert pegout_tested

    def run_test(self):
        parent = self.nodes[0]
        #parent2 = self.nodes[1]
        sidechain = self.nodes[2]
        sidechain2 = self.nodes[3]

        parent.generate(101)
        sidechain.generate(101)

        addrs = sidechain.getpeginaddress()
        addr = addrs["mainchain_address"]
        print('addrs', addrs)
        print(parent.getaddressinfo(addr))
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
            scriptpubkey = sidechain.getaddressinfo(get_new_unconfidential_address(sidechain))["scriptPubKey"]
            pegtxid = sidechain.claimpegin(raw, proof, scriptpubkey)
            raise Exception("Peg-in with non-matching claim_script should fail.")
        except JSONRPCException as e:
            print('RPC ERROR:', e.error['message'])
            assert("Given claim_script does not match the given Bitcoin transaction." in e.error["message"])

        # 12 confirms allows in mempool
        parent.generate(1)
        # Should succeed via wallet lookup for address match, and when given
        raw_pegin = sidechain.createrawpegin(raw, proof)['hex']
        signed_pegin = sidechain.signrawtransactionwithwallet(raw_pegin)

        pegtxid1 = sidechain.claimpegin(raw, proof)

        # Will invalidate the block that confirms this transaction later
        self.sync_all(self.node_groups)
        blockhash = sidechain2.generate(1)
        self.sync_all(self.node_groups)
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
        #TODO(rebase) CT assert fee here too
        # Check that there's sufficient fee for the peg-in
        #vsize = decoded["vsize"]
        #fee_output = decoded["vout"][1]
        #fallbackfee_pervbyte = Decimal("0.00001")/Decimal("1000")
        #print("fee_output", fee_output)
        #assert fee_output["scriptPubKey"]["type"] == "fee"
        #assert fee_output["value"] >= fallbackfee_pervbyte*vsize

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

        # Do multiple claims in mempool
        n_claims = 6

        print("Flooding mempool with many small claims")
        pegtxs = []
        sidechain.generate(101)

        # Do mixture of raw peg-in and automatic peg-in tx construction
        # where raw creation is done on another node
        for i in range(n_claims):
            addrs = sidechain.getpeginaddress()
            txid = parent.sendtoaddress(addrs["mainchain_address"], 1)
            parent.generate(1)
            proof = parent.gettxoutproof([txid])
            raw = parent.getrawtransaction(txid)
            if i % 2 == 0:
                parent.generate(11)
                pegtxs += [sidechain.claimpegin(raw, proof)]
            else:
                # The raw API doesn't check for the additional 2 confirmation buffer
                # So we only get 10 confirms then send off. Miners will add to block anyways.

                # Don't mature whole way yet to test signing immature peg-in input
                parent.generate(8)
                # Wallet in sidechain2 gets funds instead of sidechain
                raw_pegin = sidechain2.createrawpegin(raw, proof, addrs["claim_script"])["hex"]
                # First node should also be able to make a valid transaction with or without 3rd arg
                # since this wallet originated the claim_script itself
                sidechain.createrawpegin(raw, proof, addrs["claim_script"])
                sidechain.createrawpegin(raw, proof)
                signed_pegin = sidechain.signrawtransactionwithwallet(raw_pegin)
                assert(signed_pegin["complete"])
                assert("warning" in signed_pegin) # warning for immature peg-in
                # fully mature them now
                parent.generate(1)
                pegtxs += [sidechain.sendrawtransaction(signed_pegin["hex"])]

        self.sync_all(self.node_groups)
        sidechain2.generate(1)
        for i, pegtxid in enumerate(pegtxs):
            if i % 2 == 0:
                tx = sidechain.gettransaction(pegtxid)
            else:
                tx = sidechain2.gettransaction(pegtxid)
            if "confirmations" not in tx or tx["confirmations"] == 0:
                raise Exception("Peg-in confirmation has failed.")

        print("Test pegout")
        self.test_pegout(get_new_unconfidential_address(parent), sidechain)

        print("Test pegout P2SH")
        parent_chain_addr = get_new_unconfidential_address(parent)
        parent_pubkey = parent.getaddressinfo(parent_chain_addr)["pubkey"]
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
                assert ('pegout_hex' in scriptPubKey and 'pegout_asm' in scriptPubKey and 'pegout_type' in scriptPubKey)
                assert ('pegout_chain' in scriptPubKey and 'pegout_reqSigs' not in scriptPubKey and 'pegout_addresses' not in scriptPubKey)
                assert scriptPubKey['pegout_type'] == 'nonstandard'
                assert scriptPubKey['pegout_chain'] == pegout_chain
                assert scriptPubKey['pegout_hex'] == pegout_hex
                pegout_tested = True
                break
        assert pegout_tested

        print ("Now test failure to validate peg-ins based on intermittant bitcoind rpc failure")
        self.stop_node(1)
        txid = parent.sendtoaddress(addr, 1)
        parent.generate(12)
        proof = parent.gettxoutproof([txid])
        raw = parent.getrawtransaction(txid)
        sidechain.claimpegin(raw, proof) # stuck peg
        sidechain.generate(1)
        print("Waiting to ensure block is being rejected by sidechain2")
        time.sleep(5)

        assert(sidechain.getblockcount() != sidechain2.getblockcount())

        print("Restarting parent2")
        self.start_node(1)
        #parent2 = self.nodes[1]
        connect_nodes_bi(self.nodes, 0, 1)

        # Don't make a block, race condition when pegin-invalid block
        # is awaiting further validation, nodes reject subsequent blocks
        # even ones they create
        print("Now waiting for node to re-evaluate peg-in witness failed block... should take a few seconds")
        self.sync_all(self.node_groups)
        print("Completed!\n")
        print("Now send funds out in two stages, partial, and full")
        some_btc_addr = get_new_unconfidential_address(parent)
        #TODO(rebase) CA bitcoin balances
        #bal_1 = sidechain.getwalletinfo()["balance"]["bitcoin"]
        bal_1 = sidechain.getwalletinfo()["balance"]
        try:
            sidechain.sendtomainchain(some_btc_addr, bal_1 + 1)
            raise Exception("Sending out too much; should have failed")
        except JSONRPCException as e:
            assert("Insufficient funds" in e.error["message"])

        #assert(sidechain.getwalletinfo()["balance"]["bitcoin"] == bal_1)
        assert(sidechain.getwalletinfo()["balance"] == bal_1)
        try:
            sidechain.sendtomainchain(some_btc_addr+"b", bal_1 - 1)
            raise Exception("Sending to invalid address; should have failed")
        except JSONRPCException as e:
            assert("Invalid Bitcoin address" in e.error["message"])

        #assert(sidechain.getwalletinfo()["balance"]["bitcoin"] == bal_1)
        assert(sidechain.getwalletinfo()["balance"] == bal_1)
        try:
            sidechain.sendtomainchain("1Nro9WkpaKm9axmcfPVp79dAJU1Gx7VmMZ", bal_1 - 1)
            raise Exception("Sending to mainchain address when should have been testnet; should have failed")
        except JSONRPCException as e:
            assert("Invalid Bitcoin address" in e.error["message"])

        #assert(sidechain.getwalletinfo()["balance"]["bitcoin"] == bal_1)
        assert(sidechain.getwalletinfo()["balance"] == bal_1)

        peg_out_txid = sidechain.sendtomainchain(some_btc_addr, 1)

        peg_out_details = sidechain.decoderawtransaction(sidechain.getrawtransaction(peg_out_txid))
        # peg-out, change
        #TODO(rebase) CA/CT fee output
        #assert(len(peg_out_details["vout"]) == 3)
        assert(len(peg_out_details["vout"]) == 2)
        found_pegout_value = False
        for output in peg_out_details["vout"]:
            if "value" in output and output["value"] == 1:
                found_pegout_value = True
        assert(found_pegout_value)

        #bal_2 = sidechain.getwalletinfo()["balance"]["bitcoin"]
        bal_2 = sidechain.getwalletinfo()["balance"]
        # Make sure balance went down
        assert(bal_2 + 1 < bal_1)

        sidechain.sendtomainchain(some_btc_addr, bal_2, True)

        #TODO(rebase) CA bitcoin balance
        #assert("bitcoin" not in sidechain.getwalletinfo()["balance"])
        assert(sidechain.getwalletinfo()["balance"] == 0)

        print('Success!')

        # Manually stop sidechains first, then the parent chains.
        self.stop_node(2)
        self.stop_node(3)
        self.stop_node(0)
        self.stop_node(1)

if __name__ == '__main__':
    FedPegTest().main()
