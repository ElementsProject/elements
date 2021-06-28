#!/usr/bin/env python3
# Copyright (c) 2016 The Bitcoin Core developers
# Distributed under the MIT/X11 software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import assert_equal, assert_raises_rpc_error, Decimal, assert_greater_than

'''
    This test focuses on enforcement of PAK, not on transitioning lists
    or RPC return values for PAK enforcement settings which is covered
    in feature_dynafed.py

    TODO: Test non-activated dynafed means no block enforcement of PAK
'''

class PAKTest (BitcoinTestFramework):

    def set_test_params(self):
        self.num_nodes = 3
        self.setup_clean_chain = True
        self.extra_args = [["-enforce_pak=1", "-con_dyna_deploy_start=-1", "-initialfreecoins=210000000000000", "-anyonecanspendaremine=1", "-parent_bech32_hrp=lol", "-pubkeyprefix=112", "-scriptprefix=197", "-con_connect_genesis_outputs=1"] for i in range(self.num_nodes)]
        # First node doesn't enforce PAK, a "HF" of the other two nodes
        self.extra_args[0] = ["-acceptnonstdtxn=1"] + self.extra_args[0][1:]   ## FIXME -acceptnonstdtxn=1 should not be needed

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def run_test(self):

        # Transitioning PAK lists and checking lists in RPC tested in feature_dynafed

        self.log.info("Test wallet PAK")

        # We will re-use the same xpub, but each wallet will create its own online pak
        # so the lists will be incompatible, even if all else was synced
        xpub = "tpubD6NzVbkrYhZ4WaWSyoBvQwbpLkojyoTZPRsgXELWz3Popb3qkjcJyJUGLnL4qHHoQvao8ESaAstxYSnhyswJ76uZPStJRJCTKvosUCJZL5B"
        xpub_desc = "pkh("+xpub+"/0/*)" # Transform this into a descriptor
        init_results = []
        info_results = []
        for i in range(self.num_nodes):
            if i == 0:
                assert_raises_rpc_error(-8, "PAK enforcement is not enabled on this network.", self.nodes[i].initpegoutwallet, xpub)
                init_results += [None]
                info_results += [None]
                continue

            init_results += [ self.nodes[i].initpegoutwallet(xpub) ]
            info_results += [ self.nodes[i].getwalletpakinfo() ]
            assert_equal(init_results[i]["address_lookahead"], info_results[i]["address_lookahead"])
            assert_equal(init_results[i]["liquid_pak"], info_results[i]["liquid_pak"])
            assert_equal(init_results[i]["liquid_pak_address"], info_results[i]["liquid_pak_address"])
            assert_equal(info_results[i]["bitcoin_descriptor"], xpub_desc)
            assert_equal(info_results[i]["bip32_counter"], "0")
            validata = self.nodes[i].validateaddress(init_results[i]["address_lookahead"][0])
            assert not validata["isvalid"]
            assert validata["isvalid_parent"]
            assert not validata["parent_address_info"]["isscript"]
            assert not validata["parent_address_info"]["iswitness"]

        # Use custom derivation counter values, check if stored correctly,
        # address lookahead looks correct and that new liquid_pak was chosen
        assert_raises_rpc_error(-8, "bip32_counter must be between 0 and 1,000,000,000, inclusive.", self.nodes[1].initpegoutwallet, xpub, -1)

        assert_raises_rpc_error(-8, "bip32_counter must be between 0 and 1,000,000,000, inclusive.", self.nodes[1].initpegoutwallet, xpub, 1000000001)

        # Make sure we can also prepend the key origin to the xpub.
        self.nodes[1].initpegoutwallet("pkh([deadbeef/44h/0h/0h]"+xpub+"/0/*)")
        new_init = self.nodes[1].initpegoutwallet(xpub, 2)
        assert_equal(self.nodes[1].getwalletpakinfo()["bip32_counter"], "2")
        assert_equal(new_init["address_lookahead"][0], init_results[1]["address_lookahead"][2])
        assert(new_init["liquid_pak"] != init_results[1]["liquid_pak"])

        # Restart and connect peers to check wallet persistence
        self.stop_nodes()
        self.start_nodes()
        self.connect_nodes(0,1)
        self.connect_nodes(1,2)

        # Check PAK settings persistence in wallet across restart
        restarted_info = self.nodes[1].getwalletpakinfo()
        assert_equal(restarted_info["bitcoin_descriptor"], xpub_desc)
        assert_equal(restarted_info["liquid_pak"], new_init["liquid_pak"])
        assert_equal(restarted_info["bip32_counter"], "2")

        # Compile list of extension space entries for pak enforcement
        extension_space_proposal = []
        for entry in init_results:
            if entry is not None:
                pakentry = entry["pakentry"]
                extension_space_proposal += [pakentry[4:4+66]+pakentry[4+66+1:]]

        self.log.info("Test mempool enforcement of PAK peg-outs")

        # Transition to a pak list that only node 1 can peg-out to
        WSH_OP_TRUE = self.nodes[0].decodescript("51")["segwit"]["hex"]
        for _ in range(9):
            block = self.nodes[1].getnewblockhex(0, {"signblockscript":WSH_OP_TRUE, "max_block_witness":3, "fedpegscript":"51", "extension_space":[extension_space_proposal[0]]})
            assert_equal(self.nodes[1].submitblock(block), None)

        self.sync_all()
        assert_equal(self.nodes[0].getblockchaininfo()["extension_space"], [extension_space_proposal[0]])

        # node 1 has wrong pak entry in wallet
        assert_raises_rpc_error(-4, "Given online key is not in Pegout Authorization Key List", self.nodes[1].sendtomainchain, "", 1)

        # put back init_info version that's in pak list
        self.nodes[1].initpegoutwallet(xpub, 0, init_results[1]["liquid_pak"])

        # Node 1 will now make a PAK peg-out, accepted in all mempools and blocks
        pegout_info = self.nodes[1].sendtomainchain("", 1)
        print(pegout_info)
        raw_node1_pegout = self.nodes[1].gettransaction(pegout_info["txid"])["hex"]
        self.sync_all() # mempool sync
        self.nodes[1].generatetoaddress(1, self.nodes[0].getnewaddress())
        self.sync_all() # block sync
        assert_greater_than(self.nodes[1].gettransaction(pegout_info["txid"])["confirmations"], 0)

        # Re-org keep node 1 peg-out unconfirmed and transition to "full list"
        # then check peg-out fails

        # Invalidate back to block 1, then make 9 new blocks to hit transition
        # If you roll back to genesis block p2p code gets flakey
        num_block_rollback = self.nodes[1].getblockcount()-2
        fork_hash = self.nodes[1].getblockhash(2)
        for i in range(self.num_nodes):
           self.nodes[i].invalidateblock(fork_hash)
        self.sync_blocks()

        for _ in range(num_block_rollback):
            block = self.nodes[1].getnewblockhex(0, {"signblockscript":WSH_OP_TRUE, "max_block_witness":3, "fedpegscript":"51", "extension_space":extension_space_proposal})
            self.nodes[1].submitblock(block)

        self.sync_blocks()

        # node 0 puts the peg-out back in its mempool, can't sync all
        self.nodes[0].sendrawtransaction(raw_node1_pegout)
        self.sync_mempools(self.nodes[1:])

        # rejected in mempool
        assert_raises_rpc_error(-26, "invalid-pegout-proof", self.nodes[1].sendrawtransaction, raw_node1_pegout)
        assert_raises_rpc_error(-26, "invalid-pegout-proof", self.nodes[2].sendrawtransaction, raw_node1_pegout)
        # node 0 tries to make bad block
        wrong_pak_prop = self.nodes[0].getnewblockhex()
        # rejected in blocks
        assert_raises_rpc_error(-25, "bad-pak-tx", self.nodes[1].testproposedblock, wrong_pak_prop, True)
        assert_raises_rpc_error(-25, "bad-pak-tx", self.nodes[2].testproposedblock, wrong_pak_prop, True)

        self.log.info("Test various RPC arguments")

        # Fail to peg-out too-small value
        assert_raises_rpc_error(-8, "Invalid amount for send, must send more than 0.00100000 BTC", self.nodes[1].sendtomainchain, "", Decimal('0.0009'))

        # Use wrong network's extended pubkey
        mainnetxpub = "xpub6AATBi58516uxLogbuaG3jkom7x1qyDoZzMN2AePBuQnMFKUV9xC2BW9vXsFJ9rELsvbeGQcFWhtbyM4qDeijM22u3AaSiSYEvuMZkJqtLn"
        assert_raises_rpc_error(-8, "%s is not a valid descriptor function" % mainnetxpub, self.nodes[1].initpegoutwallet, mainnetxpub)

        # Test fixed online pubkey
        init_info = self.nodes[1].initpegoutwallet(xpub)
        init_info2 = self.nodes[1].initpegoutwallet(xpub, 0, init_info['liquid_pak'])
        assert_equal(init_info, init_info2)
        init_info3 = self.nodes[1].initpegoutwallet(xpub)
        assert init_info != init_info3

        # Test Descriptor PAK Support

        # Non-supported descriptors
        assert_raises_rpc_error(-8, "bitcoin_descriptor is not of any type supported: pkh(<xpub>), sh(wpkh(<xpub>)), wpkh(<xpub>), or <xpub>.", self.nodes[1].initpegoutwallet, "pk(tpubD6NzVbkrYhZ4WaWSyoBvQwbpLkojyoTZPRsgXELWz3Popb3qkjcJyJUGLnL4qHHoQvao8ESaAstxYSnhyswJ76uZPStJRJCTKvosUCJZL5B/0/*)")

        assert_raises_rpc_error(-8, "bitcoin_descriptor must be a ranged descriptor.", self.nodes[1].initpegoutwallet, "pkh(tpubD6NzVbkrYhZ4WaWSyoBvQwbpLkojyoTZPRsgXELWz3Popb3qkjcJyJUGLnL4qHHoQvao8ESaAstxYSnhyswJ76uZPStJRJCTKvosUCJZL5B)")

        # Peg out with each new type, check that destination script matches
        wpkh_desc = "wpkh("+xpub+"/0/*)"
        # add a valid checksum
        wpkh_desc = self.nodes[1].getdescriptorinfo(wpkh_desc)["descriptor"]
        wpkh_info = self.nodes[1].initpegoutwallet(wpkh_desc)
        wpkh_pak_info = self.nodes[1].getwalletpakinfo()

        # Transition to wpkh entry list
        wpkh_pak_entry = wpkh_info["pakentry"]
        wpkh_pak_prop = [wpkh_pak_entry[4:4+66]+wpkh_pak_entry[4+66+1:]]
        for _ in range(10):
            block = self.nodes[1].getnewblockhex(0, {"signblockscript":WSH_OP_TRUE, "max_block_witness":3, "fedpegscript":"51", "extension_space":wpkh_pak_prop})
            self.nodes[1].submitblock(block)
        self.sync_blocks()

        # Get some block subsidy and send off
        self.nodes[1].generatetoaddress(101, self.nodes[1].getnewaddress())
        wpkh_stmc = self.nodes[1].sendtomainchain("", 1)
        wpkh_txid = wpkh_stmc['txid']

        # Also check some basic return fields of sendtomainchain with pak
        assert_equal(wpkh_stmc["bitcoin_address"], wpkh_info["address_lookahead"][0])
        validata = self.nodes[1].validateaddress(wpkh_stmc["bitcoin_address"])
        assert not validata["isvalid"]
        assert validata["isvalid_parent"]
        assert not validata["parent_address_info"]["isscript"]
        assert validata["parent_address_info"]["iswitness"]
        assert_equal(wpkh_pak_info["bip32_counter"], wpkh_stmc["bip32_counter"])
        assert_equal(wpkh_pak_info["bitcoin_descriptor"], wpkh_stmc["bitcoin_descriptor"])

        sh_wpkh_desc = "sh(wpkh("+xpub+"/0/1/*))"
        sh_wpkh_info = self.nodes[1].initpegoutwallet(sh_wpkh_desc)

        validata = self.nodes[1].validateaddress(sh_wpkh_info["address_lookahead"][0])
        assert not validata["isvalid"]
        assert validata["isvalid_parent"]
        assert validata["parent_address_info"]["isscript"]
        assert not validata["parent_address_info"]["iswitness"]

        # Transition to sh_wpkh entry list
        sh_wpkh_pak_entry = sh_wpkh_info["pakentry"]
        sh_wpkh_pak_prop = [sh_wpkh_pak_entry[4:4+66]+sh_wpkh_pak_entry[4+66+1:]]
        for _ in range(10):
            block = self.nodes[1].getnewblockhex(0, {"signblockscript":WSH_OP_TRUE, "max_block_witness":3, "fedpegscript":"51", "extension_space":sh_wpkh_pak_prop})
            self.nodes[1].submitblock(block)
        self.sync_blocks()

        self.nodes[1].generatetoaddress(1, self.nodes[1].getnewaddress())
        sh_wpkh_txid = self.nodes[1].sendtomainchain("", 1)['txid']

        # Make sure peg-outs look correct
        wpkh_raw = self.nodes[1].decoderawtransaction(self.nodes[1].gettransaction(wpkh_txid)['hex'])
        sh_wpkh_raw = self.nodes[1].decoderawtransaction(self.nodes[1].gettransaction(sh_wpkh_txid)['hex'])

        peg_out_found = False
        for output in wpkh_raw["vout"]:
            print(output)
            if "pegout_address" in output["scriptPubKey"]:
                if output["scriptPubKey"]["pegout_address"] == wpkh_info["address_lookahead"][0]:
                    peg_out_found = True
                    break
                else:
                    raise Exception("Found unexpected peg-out output")
        assert peg_out_found

        peg_out_found = False
        for output in sh_wpkh_raw["vout"]:
            if "pegout_address" in output["scriptPubKey"]:
                if output["scriptPubKey"]["pegout_address"] == sh_wpkh_info["address_lookahead"][0]:
                    peg_out_found = True
                    break
                else:
                    raise Exception("Found unexpected peg-out output")
        assert peg_out_found

        # Make sure they all confirm
        self.nodes[1].generatetoaddress(1, self.nodes[0].getnewaddress())
        for tx_id in [wpkh_txid, sh_wpkh_txid]:
            assert_greater_than(self.nodes[1].gettransaction(tx_id)["confirmations"], 0)

        self.log.info("Test that pak-less pegouts are rejected")

        # Last test of a pak-less peg-out failing to get into mempool/block
        # Note it leaves a transaction in node 0's mempool, so sync_all cannot
        # work after unless it's somehow booted.

        # node 0 will now create a pegout, will fail to enter mempool of node 1 or 2
        # since it's pak-less
        nopak_pegout_txid = self.nodes[0].sendtomainchain("n3NkSZqoPMCQN5FENxUBw4qVATbytH6FDK", 1)
        raw_pakless_pegout = self.nodes[0].gettransaction(nopak_pegout_txid)["hex"]
        assert nopak_pegout_txid in self.nodes[0].getrawmempool()

        assert_raises_rpc_error(-26, "invalid-pegout-proof", self.nodes[1].sendrawtransaction, raw_pakless_pegout)
        assert_raises_rpc_error(-26, "invalid-pegout-proof", self.nodes[2].sendrawtransaction, raw_pakless_pegout)

        # node 0 makes a block that includes the pakless pegout, rejected by others
        # by consensus
        bad_prop = self.nodes[0].getnewblockhex()
        assert_raises_rpc_error(-25, "bad-pak-tx", self.nodes[1].testproposedblock, bad_prop, True)
        assert_raises_rpc_error(-25, "bad-pak-tx", self.nodes[2].testproposedblock, bad_prop, True)

        # Test that subtracting fee from output works
        self.nodes[1].generatetoaddress(101, self.nodes[1].getnewaddress())
        self.nodes[1].sendtomainchain("", self.nodes[1].getbalance()["bitcoin"], True)
        assert_equal(self.nodes[1].getbalance()["bitcoin"], 0)

        # TODO: create rawsendtomainchain to do transaction surgery for testing

if __name__ == '__main__':
    PAKTest ().main ()
