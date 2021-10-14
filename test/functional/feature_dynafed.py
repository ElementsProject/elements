#!/usr/bin/env python3
# Copyright (c) 2019 The Elements Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Test dynamic federations state machine logic

NOTE: This test is not testing the behavior not related to transitions themselves.
That is for other tests such as feature_pak, feature_fedpeg, feature_blocksign

1) Test "legacy" params are still in play before versionbits activation
2) Test transition to dynafed preserves expected chainparams
3) Test a full epoch with no votes
4) Test full epoch with just under 4/5 votes, with competing random proposals
5) Test full epoch with just at 4/5 votes, with competing random proposals
6) Test full epoch with 5/5 votes
7) Test that peg-outs(PAK) and peg-ins are ejected from mempool block before transition
and rejected when re-submitted if there is a parameter mismatch
8) Test that reorging a transition results in transitions being undone,
previously ejected transactions are allowed back into the mempool when appropriate

"""
from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import assert_raises_rpc_error, assert_equal

# Hardcoded PAK that's in chainparams to make sure PAK is enforced even when dynafed is not
initial_online = "02fcba7ecf41bc7e1be4ee122d9d22e3333671eb0a3a87b5cdf099d59874e1940f"
# Random key to make new pak
initial_offline = "03808355deeb0555203b53df7ef8f36edaf66ab0207ca1b11968a7ac421554e621"
initial_extension = [initial_online+initial_online]
new_extension = [initial_offline+initial_online]

ERR_MP_INVALID_PEGOUT = "invalid-pegout-proof"
ERR_MP_INVALID_PEGIN = "pegin-no-witness"

def go_to_epoch_end(node):
    epoch_info = node.getblockchaininfo()
    blocks_to_mine = epoch_info["epoch_length"] - epoch_info["epoch_age"] - 1
    node.generatetoaddress(blocks_to_mine, node.getnewaddress())

def validate_no_vote_op_true(node, block, first_dynafed_active_block):

    block_info = node.getblock(block)
    dynamic_parameters = block_info["dynamic_parameters"]
    block_height = block_info["height"]
    assert "current" in dynamic_parameters
    assert "proposed" in dynamic_parameters
    # signblockscript is now the P2WSH-ification of OP_TRUE
    WSH_OP_TRUE = node.decodescript("51")["segwit"]["hex"]
    assert_equal(dynamic_parameters["current"]["signblockscript"], WSH_OP_TRUE)
    if block_height % 10 == 0 or first_dynafed_active_block:
        assert_equal(dynamic_parameters["current"]["fedpegscript"], "51")
        assert_equal(dynamic_parameters["current"]["extension_space"], initial_extension)
    else:
        assert_equal(dynamic_parameters["current"]["fedpegscript"], "")
        assert_equal(dynamic_parameters["current"]["extension_space"], [])
    assert_equal(dynamic_parameters["current"]["max_block_witness"], 74)
    # nothing was proposed, null fields make impossible to be valid blockheader
    # due to script rules requiring bool true on stack
    assert_equal(dynamic_parameters["proposed"]["signblockscript"], "")
    assert_equal(dynamic_parameters["proposed"]["fedpegscript"], "")
    assert_equal(dynamic_parameters["proposed"]["max_block_witness"], 0)
    assert_equal(dynamic_parameters["proposed"]["extension_space"], [])

class DynaFedTest(BitcoinTestFramework):
    def set_test_params(self):
        self.setup_clean_chain = True
        self.num_nodes = 2
        # We want to test activation of dynafed
        self.extra_args = [[
            "-con_dyna_deploy_start=1000",
            "-enforce_pak=1",
            "-con_parent_chain_signblockscript=51",
            "-peginconfirmationdepth=1",
            "-parentscriptprefix=75",
            "-parent_bech32_hrp=ert",
            "-con_dyna_deploy_signal=1",
        ] for i in range(self.num_nodes)]
        # second node will not mine transactions
        self.extra_args[1].append("-blocksonly=1")
        # Make sure nothing breaks if peers have a different activation.
        self.extra_args[1][0] = "-con_dyna_deploy_start=937"

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def test_legacy_params(self):
        self.log.info("Testing legacy parameters...")
        for i in range(self.num_nodes):
            assert_equal(self.nodes[i].getblockcount(), 0)

            # Check deployment exists and is not active
            dyna_activate = self.nodes[i].getblockchaininfo()["softforks"]["dynafed"]["bip9"]
            assert_equal(dyna_activate["status"], "defined")

            # fedpegscript is OP_TRUE
            legacy_sc_info = self.nodes[i].getsidechaininfo()
            assert_equal(legacy_sc_info["fedpegscript"], "51")
            # No history yet, only one "live" fedpegscript
            assert_equal(legacy_sc_info["current_fedpegscripts"], ["51"])

            # blocksigner is OP_TRUE, extension space is hardcoded one in chainparams
            signblock_info = self.nodes[i].getblockchaininfo()
            assert_equal(signblock_info["signblock_hex"], "51")
            assert_equal(signblock_info["current_signblock_hex"], "51")
            assert_equal(signblock_info["max_block_witness"], 74)
            assert_equal(signblock_info["extension_space"], initial_extension)

            pak_info = self.nodes[i].getpakinfo()
            assert_equal(pak_info["block_paklist"]["reject"], False)
            assert_equal(pak_info["block_paklist"]["online"], [initial_online])
            assert_equal(pak_info["block_paklist"]["offline"], [initial_online])

            # can not put proposed params into blockheader pre-dynafed
            assert_raises_rpc_error(-8, "Dynamic federations is not active on this network. Proposed parameters are not needed.", self.nodes[i].getnewblockhex, 0, {})

        # TODO Reject serialized dynamic federations blocks before activation

    def test_dynafed_activation(self):
        self.log.info("Testing dynafed versionbits activation...")

        # Signaling window is in height, not time, so first block that will signal is
        # at height 1008 which is evenly disible by 144(regtest bip9 window size)
        # Giving funds to node 1 to avoid a transaction size blowup when sweeping later
        blocks = self.nodes[0].generatetoaddress(1006, self.nodes[1].getnewaddress())
        assert_equal(self.nodes[0].getblockchaininfo()["softforks"]["dynafed"]["bip9"]["status"], "defined")
        blocks += self.nodes[0].generatetoaddress(1, self.nodes[0].getnewaddress())
        assert_equal(self.nodes[0].getblockchaininfo()["softforks"]["dynafed"]["bip9"]["status"], "started")
        blocks += self.nodes[0].generatetoaddress(144, self.nodes[0].getnewaddress())
        assert_equal(self.nodes[0].getblockchaininfo()["softforks"]["dynafed"]["bip9"]["status"], "locked_in")

        # Move chain forward to activation, any new blocks will be enforced
        blocks += self.nodes[0].generatetoaddress(144, self.nodes[0].getnewaddress())
        self.sync_blocks(timeout=240)
        assert_equal(self.nodes[0].getblockchaininfo()["softforks"]["dynafed"]["bip9"]["status"], "active")

        # Existing blocks should have null dynafed fields
        for block in blocks:
            assert "dynamic_parameters" not in self.nodes[0].getblock(block)

        # Next block is first dynamic federation block
        block = self.nodes[0].generatetoaddress(1, self.nodes[0].getnewaddress())[0]
        self.sync_all()
        # We publish full block on BIP9 transition
        for i in range(self.num_nodes):
            validate_no_vote_op_true(self.nodes[i], block, True)

    def test_illegal_proposals(self):

        WSH_OP_TRUE = self.nodes[0].decodescript("51")["segwit"]["hex"]
        # fedpegscript proposals starting with OP_DEPTH(0x74) are illegal when witness v0
        assert_raises_rpc_error(-1, "invalid-dyna-fed, Proposed fedpegscript starts with OP_DEPTH, which is illegal", self.nodes[0].getnewblockhex, 0, {"signblockscript":WSH_OP_TRUE, "max_block_witness":100, "fedpegscript":"74", "extension_space":[]})
        # but it's ok to have the opcode elsewhere
        self.nodes[0].getnewblockhex(0, {"signblockscript":WSH_OP_TRUE, "max_block_witness":100, "fedpegscript":"0074", "extension_space":[]})

        # signblockscript proposals must be native segwit scriptpubkeys
        assert_raises_rpc_error(-1, "invalid-dyna-fed, proposed signblockscript must be native segwit scriptPubkey", self.nodes[0].getnewblockhex, 0, {"signblockscript":"51", "max_block_witness":100, "fedpegscript":"51", "extension_space":[]})
        assert_raises_rpc_error(-1, "invalid-dyna-fed, proposed signblockscript must be native segwit scriptPubkey", self.nodes[0].getnewblockhex, 0, {"signblockscript":"00"+WSH_OP_TRUE, "max_block_witness":100, "fedpegscript":"51", "extension_space":[]})

        # Since we're enforcing PAK, extension space entries *must* be 66 bytes
        # each 33 of which are serialized compressed pubkeys
        assert_raises_rpc_error(-1, "invalid-dyna-fed, Extension space is not list of valid PAK entries", self.nodes[0].getnewblockhex, 0, {"signblockscript":WSH_OP_TRUE, "max_block_witness":100, "fedpegscript":"51", "extension_space":["00"]})
        assert_raises_rpc_error(-1, "invalid-dyna-fed, Extension space is not list of valid PAK entries", self.nodes[0].getnewblockhex, 0, {"signblockscript":WSH_OP_TRUE, "max_block_witness":100, "fedpegscript":"51", "extension_space":["", initial_extension[0]]})

    def test_no_vote(self):
        self.log.info("Testing no-vote epoch...")
        go_to_epoch_end(self.nodes[0])

        # Mine epoch_length blocks with no proposals
        blocks = self.nodes[0].generatetoaddress(10, self.nodes[0].getnewaddress())
        self.sync_all()

        for i in range(self.num_nodes):
            for block in blocks:
                validate_no_vote_op_true(self.nodes[i], block, False)

        # Now transition using vanilla getnewblockhex, nothing changed
        block = self.nodes[0].generatetoaddress(1, self.nodes[0].getnewaddress())[0]
        self.sync_all()

        for i in range(self.num_nodes):
            validate_no_vote_op_true(self.nodes[i], block, False)

    def test_under_vote(self):
        self.log.info("Testing failed voting epoch...")
        go_to_epoch_end(self.nodes[0])

        # Mine 7 blocks with agreeing proposals for single-sig, falls short of 4/5 of 10
        new_signblock = self.nodes[0].getaddressinfo(self.nodes[0].getnewaddress("", "bech32"))["scriptPubKey"]
        cur_height = self.nodes[0].getblockcount()
        for _ in range(7):
            prop_block = self.nodes[0].getnewblockhex(0, {"signblockscript":new_signblock, "max_block_witness":100, "fedpegscript":"52", "extension_space":new_extension})
            self.nodes[0].submitblock(prop_block)
        self.sync_all()
        assert_equal(self.nodes[0].getblockcount(), cur_height+7)
        # Now mine 3 blank blocks
        self.nodes[0].generatetoaddress(3, self.nodes[0].getnewaddress())
        # No transition will take place, generatetoaddress still works for new epoch
        block = self.nodes[0].generatetoaddress(1, self.nodes[0].getnewaddress())[0]
        self.sync_all()

        for i in range(self.num_nodes):
            validate_no_vote_op_true(self.nodes[i], block, False)

    def test_four_fifth_vote(self):
        self.log.info("Testing just-successful transition epoch...")
        go_to_epoch_end(self.nodes[0])

        # Mine 8 blocks with agreeing proposals for single-sig, triggering transition
        new_signblock = self.nodes[0].getaddressinfo(self.nodes[0].getnewaddress("", "bech32"))["scriptPubKey"]
        cur_height = self.nodes[0].getblockcount()
        WSH_OP_TRUE = self.nodes[0].decodescript("51")["segwit"]["hex"]
        for _ in range(8):
            # Check that things don't change until the 10th block is submitted
            for i in range(self.num_nodes):
                chain_info = self.nodes[i].getblockchaininfo()
                fedpeg_info = self.nodes[i].getsidechaininfo()
                assert_equal(chain_info["current_signblock_hex"], WSH_OP_TRUE)
                assert_equal(chain_info["max_block_witness"], 74)
                assert_equal(chain_info["extension_space"], initial_extension)
                assert_equal(fedpeg_info["current_fedpegscripts"], ["51", "51"])

            prop_block = self.nodes[0].getnewblockhex(0, {"signblockscript":new_signblock, "max_block_witness":107, "fedpegscript":"52", "extension_space":new_extension})
            self.nodes[0].submitblock(prop_block)
        self.sync_all()
        assert_equal(self.nodes[0].getblockcount(), cur_height+8)

        # Now mine 1 blank block
        self.nodes[0].generatetoaddress(1, self.nodes[0].getnewaddress())
        self.sync_all()

        # Old parameters still enforced for next block...
        for i in range(self.num_nodes):
            chain_info = self.nodes[i].getblockchaininfo()
            fedpeg_info = self.nodes[i].getsidechaininfo()
            assert_equal(chain_info["current_signblock_hex"], WSH_OP_TRUE)
            assert_equal(chain_info["max_block_witness"], 74)
            assert_equal(chain_info["extension_space"], initial_extension)
            assert_equal(fedpeg_info["current_fedpegscripts"], ["51", "51"])

        # Last blank block
        self.nodes[0].generatetoaddress(1, self.nodes[0].getnewaddress())
        self.sync_all()

        # We have now transitioned, next block must have signature
        unsigned_block = self.nodes[0].getnewblockhex()
        assert_equal(self.nodes[0].submitblock(unsigned_block), "block-proof-invalid")
        assert_equal(self.nodes[0].getblockcount(), cur_height+10)

        # New params now enforced
        for i in range(self.num_nodes):
            chain_info = self.nodes[i].getblockchaininfo()
            fedpeg_info = self.nodes[i].getsidechaininfo()
            assert_equal(chain_info["current_signblock_hex"], new_signblock)
            assert_equal(chain_info["max_block_witness"], 107) # 72+33+2
            assert_equal(chain_info["extension_space"], new_extension)
            assert_equal(fedpeg_info["current_fedpegscripts"], ["52", "51"])

    def test_all_vote(self):
        self.log.info("Testing unanimous transition epoch...")
        # We have now transitioned to single-sig blocks from node 0
        # Let's transition node 1's key with all votes to it

        cur_height = self.nodes[0].getblockcount()

        new_signblock = self.nodes[1].getaddressinfo(self.nodes[1].getnewaddress("", "bech32"))["scriptPubKey"]
        for _ in range(10):
            # Check that things don't change until the 10th block is submitted
            for i in range(self.num_nodes):
                chain_info = self.nodes[i].getblockchaininfo()
                fedpeg_info = self.nodes[i].getsidechaininfo()
                assert chain_info["current_signblock_hex"] != new_signblock
                assert_equal(chain_info["max_block_witness"], 107)
                assert_equal(chain_info["extension_space"], new_extension)
                assert_equal(fedpeg_info["current_fedpegscripts"], ["52", "51"])

            block = self.nodes[1].getnewblockhex(0, {"signblockscript":new_signblock, "max_block_witness":108, "fedpegscript":"53", "extension_space":new_extension})
            sig = self.nodes[0].signblock(block, "")

            assert_raises_rpc_error(-25, "Could not sign the block.", self.nodes[1].signblock, block, "")
            comb_result = self.nodes[0].combineblocksigs(block, sig, "")
            assert comb_result["complete"]
            self.nodes[1].submitblock(comb_result["hex"])
            self.sync_all()

        self.sync_all()
        assert_equal(self.nodes[0].getblockcount(), cur_height+10)

        chain_info = self.nodes[0].getblockchaininfo()
        fedpeg_info = self.nodes[0].getsidechaininfo()
        assert_equal(chain_info["current_signblock_hex"], new_signblock)
        assert_equal(chain_info["max_block_witness"], 108)
        assert_equal(chain_info["extension_space"], new_extension)
        assert_equal(fedpeg_info["current_fedpegscripts"], ["53", "52"])

        # Now node 1 is the signer
        block = self.nodes[0].getnewblockhex()
        sig = self.nodes[1].signblock(block, "")
        assert_raises_rpc_error(-25, "Could not sign the block.", self.nodes[0].signblock, block, "")
        comb_result = self.nodes[1].combineblocksigs(block, sig, "")
        assert comb_result["complete"]
        self.nodes[0].submitblock(comb_result["hex"])
        assert_equal(self.nodes[0].getblockcount(), cur_height+11)

    def test_transition_mempool_eject(self):
        self.log.info("Testing mempool (r)ejection policy on transitions...")
        # node 1 is still signer, let's transition to something we can PAK peg-out to
        # and OP_TRUE fedpegscript, and set signblockscript back to OP_TRUE

        WSH_OP_TRUE = self.nodes[0].decodescript("51")["segwit"]["hex"]
        xpub = "tpubD6NzVbkrYhZ4WaWSyoBvQwbpLkojyoTZPRsgXELWz3Popb3qkjcJyJUGLnL4qHHoQvao8ESaAstxYSnhyswJ76uZPStJRJCTKvosUCJZL5B"
        init_details = self.nodes[0].initpegoutwallet(xpub)
        pak_entry = init_details["pakentry"]
        # stitch the extension space together using the relevant keys
        extension_space = [pak_entry[4:4+66]+pak_entry[4+66+1:]]
        pak_prop = {"signblockscript":WSH_OP_TRUE, "max_block_witness":3, "fedpegscript":"51", "extension_space":extension_space}

        epoch_info = self.nodes[0].getblockchaininfo()
        blocks_to_end = epoch_info["epoch_length"] - epoch_info["epoch_age"] - 1
        for _ in range(blocks_to_end):
            block = self.nodes[1].getnewblockhex(0, pak_prop)
            sig = self.nodes[1].signblock(block, "")
            comb_result = self.nodes[1].combineblocksigs(block, sig, "")
            assert comb_result["complete"]
            self.nodes[1].submitblock(comb_result["hex"])

        self.sync_all()
        assert_equal(self.nodes[1].getblockchaininfo()["current_signblock_hex"], WSH_OP_TRUE)
        assert_equal(self.nodes[1].getsidechaininfo()["current_fedpegscripts"], ["51", "53"])

        # Transactions

        # Peg-in prep:
        # hack: since we're not validating peg-ins in parent chain, just make
        # both the funding and claim tx on same chain (printing money)
        fund_info = self.nodes[0].getpeginaddress()
        peg_id = self.nodes[0].sendtoaddress(fund_info["mainchain_address"], 1)
        peg_tx = self.nodes[0].gettransaction(peg_id)["hex"]
        self.nodes[0].testmempoolaccept([peg_tx])
        # only one confirm needed in this setup, we do 10 to sync with epoch_length
        self.nodes[0].generatetoaddress(10, self.nodes[0].getnewaddress())
        proof = self.nodes[0].gettxoutproof([peg_id])
        raw_tx = self.nodes[0].gettransaction(peg_id)["hex"]

        # Now, peg-in and PAK peg-out in node 0 mempool

        # We need this transaction to get into the mempool, then transition
        # to new fedpegscript, then wait another epoch, to get dumped.
        claim_id = self.nodes[0].claimpegin(raw_tx, proof, fund_info["claim_script"])
        # saving for re-submission later
        raw_claim = self.nodes[0].gettransaction(claim_id)["hex"]
        # This transaction will be dumped as soon as transition activates
        pegout_id = self.nodes[0].sendtomainchain("", 1)["txid"]
        # Chain payment, this should get "recursively" kicked on transition
        pegout_child_id = self.nodes[0].sendtoaddress(self.nodes[0].getnewaddress(), self.nodes[0].getbalance()['bitcoin'], "", "", True)
        raw_pegout = self.nodes[0].gettransaction(pegout_id)["hex"]
        raw_pool = self.nodes[0].getrawmempool()
        assert claim_id in raw_pool
        assert pegout_id in raw_pool
        assert pegout_child_id in raw_pool

        # node 1 is blocksonly, no mempool so it won't mine node 0's transactions
        assert_equal(self.nodes[1].getrawmempool(), [])
        # Now generate an epoch of blocks on node 1 to show that non-transitions don't dump
        # PAK or peg-in transactions from mempool
        self.nodes[1].generatetoaddress(10, self.nodes[1].getnewaddress())
        self.sync_blocks()
        assert_equal(self.nodes[0].getblockchaininfo()["epoch_age"], 9)

        # Transactions are still in mempool
        raw_pool = self.nodes[0].getrawmempool()
        assert claim_id in raw_pool
        assert pegout_id in raw_pool
        assert pegout_child_id in raw_pool

        # Now have node 1 transition to exact same pak and fedpegscript
        for _ in range(10):
            block = self.nodes[1].getnewblockhex(0, pak_prop)
            assert_equal(self.nodes[1].submitblock(block), None)

        self.sync_blocks()
        assert_equal(self.nodes[0].getblockchaininfo()["epoch_age"], 9)

        # After the 10th block, nothing gets the boot
        raw_pool = self.nodes[0].getrawmempool()
        assert claim_id in raw_pool
        assert pegout_id in raw_pool
        assert pegout_child_id in raw_pool

        # Now have node 1 transition to new pak and fedpegscript
        pak_prop["fedpegscript"] = "52"
        pak_prop["extension_space"] = initial_extension
        for _ in range(10):
            raw_pool = self.nodes[0].getrawmempool()
            assert claim_id in raw_pool
            assert pegout_id in raw_pool
            assert pegout_child_id in raw_pool
            block = self.nodes[1].getnewblockhex(0, pak_prop)
            assert_equal(self.nodes[1].submitblock(block), None)
            self.sync_blocks()

        assert_equal(self.nodes[0].getblockchaininfo()["epoch_age"], 9)

        # After 10 blocks, PAK and child is booted, peg-in still lingers for 1 more epoch
        raw_pool = self.nodes[0].getrawmempool()
        assert claim_id in raw_pool
        assert pegout_id not in raw_pool
        assert pegout_child_id not in raw_pool

        # Re-submission fails
        assert_raises_rpc_error(-26, "invalid-pegout-proof", self.nodes[0].sendrawtransaction, raw_pegout)

        for _ in range(10):
            assert claim_id in self.nodes[0].getrawmempool()
            self.nodes[1].submitblock(self.nodes[1].getnewblockhex())
            self.sync_blocks()

        # After 10 blocks(no proposal), peg-in is finally dumped
        assert claim_id not in self.nodes[0].getrawmempool()

        # Both claim and peg-out rejected from submission as well
        assert_raises_rpc_error(-26, "invalid-pegout-proof", self.nodes[0].sendrawtransaction, raw_pegout)
        assert_raises_rpc_error(-26, "pegin-no-witness, Peg-in tx is invalid.", self.nodes[0].sendrawtransaction, raw_claim)

        # Now we test reorg behavior
        best_blockhash = self.nodes[0].getbestblockhash()

        # Invalidate tip, peg-in should be allowed back into mempool but not pegout
        self.nodes[0].invalidateblock(best_blockhash)
        self.nodes[0].sendrawtransaction(raw_claim)
        assert claim_id in self.nodes[0].getrawmempool()
        assert_raises_rpc_error(-26, "invalid-pegout-proof", self.nodes[0].sendrawtransaction, raw_pegout)

        # Reconsider best block, should be booted and invalid again
        self.nodes[0].reconsiderblock(best_blockhash)
        assert claim_id not in self.nodes[0].getrawmempool()

        # Go back 20 blocks to let peg-out back in
        old_blockhash = self.nodes[0].getblockhash(self.nodes[0].getblockcount()-20)
        self.nodes[0].invalidateblock(old_blockhash)
        self.nodes[0].sendrawtransaction(raw_claim)
        self.nodes[0].sendrawtransaction(raw_pegout)
        assert claim_id in self.nodes[0].getrawmempool()
        assert pegout_id in self.nodes[0].getrawmempool()

        # Again go back to tip, both booted and not let back in
        self.nodes[0].reconsiderblock(best_blockhash)
        assert claim_id not in self.nodes[0].getrawmempool()
        assert pegout_id not in self.nodes[0].getrawmempool()
        assert_raises_rpc_error(-26, "invalid-pegout-proof", self.nodes[0].sendrawtransaction, raw_pegout)
        assert_raises_rpc_error(-26, "pegin-no-witness, Peg-in tx is invalid.", self.nodes[0].sendrawtransaction, raw_claim)

    def assert_accepted(self, tx):
        ret = self.nodes[0].testmempoolaccept([tx])[0]
        assert ret["allowed"], ret["reject-reason"]

    def test_valid_epochs(self):
        self.log.info("Testing pegins and pegouts stay valid for some epochs")
        # previous test leaves us at age 9
        self.nodes[0].generatetoaddress(1, self.nodes[0].getnewaddress())
        self.sync_all()
        assert_equal(self.nodes[1].getblockchaininfo()["epoch_age"], 0)

        # signblockscript is OP_TRUE, let's transition to something we can PAK peg-out to
        # and OP_TRUE fedpegscript, and set signblockscript back to OP_TRUE

        WSH_OP_TRUE = self.nodes[0].decodescript("51")["segwit"]["hex"]
        xpub = "tpubD6NzVbkrYhZ4WaWSyoBvQwbpLkojyoTZPRsgXELWz3Popb3qkjcJyJUGLnL4qHHoQvao8ESaAstxYSnhyswJ76uZPStJRJCTKvosUCJZL5B"
        init_details = self.nodes[1].initpegoutwallet(xpub)
        pak_entry = init_details["pakentry"]
        # stitch the extension space together using the relevant keys
        extension_space = [pak_entry[4:4+66]+pak_entry[4+66+1:]]
        pak_prop = {"signblockscript":WSH_OP_TRUE, "max_block_witness":3, "fedpegscript":"51", "extension_space":extension_space}
        # generate blocks with the new proposal
        for _ in range(9):
            self.nodes[1].submitblock(self.nodes[1].getnewblockhex(0, pak_prop))

        self.sync_all()
        assert_equal(self.nodes[1].getblockchaininfo()["epoch_age"], 9)
        assert_equal(self.nodes[1].getblockchaininfo()["current_signblock_hex"], WSH_OP_TRUE)
        assert_equal(self.nodes[1].getsidechaininfo()["current_fedpegscripts"], ["51", "52"])

        # Transactions

        # pegout prep is easy, just pegout
        pegout_tx = self.nodes[1].gettransaction(self.nodes[1].sendtomainchain("", 1)["txid"])["hex"]
        self.assert_accepted(pegout_tx)

        # Peg-in prep:
        # hack: since we're not validating peg-ins in parent chain, just make
        # both the funding and claim tx on same chain (printing money)
        fund_info = self.nodes[0].getpeginaddress()
        peg_id = self.nodes[0].sendtoaddress(fund_info["mainchain_address"], 1)
        peg_tx = self.nodes[0].gettransaction(peg_id)["hex"]
        # we need the confirmation of the peg tx, so we can't easily assert
        # that the pegin tx would be accepted at this very point
        self.nodes[0].generatetoaddress(1, self.nodes[0].getnewaddress())
        proof = self.nodes[0].gettxoutproof([peg_id])
        pegin_tx = self.nodes[0].createrawpegin(peg_tx, proof, fund_info["claim_script"])["hex"]
        pegin_tx = self.nodes[0].signrawtransactionwithwallet(pegin_tx)["hex"]
        # both should be allowed after that block
        assert_equal(self.nodes[0].getsidechaininfo()["current_fedpegscripts"], ["51", "52"])
        self.assert_accepted(pegin_tx)
        self.assert_accepted(pegout_tx)

        # let's generate 20 blocks to pass through 2 new epochs without there being a transition
        for _ in range(20):
            self.nodes[0].generatetoaddress(1, self.nodes[0].getnewaddress())
            self.assert_accepted(pegin_tx)
            self.assert_accepted(pegout_tx)
        assert_equal(self.nodes[0].getsidechaininfo()["current_fedpegscripts"], ["51", "51"])
        self.sync_blocks()

        # Now have node 1 transition to new pak and fedpegscript
        pak_prop["fedpegscript"] = "52"
        pak_prop["extension_space"] = initial_extension
        for _ in range(9):
            self.assert_accepted(pegin_tx)
            self.assert_accepted(pegout_tx)
            self.nodes[1].submitblock(self.nodes[1].getnewblockhex(0, pak_prop))
            self.sync_blocks()

        # so right before the next epoch, the new params are active and
        # the pegout is already invalid while the pegin is still valid
        self.assert_accepted(pegin_tx)
        assert_equal(self.nodes[0].testmempoolaccept([pegout_tx])[0]["reject-reason"], ERR_MP_INVALID_PEGOUT)
        # lets go back one block and make sure we can mine the pegout tx
        old_tip = self.nodes[0].getbestblockhash()
        self.nodes[0].invalidateblock(old_tip)
        pegout_txid = self.nodes[0].sendrawtransaction(pegout_tx)
        self.nodes[0].submitblock(self.nodes[0].getnewblockhex(0, pak_prop))
        tip = self.nodes[0].getbestblockhash()
        assert_equal(self.nodes[0].getrawtransaction(pegout_txid, True, tip)["confirmations"], 1)
        # undo it again so that we can make sure it is no longer allowed after this point
        self.nodes[0].invalidateblock(tip)
        self.nodes[0].reconsiderblock(old_tip)

        # and after the 10th block of course that is still the case
        self.nodes[1].submitblock(self.nodes[1].getnewblockhex(0, pak_prop))
        self.sync_blocks()
        self.assert_accepted(pegin_tx)
        assert_equal(self.nodes[0].testmempoolaccept([pegout_tx])[0]["reject-reason"], ERR_MP_INVALID_PEGOUT)

        # We're in the next epoch, in this one the pegin tx should be accepted up until the last block
        assert_equal(self.nodes[1].getsidechaininfo()["current_fedpegscripts"], ["52", "51"])
        for _ in range(9):
            self.assert_accepted(pegin_tx)
            assert_equal(self.nodes[0].testmempoolaccept([pegout_tx])[0]["reject-reason"], ERR_MP_INVALID_PEGOUT)
            self.nodes[1].generatetoaddress(1, self.nodes[1].getnewaddress())
            self.sync_blocks()

        # so on the last block both should not be allowed
        assert_equal(self.nodes[1].getsidechaininfo()["current_fedpegscripts"], ["52", "52"])
        assert_equal(self.nodes[0].testmempoolaccept([pegout_tx])[0]["reject-reason"], ERR_MP_INVALID_PEGOUT)
        assert_equal(self.nodes[0].testmempoolaccept([pegin_tx])[0]["reject-reason"], ERR_MP_INVALID_PEGIN)

        # then undo the last block and make sure we could have mined the pegin in the very last block
        self.nodes[0].invalidateblock(self.nodes[0].getbestblockhash())
        # first use the pegin tx created earlier
        pegin_txid = self.nodes[0].sendrawtransaction(pegin_tx)
        self.nodes[0].generatetoaddress(1, self.nodes[0].getnewaddress())
        assert_equal(self.nodes[0].gettransaction(pegin_txid)["confirmations"], 1)
        # make sure that using claimpegin directly also works
        self.nodes[0].invalidateblock(self.nodes[0].getbestblockhash())
        pegin_txid = self.nodes[0].claimpegin(peg_tx, proof, fund_info["claim_script"])
        self.nodes[0].generatetoaddress(1, self.nodes[0].getnewaddress())
        assert_equal(self.nodes[0].gettransaction(pegin_txid)["confirmations"], 1)

    def run_test(self):
        self.test_legacy_params()
        self.test_dynafed_activation()
        self.test_illegal_proposals()
        self.test_no_vote()
        self.test_under_vote()
        self.test_four_fifth_vote()
        self.test_all_vote()
        self.test_transition_mempool_eject()
        self.test_valid_epochs()

if __name__ == '__main__':
    DynaFedTest().main()
