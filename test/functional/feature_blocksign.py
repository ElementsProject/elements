#!/usr/bin/env python3

import codecs
import hashlib
import random

from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import (assert_raises_rpc_error, assert_equal, connect_nodes_bi)
from test_framework import (
    address,
    key,
)

# Generate wallet import format from private key.
def wif(pk):
    # Base58Check version for regtest WIF keys is 0xef = 239
    return address.byte_to_base58(pk, 239)

# The signblockscript is a Bitcoin Script k-of-n multisig script.
def make_signblockscript(num_nodes, required_signers, keys):
    assert(num_nodes >= required_signers)
    script = "{}".format(50 + required_signers)
    for i in range(num_nodes):
        k = keys[i]
        script += "41"
        script += codecs.encode(k.get_pubkey(), 'hex_codec').decode("utf-8")
    script += "{}".format(50 + num_nodes) # num keys
    script += "ae" # OP_CHECKMULTISIG
    print('signblockscript', script)
    return script

class BlockSignTest(BitcoinTestFramework):
    """
    Test signed-blockchain-related RPC calls and functionality:

        - getnewblockhex
        - signblock
        - combineblocksigs
        - submitblock
        - testproposedblock
        - getcompactsketch
        - consumecompactsketch
        - consumegetblocktxn
        - finalizecompactblock

        As well as syncing blocks over p2p

    """
    # Dynamically generate N keys to be used for block signing.
    def init_keys(self, num_keys):
        self.keys = []
        self.wifs = []
        for i in range(num_keys):
            k = key.CECKey()
            pk_bytes = hashlib.sha256(str(random.getrandbits(256)).encode('utf-8')).digest()
            k.set_secretbytes(pk_bytes)
            w = wif(pk_bytes)
            print("generated key {}: \n pub: {}\n  wif: {}".format(i+1,
                codecs.encode(k.get_pubkey(), 'hex_codec').decode("utf-8"),
                w))
            self.keys.append(k)
            self.wifs.append(wif(pk_bytes))

    def set_test_params(self):
        self.num_nodes = 5
        self.num_keys = 4
        self.required_signers = 3
        self.setup_clean_chain = True
        self.init_keys(self.num_nodes-1) # Last node cannot sign and is connected to all via p2p
        signblockscript = make_signblockscript(self.num_keys, self.required_signers, self.keys)
        self.extra_args = [[
            "-signblockscript={}".format(signblockscript),
            "-con_max_block_sig_size={}".format(self.required_signers*74),
            "-anyonecanspendaremine=1"
        ]] * self.num_nodes

    def setup_network(self):
        self.setup_nodes()
        # Connect non-signing node to a single signing one (to not pass blocks between signers)
        connect_nodes_bi(self.nodes, 0, self.num_nodes-1)

    def check_height(self, expected_height):
        for n in self.nodes:
            assert_equal(n.getblockcount(), expected_height)

    def mine_block(self, make_transactions):
        # mine block in round robin sense: depending on the block number, a node
        # is selected to create the block, others sign it and the selected node
        # broadcasts it
        mineridx = self.nodes[0].getblockcount() % self.num_nodes # assuming in sync
        mineridx_next = (self.nodes[0].getblockcount() + 1) % self.num_nodes
        miner = self.nodes[mineridx]
        miner_next = self.nodes[mineridx_next]
        blockcount = miner.getblockcount()

        # Make a few transactions to make non-empty blocks for compact transmission
        if make_transactions:
            for i in range(5):
                miner.sendtoaddress(miner_next.getnewaddress(), int(miner.getbalance()/10), "", "", True)
        # miner makes a block
        block = miner.getnewblockhex()

        # other signing nodes get fed compact blocks
        for i in range(self.num_keys):
            if i == mineridx:
                continue
            sketch = miner.getcompactsketch(block)
            compact_response = self.nodes[i].consumecompactsketch(sketch)
            if make_transactions:
                block_txn =  self.nodes[i].consumegetblocktxn(block, compact_response["block_tx_req"])
                final_block = self.nodes[i].finalizecompactblock(sketch, block_txn, compact_response["found_transactions"])
            else:
                # If there's only coinbase, it should succeed immediately
                final_block = compact_response["blockhex"]
            # Block should be complete, sans signatures
            self.nodes[i].testproposedblock(final_block)

        # non-signing node can not sign
        assert_raises_rpc_error(-25, "Could not sign the block.", self.nodes[-1].signblock, block)

        # collect num_keys signatures from signers, reduce to required_signers sigs during combine
        sigs = []
        for i in range(self.num_keys):
            result = miner.combineblocksigs(block, sigs)
            sigs = sigs + self.nodes[i].signblock(block)
            assert_equal(result["complete"], i >= self.required_signers)
            # submitting should have no effect pre-threshhold
            if i < self.required_signers:
                miner.submitblock(result["hex"])
                self.check_height(blockcount)

        result = miner.combineblocksigs(block, sigs)
        assert_equal(result["complete"], True)

        # All signing nodes must submit... we're not connected!
        self.nodes[0].submitblock(result["hex"])
        early_proposal = self.nodes[0].getnewblockhex() # testproposedblock should reject
        # Submit blocks to all other signing nodes next, as well as too-early block proposal
        for i in range(1, self.num_keys):
            assert_raises_rpc_error(-25, "proposal was not based on our best chain", self.nodes[i].testproposedblock, early_proposal)
            self.nodes[i].submitblock(result["hex"])

        # All nodes should be synced in blocks and transactions(mempool should be empty)
        self.sync_all()

    def mine_blocks(self, num_blocks, transactions):
        for i in range(num_blocks):
            self.mine_block(transactions)

    def run_test(self):
        # Have every node except last import its block signing private key.
        for i in range(self.num_keys):
            self.nodes[i].importprivkey(self.wifs[i])

        self.check_height(0)

        # mine a block with no transactions
        print("Mining and signing 101 blocks to unlock funds")
        self.mine_blocks(101, False)

        # mine blocks with transactions
        print("Mining and signing non-empty blocks")
        self.mine_blocks(10, True)

        # Height check also makes sure non-signing, p2p connected node gets block
        self.check_height(111)

        # signblock rpc field stuff
        tip = self.nodes[0].getblockhash(self.nodes[0].getblockcount())
        header = self.nodes[0].getblockheader(tip)
        block = self.nodes[0].getblock(tip)
        info = self.nodes[0].getblockchaininfo()

        assert('signblock_witness_asm' in header)
        assert('signblock_witness_hex' in header)
        assert('signblock_witness_asm' in block)
        assert('signblock_witness_hex' in block)

        signblockscript = make_signblockscript(self.num_keys, self.required_signers, self.keys)
        assert_equal(info['signblock_asm'], self.nodes[0].decodescript(signblockscript)['asm'])
        assert_equal(info['signblock_hex'], signblockscript)

if __name__ == '__main__':
    BlockSignTest().main()
