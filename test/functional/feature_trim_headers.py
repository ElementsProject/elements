#!/usr/bin/env python3

import codecs

from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import assert_equal
from test_framework import (
    address,
    key,
)
from test_framework.messages import (
    CBlock,
    from_hex,
)
from test_framework.script import (
    OP_NOP,
    OP_RETURN,
    CScript
)

# Generate wallet import format from private key.
def wif(pk):
    # Base58Check version for regtest WIF keys is 0xef = 239
    pk_compressed = pk + bytes([0x1])
    return address.byte_to_base58(pk_compressed, 239)

# The signblockscript is a Bitcoin Script k-of-n multisig script.
def make_signblockscript(num_nodes, required_signers, keys):
    assert num_nodes >= required_signers
    script = "{}".format(50 + required_signers)
    for i in range(num_nodes):
        k = keys[i]
        script += "21"
        script += codecs.encode(k.get_pubkey().get_bytes(), 'hex_codec').decode("utf-8")
    script += "{}".format(50 + num_nodes)  # num keys
    script += "ae"  # OP_CHECKMULTISIG
    return script

class TrimHeadersTest(BitcoinTestFramework):
    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    # Dynamically generate N keys to be used for block signing.
    def init_keys(self, num_keys):
        self.keys = []
        self.wifs = []
        for i in range(num_keys):
            k = key.ECKey()
            k.generate()
            w = wif(k.get_bytes())
            self.keys.append(k)
            self.wifs.append(w)

    def set_test_params(self):
        self.num_nodes = 3
        self.num_keys = 1
        self.required_signers = 1
        self.setup_clean_chain = True
        self.init_keys(self.num_keys)
        signblockscript = make_signblockscript(self.num_keys, self.required_signers, self.keys)
        self.witnessScript = signblockscript  # post-dynafed this becomes witnessScript
        args = [
            "-signblockscript={}".format(signblockscript),
            "-con_max_block_sig_size={}".format(self.required_signers * 74 + self.num_nodes * 33),
            "-anyonecanspendaremine=1",
            "-evbparams=dynafed:0:::",
            "-con_dyna_deploy_signal=1",
        ]
        self.trim_args = args + ["-trim_headers=1"]
        self.prune_args = self.trim_args + ["-prune=1"]
        self.extra_args = [
            args,
            self.trim_args,
            self.prune_args,
        ]

    def setup_network(self):
        self.setup_nodes()
        self.connect_nodes(0, 1)
        self.connect_nodes(0, 2)

    def check_height(self, expected_height, all=False, verbose=True):
        if verbose:
            self.log.info(f"Check height {expected_height}")
        if all:
            for n in self.nodes:
                assert_equal(n.getblockcount(), expected_height)
        else:
            assert_equal(self.nodes[0].getblockcount(), expected_height)

    def mine_block(self, make_transactions):
        # alternate mining between the signing nodes
        mineridx = self.nodes[0].getblockcount() % self.required_signers  # assuming in sync
        mineridx_next = (self.nodes[0].getblockcount() + 1) % self.required_signers
        miner = self.nodes[mineridx]
        miner_next = self.nodes[mineridx_next]

        # If dynafed is enabled, this means signblockscript has been WSH-wrapped
        blockchain_info = self.nodes[0].getblockchaininfo()
        deployment_info = self.nodes[0].getdeploymentinfo()
        dynafed_active = deployment_info['deployments']['dynafed']['bip9']['status'] == "active"
        if dynafed_active:
            wsh_wrap = self.nodes[0].decodescript(self.witnessScript)['segwit']['hex']
            assert_equal(wsh_wrap, blockchain_info['current_signblock_hex'])

        # Make a few transactions to make non-empty blocks for compact transmission
        if make_transactions:
            for i in range(10):
                miner.sendtoaddress(miner_next.getnewaddress(), 1, "", "", True)
        # miner makes a block
        block = miner.getnewblockhex()
        block_struct = from_hex(CBlock(), block)

        # make another block with the commitment field filled out
        dummy_block = miner.getnewblockhex(commit_data="deadbeef")
        dummy_struct = from_hex(CBlock(), dummy_block)
        assert_equal(len(dummy_struct.vtx[0].vout), len(block_struct.vtx[0].vout) + 1)
        # OP_RETURN deadbeef
        assert_equal(CScript(dummy_struct.vtx[0].vout[0].scriptPubKey).hex(), '6a04deadbeef')

        # All nodes get compact blocks, first node may get complete
        # block in 0.5 RTT even with transactions thanks to p2p connection
        # with non-signing node being miner
        for i in range(self.num_keys):
            sketch = miner.getcompactsketch(block)
            compact_response = self.nodes[i].consumecompactsketch(sketch)
            if "block_tx_req" in compact_response:
                block_txn = self.nodes[i].consumegetblocktxn(block, compact_response["block_tx_req"])
                final_block = self.nodes[i].finalizecompactblock(sketch, block_txn, compact_response["found_transactions"])
            else:
                # If there's only coinbase, it should succeed immediately
                final_block = compact_response["blockhex"]
            # Block should be complete, sans signatures
            self.nodes[i].testproposedblock(final_block)

        # collect num_keys signatures from signers, reduce to required_signers sigs during combine
        sigs = []
        for i in range(self.num_keys):
            result = miner.combineblocksigs(block, sigs, self.witnessScript)
            sigs = sigs + self.nodes[i].signblock(block, self.witnessScript)
            assert_equal(result["complete"], i >= self.required_signers)
            # submitting should have no effect pre-threshhold
            if i < self.required_signers:
                miner.submitblock(result["hex"])

        result = miner.combineblocksigs(block, sigs, self.witnessScript)
        assert_equal(result["complete"], True)

        self.nodes[0].submitblock(result["hex"])

    def mine_blocks(self, num_blocks, transactions):
        for _ in range(num_blocks):
            self.mine_block(transactions)

    def mine_large_blocks(self, n):
        big_script = CScript([OP_RETURN] + [OP_NOP] * 950000)
        node = self.nodes[0]

        for _ in range(n):
            hex = node.getnewblockhex()
            block = from_hex(CBlock(), hex)
            tx = block.vtx[0]
            tx.vout[0].scriptPubKey = big_script
            tx.rehash()
            block.vtx[0] = tx
            block.hashMerkleRoot = block.calc_merkle_root()
            block.solve()
            h = block.serialize().hex()

            sigs = node.signblock(h, self.witnessScript)

            result = node.combineblocksigs(h, sigs, self.witnessScript)
            assert_equal(result["complete"], True)

            node.submitblock(result["hex"])


    def run_test(self):
        for i in range(self.num_keys):
            self.nodes[i].importprivkey(self.wifs[i])

        expected_height = 0
        self.check_height(expected_height, all=True)

        self.log.info("Mining and signing 101 blocks to unlock funds")
        expected_height += 101
        self.mine_blocks(101, False)
        self.sync_all()
        self.check_height(expected_height, all=True)
        # check the new field in getblockchaininfo
        assert not self.nodes[0].getblockchaininfo()["trim_headers"]
        assert self.nodes[1].getblockchaininfo()["trim_headers"]
        assert self.nodes[2].getblockchaininfo()["trim_headers"]

        self.log.info("Shut down trimmed nodes")
        self.stop_node(1)
        self.stop_node(2)

        self.log.info("Mining and signing non-empty blocks")
        expected_height += 10
        self.mine_blocks(10, True)
        self.check_height(expected_height)

        # signblock rpc field stuff
        tip = self.nodes[0].getblockhash(self.nodes[0].getblockcount())
        header = self.nodes[0].getblockheader(tip)
        block = self.nodes[0].getblock(tip)

        assert 'signblock_witness_asm' in header
        assert 'signblock_witness_hex' in header
        assert 'signblock_witness_asm' in block
        assert 'signblock_witness_hex' in block

        assert_equal(self.nodes[0].getdeploymentinfo()['deployments']['dynafed']['bip9']['status'], "defined")

        # activate dynafed
        blocks_til_dynafed = 431 - self.nodes[0].getblockcount()
        self.log.info("Activating dynafed")
        self.mine_blocks(blocks_til_dynafed, False)
        expected_height += blocks_til_dynafed
        self.check_height(expected_height)

        assert_equal(self.nodes[0].getdeploymentinfo()['deployments']['dynafed']['bip9']['status'], "locked_in")

        num = 3000
        self.log.info(f"Mine {num} dynamic federation blocks without txns")
        self.mine_blocks(num, False)
        expected_height += num
        self.check_height(expected_height)

        num = 10
        self.log.info(f"Mine {num} dynamic federation blocks with txns")
        self.mine_blocks(num, True)
        expected_height += num
        self.check_height(expected_height)

        num = 777
        self.log.info(f"Mine {num} large blocks")
        expected_height += num
        self.mine_large_blocks(num)

        self.log.info("Restart the trimmed nodes")
        self.start_node(1, extra_args=self.trim_args)
        self.start_node(2, extra_args=self.prune_args)
        self.connect_nodes(0, 1)
        self.connect_nodes(0, 2)

        self.sync_all()
        self.check_height(expected_height, all=True)

        self.log.info("Prune the pruned node")
        self.nodes[2].pruneblockchain(4000)

        hash = self.nodes[0].getblockhash(expected_height)
        block = self.nodes[0].getblock(hash)
        for i in range(1, self.num_nodes):
            assert_equal(hash, self.nodes[i].getblockhash(expected_height))
            assert_equal(block, self.nodes[i].getblock(hash))

        self.log.info(f"All nodes at height {expected_height} with block hash {hash}")


if __name__ == '__main__':
    TrimHeadersTest().main()
