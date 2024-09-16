#!/usr/bin/env python3
# Copyright (c) 2014-2021 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Test the RBF code."""

from decimal import Decimal

from test_framework.messages import (
    BIP125_SEQUENCE_NUMBER,
    COIN,
    COutPoint,
    CTransaction,
    CTxIn,
    CTxOut,
    CTxOutValue,
    SEQUENCE_FINAL,
)
from test_framework.script import CScript, OP_DROP
from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import (
    assert_equal,
    assert_raises_rpc_error,
)
from test_framework.script_util import (
    DUMMY_P2WPKH_SCRIPT,
    DUMMY_2_P2WPKH_SCRIPT,
)
from test_framework.wallet import MiniWallet
from test_framework.address import ADDRESS_BCRT1_UNSPENDABLE

MAX_REPLACEMENT_LIMIT = 100
class ReplaceByFeeTest(BitcoinTestFramework):
    def set_test_params(self):
        self.num_nodes = 2
        self.extra_args = [
            [
                "-acceptnonstdtxn=1",
                "-maxorphantx=1000",
                "-limitancestorcount=50",
                "-limitancestorsize=101",
                "-limitdescendantcount=200",
                "-limitdescendantsize=101",
            ],
            # second node has default mempool parameters
            [
            ],
        ]
        self.supports_cli = False

    def run_test(self):
        self.wallet = MiniWallet(self.nodes[0])
        # the pre-mined test framework chain contains coinbase outputs to the
        # MiniWallet's default address in blocks 76-100 (see method
        # BitcoinTestFramework._initialize_chain())
        self.wallet.rescan_utxos()

        # ELEMENTS: FIXME
        # self.log.info("Running test simple doublespend...")
        # self.test_simple_doublespend()

        # self.log.info("Running test doublespend chain...")
        # self.test_doublespend_chain()

        # self.log.info("Running test doublespend tree...")
        # self.test_doublespend_tree()

        # self.log.info("Running test replacement feeperkb...")
        # self.test_replacement_feeperkb()

        # self.log.info("Running test spends of conflicting outputs...")
        # self.test_spends_of_conflicting_outputs()

        # self.log.info("Running test new unconfirmed inputs...")
        # self.test_new_unconfirmed_inputs()

        # self.log.info("Running test too many replacements...")
        # self.test_too_many_replacements()

        #self.log.info("Running test too many replacements using default mempool params...")
        #self.test_too_many_replacements_with_default_mempool_params()

        #self.log.info("Running test opt-in...")
        #self.test_opt_in()

        # self.log.info("Running test RPC...")
        # self.test_rpc()

        # self.log.info("Running test prioritised transactions...")
        # self.test_prioritised_transactions()

        # self.log.info("Running test no inherited signaling...")
        # self.test_no_inherited_signaling()

        # self.log.info("Running test replacement relay fee...")
        # self.test_replacement_relay_fee()

        # self.log.info("Passed")

    def make_utxo(self, node, amount, confirmed=True, scriptPubKey=DUMMY_P2WPKH_SCRIPT):
        """Create a txout with a given amount and scriptPubKey

        confirmed - txouts created will be confirmed in the blockchain;
                    unconfirmed otherwise.
        """
        txid, n = self.wallet.send_to(from_node=node, scriptPubKey=scriptPubKey, amount=amount)

        # If requested, ensure txouts are confirmed.
        if confirmed:
            mempool_size = len(node.getrawmempool())
            while mempool_size > 0:
                node.generate(1)
                new_size = len(node.getrawmempool())
                # Error out if we have something stuck in the mempool, as this
                # would likely be a bug.
                assert new_size < mempool_size
                mempool_size = new_size

        return COutPoint(int(txid, 16), n)


    def test_simple_doublespend(self):
        """Simple doublespend"""
        # ELEMENTS: keep make_utxo logic instead of create_self_transfer change (from Bitcoin PR #22330)
        tx0_outpoint = self.make_utxo(self.nodes[0], int(1.1 * COIN))

        # make_utxo may have generated a bunch of blocks, so we need to sync
        # before we can spend the coins generated, or else the resulting
        # transactions might not be accepted by our peers.
        self.sync_all()

        feeout = CTxOut(int(0.1*COIN), CScript())
        tx1a = CTransaction()
        tx1a.vin = [CTxIn(tx0_outpoint, nSequence=0)]
        tx1a.vout = [CTxOut(1 * COIN, DUMMY_P2WPKH_SCRIPT), feeout]
        tx1a_hex = tx1a.serialize().hex()
        tx1a_txid = self.nodes[0].sendrawtransaction(tx1a_hex, 0)

        # Should fail because we haven't changed the fee
        tx1b = CTransaction()
        tx1b.vin = [CTxIn(tx0_outpoint, nSequence=0)]
        tx1b.vout = [CTxOut(1 * COIN, DUMMY_2_P2WPKH_SCRIPT), feeout]
        tx1b_hex = tx1b.serialize().hex()

        # This will raise an exception due to insufficient fee
        assert_raises_rpc_error(-26, "insufficient fee", self.nodes[0].sendrawtransaction, tx1b_hex, 0)

        # Extra 0.1 BTC fee
        tx1b = CTransaction()
        tx1b.vin = [CTxIn(tx0_outpoint, nSequence=0)]
        tx1b.vout = [CTxOut(int(0.9 * COIN), DUMMY_P2WPKH_SCRIPT), feeout, feeout]
        tx1b_hex = tx1b.serialize().hex()
        # Works when enabled
        tx1b_txid = self.nodes[0].sendrawtransaction(tx1b_hex, 0)

        mempool = self.nodes[0].getrawmempool()

        assert tx1a_txid not in mempool
        assert tx1b_txid in mempool

        assert_equal(tx1b_hex, self.nodes[0].getrawtransaction(tx1b_txid))

    def test_doublespend_chain(self):
        """Doublespend of a long chain"""

        initial_nValue = 5 * COIN
        tx0_outpoint = self.make_utxo(self.nodes[0], initial_nValue)

        prevout = tx0_outpoint
        remaining_value = initial_nValue
        chain_txids = []
        while remaining_value > 1 * COIN:
            remaining_value -= int(0.1 * COIN)
            tx = CTransaction()
            tx.vin = [CTxIn(prevout, nSequence=0)]
            feeout = CTxOut(1*COIN)
            tx.vout = [CTxOut(remaining_value, CScript([1, OP_DROP] * 15 + [1])), feeout]
            tx_hex = tx.serialize().hex()
            txid = self.nodes[0].sendrawtransaction(tx_hex, 0)
            chain_txids.append(txid)
            prevout = COutPoint(int(txid, 16), 0)

        # Whether the double-spend is allowed is evaluated by including all
        # child fees - 4 BTC - so this attempt is rejected.
        dbl_tx = CTransaction()
        dbl_tx.vin = [CTxIn(tx0_outpoint, nSequence=0)]
        dbl_tx.vout = [CTxOut(initial_nValue - 3 * COIN, DUMMY_P2WPKH_SCRIPT)]
        dbl_tx_hex = dbl_tx.serialize().hex()

        # This will raise an exception due to insufficient fee
        assert_raises_rpc_error(-26, "insufficient fee", self.nodes[0].sendrawtransaction, dbl_tx_hex, 0)

        # Accepted with sufficient fee
        dbl_tx = CTransaction()
        dbl_tx.vin = [CTxIn(tx0_outpoint, nSequence=0)]
        dbl_tx.vout = [CTxOut(int(0.1 * COIN), DUMMY_P2WPKH_SCRIPT)]
        dbl_tx_hex = dbl_tx.serialize().hex()
        self.nodes[0].sendrawtransaction(dbl_tx_hex, 0)

        mempool = self.nodes[0].getrawmempool()
        for doublespent_txid in chain_txids:
            assert doublespent_txid not in mempool

    def test_doublespend_tree(self):
        """Doublespend of a big tree of transactions"""

        initial_nValue = 5 * COIN
        tx0_outpoint = self.make_utxo(self.nodes[0], initial_nValue)

        def branch(prevout, initial_value, max_txs, tree_width=5, fee=0.00001 * COIN, _total_txs=None):
            if _total_txs is None:
                _total_txs = [0]
            if _total_txs[0] >= max_txs:
                return

            txout_value = (initial_value - fee) // tree_width
            if txout_value < fee:
                return

            vout = [CTxOut(txout_value, CScript([i+1]))
                    for i in range(tree_width)]
            vout.append(CTxOut(int(initial_value - tree_width*txout_value)))
            tx = CTransaction()
            tx.vin = [CTxIn(prevout, nSequence=0)]
            tx.vout = vout
            tx_hex = tx.serialize().hex()

            assert len(tx.serialize()) < 100000
            txid = self.nodes[0].sendrawtransaction(tx_hex, 0)
            yield tx
            _total_txs[0] += 1

            txid = int(txid, 16)

            for i, txout in enumerate(tx.vout):
                if txout.is_fee():
                    continue
                for x in branch(COutPoint(txid, i), txout_value,
                                  max_txs,
                                  tree_width=tree_width, fee=fee,
                                  _total_txs=_total_txs):
                    yield x

        fee = int(0.00001 * COIN)
        n = MAX_REPLACEMENT_LIMIT
        tree_txs = list(branch(tx0_outpoint, initial_nValue, n, fee=fee))
        assert_equal(len(tree_txs), n)

        # Attempt double-spend, will fail because too little fee paid
        dbl_tx = CTransaction()
        dbl_tx.vin = [CTxIn(tx0_outpoint, nSequence=0)]
        dbl_tx.vout = [CTxOut(initial_nValue - fee * n, DUMMY_P2WPKH_SCRIPT), CTxOut(fee*n)]
        dbl_tx_hex = dbl_tx.serialize().hex()
        # This will raise an exception due to insufficient fee
        assert_raises_rpc_error(-26, "insufficient fee", self.nodes[0].sendrawtransaction, dbl_tx_hex, 0)

        # 0.1 BTC fee is enough
        dbl_tx = CTransaction()
        dbl_tx.vin = [CTxIn(tx0_outpoint, nSequence=0)]
        dbl_tx.vout = [CTxOut(initial_nValue - fee * n - int(0.1 * COIN), DUMMY_P2WPKH_SCRIPT)]
        dbl_tx_hex = dbl_tx.serialize().hex()
        self.nodes[0].sendrawtransaction(dbl_tx_hex, 0)

        mempool = self.nodes[0].getrawmempool()

        for tx in tree_txs:
            tx.rehash()
            assert tx.hash not in mempool

        # Try again, but with more total transactions than the "max txs
        # double-spent at once" anti-DoS limit.
        for n in (MAX_REPLACEMENT_LIMIT + 1, MAX_REPLACEMENT_LIMIT * 2):
            fee = int(0.00001 * COIN)
            tx0_outpoint = self.make_utxo(self.nodes[0], initial_nValue)
            tree_txs = list(branch(tx0_outpoint, initial_nValue, n, fee=fee))
            assert_equal(len(tree_txs), n)

            dbl_tx = CTransaction()
            dbl_tx.vin = [CTxIn(tx0_outpoint, nSequence=0)]
            dbl_tx.vout = [CTxOut(initial_nValue - 2 * fee * n, DUMMY_P2WPKH_SCRIPT), CTxOut(2*fee*n)]
            dbl_tx_hex = dbl_tx.serialize().hex()
            # This will raise an exception
            assert_raises_rpc_error(-26, "too many potential replacements", self.nodes[0].sendrawtransaction, dbl_tx_hex, 0)

            for tx in tree_txs:
                tx.rehash()
                self.nodes[0].getrawtransaction(tx.hash)

    def test_replacement_feeperkb(self):
        """Replacement requires fee-per-KB to be higher"""
        tx0_outpoint = self.make_utxo(self.nodes[0], int(1.1 * COIN))

        tx1a = CTransaction()
        tx1a.vin = [CTxIn(tx0_outpoint, nSequence=0)]
        tx1a.vout = [CTxOut(1 * COIN, DUMMY_P2WPKH_SCRIPT), CTxOut(int(0.1*COIN))]
        tx1a_hex = tx1a.serialize().hex()
        self.nodes[0].sendrawtransaction(tx1a_hex, 0)

        # Higher fee, but the fee per KB is much lower, so the replacement is
        # rejected.
        tx1b = CTransaction()
        tx1b.vin = [CTxIn(tx0_outpoint, nSequence=0)]
        tx1b.vout = [CTxOut(int(0.001 * COIN), CScript([b'a' * 999000])), CTxOut(int(1.1 * COIN - 0.001 * COIN))]
        tx1b_hex = tx1b.serialize().hex()

        # This will raise an exception due to insufficient fee
        assert_raises_rpc_error(-26, "insufficient fee", self.nodes[0].sendrawtransaction, tx1b_hex, 0)

    def test_spends_of_conflicting_outputs(self):
        """Replacements that spend conflicting tx outputs are rejected"""
        utxo1 = self.make_utxo(self.nodes[0], int(1.2 * COIN))
        utxo2 = self.make_utxo(self.nodes[0], 3 * COIN)

        tx1a = CTransaction()
        tx1a.vin = [CTxIn(utxo1, nSequence=0)]
        tx1a.vout = [CTxOut(int(1.1 * COIN), DUMMY_P2WPKH_SCRIPT), CTxOut(int(0.1*COIN))]
        tx1a_hex = tx1a.serialize().hex()
        tx1a_txid = self.nodes[0].sendrawtransaction(tx1a_hex, 0)

        tx1a_txid = int(tx1a_txid, 16)

        # Direct spend an output of the transaction we're replacing.
        tx2 = CTransaction()
        tx2.vin = [CTxIn(utxo1, nSequence=0), CTxIn(utxo2, nSequence=0)]
        tx2.vin.append(CTxIn(COutPoint(tx1a_txid, 0), nSequence=0))
        tx2.vout = tx1a.vout + [CTxOut(3*COIN + int(1.1*COIN))]
        tx2_hex = tx2.serialize().hex()

        # This will raise an exception
        assert_raises_rpc_error(-26, "bad-txns-spends-conflicting-tx", self.nodes[0].sendrawtransaction, tx2_hex, 0)

        # Spend tx1a's output to test the indirect case.
        tx1b = CTransaction()
        tx1b.vin = [CTxIn(COutPoint(tx1a_txid, 0), nSequence=0)]
        tx1b.vout = [CTxOut(1 * COIN, DUMMY_P2WPKH_SCRIPT), CTxOut(int(0.1*COIN))]
        tx1b_hex = tx1b.serialize().hex()
        tx1b_txid = self.nodes[0].sendrawtransaction(tx1b_hex, 0)
        tx1b_txid = int(tx1b_txid, 16)

        tx2 = CTransaction()
        tx2.vin = [CTxIn(utxo1, nSequence=0), CTxIn(utxo2, nSequence=0),
                   CTxIn(COutPoint(tx1b_txid, 0))]
        tx2.vout = tx1a.vout + [CTxOut(3*COIN + int(1.0*COIN))]
        tx2_hex = tx2.serialize().hex()

        # This will raise an exception
        assert_raises_rpc_error(-26, "bad-txns-spends-conflicting-tx", self.nodes[0].sendrawtransaction, tx2_hex, 0)

    def test_new_unconfirmed_inputs(self):
        """Replacements that add new unconfirmed inputs are rejected"""
        confirmed_utxo = self.make_utxo(self.nodes[0], int(1.1 * COIN))
        unconfirmed_utxo = self.make_utxo(self.nodes[0], int(0.1 * COIN), False)

        tx1 = CTransaction()
        tx1.vin = [CTxIn(confirmed_utxo)]
        tx1.vout = [CTxOut(1 * COIN, DUMMY_P2WPKH_SCRIPT), CTxOut(int(0.1*COIN))]
        tx1_hex = tx1.serialize().hex()
        self.nodes[0].sendrawtransaction(tx1_hex, 0)

        tx2 = CTransaction()
        tx2.vin = [CTxIn(confirmed_utxo), CTxIn(unconfirmed_utxo)]
        tx2.vout = tx1.vout + [CTxOut(int(0.1*COIN))]
        tx2_hex = tx2.serialize().hex()

        # This will raise an exception
        assert_raises_rpc_error(-26, "replacement-adds-unconfirmed", self.nodes[0].sendrawtransaction, tx2_hex, 0)

    def test_too_many_replacements(self):
        """Replacements that evict too many transactions are rejected"""
        # Try directly replacing more than MAX_REPLACEMENT_LIMIT
        # transactions

        # Start by creating a single transaction with many outputs
        initial_nValue = 10 * COIN
        utxo = self.make_utxo(self.nodes[0], initial_nValue)
        fee = int(0.0001 * COIN)
        split_value = int((initial_nValue - fee) / (MAX_REPLACEMENT_LIMIT + 1))

        outputs = []
        for _ in range(MAX_REPLACEMENT_LIMIT + 1):
            outputs.append(CTxOut(split_value, CScript([1])))

        splitting_tx = CTransaction()
        splitting_tx.vin = [CTxIn(utxo, nSequence=0)]
        splitting_tx.vout = outputs + [CTxOut(int(initial_nValue - (MAX_REPLACEMENT_LIMIT+1) * split_value))]
        splitting_tx_hex = splitting_tx.serialize().hex()

        txid = self.nodes[0].sendrawtransaction(splitting_tx_hex, 0)
        txid = int(txid, 16)

        # Now spend each of those outputs individually
        for i in range(MAX_REPLACEMENT_LIMIT + 1):
            tx_i = CTransaction()
            tx_i.vin = [CTxIn(COutPoint(txid, i), nSequence=0)]
            tx_i.vout = [CTxOut(split_value - fee, DUMMY_P2WPKH_SCRIPT), CTxOut(fee)]
            tx_i_hex = tx_i.serialize().hex()
            self.nodes[0].sendrawtransaction(tx_i_hex, 0)

        # Now create doublespend of the whole lot; should fail.
        # Need a big enough fee to cover all spending transactions and have
        # a higher fee rate
        double_spend_value = (split_value - 100 * fee) * (MAX_REPLACEMENT_LIMIT + 1)
        inputs = []
        for i in range(MAX_REPLACEMENT_LIMIT + 1):
            inputs.append(CTxIn(COutPoint(txid, i), nSequence=0))
        double_tx = CTransaction()
        double_tx.vin = inputs
        double_tx.vout = [CTxOut(double_spend_value, CScript([b'a'])), CTxOut(int(split_value*(MAX_REPLACEMENT_LIMIT+1)-double_spend_value))]
        double_tx_hex = double_tx.serialize().hex()

        # This will raise an exception
        assert_raises_rpc_error(-26, "too many potential replacements", self.nodes[0].sendrawtransaction, double_tx_hex, 0)

        # If we remove an input, it should pass
        double_tx = CTransaction()
        double_tx.vin = inputs[0:-1]
        double_tx.vout = [CTxOut(double_spend_value, CScript([b'a'])), CTxOut(int(split_value*(MAX_REPLACEMENT_LIMIT)-double_spend_value))]
        double_tx_hex = double_tx.serialize().hex()
        self.nodes[0].sendrawtransaction(double_tx_hex, 0)

    def test_too_many_replacements_with_default_mempool_params(self):
        """
        Test rule 5 of BIP125 (do not allow replacements that cause more than 100
        evictions) without having to rely on non-default mempool parameters.

        In order to do this, create a number of "root" UTXOs, and then hang
        enough transactions off of each root UTXO to exceed the MAX_REPLACEMENT_LIMIT.
        Then create a conflicting RBF replacement transaction.
        """
        normal_node = self.nodes[1]
        wallet = MiniWallet(normal_node)
        wallet.rescan_utxos()
        # Clear mempools to avoid cross-node sync failure.
        for node in self.nodes:
            self.generate(node, 1)

        # This has to be chosen so that the total number of transactions can exceed
        # MAX_REPLACEMENT_LIMIT without having any one tx graph run into the descendant
        # limit; 10 works.
        num_tx_graphs = 10

        # (Number of transactions per graph, BIP125 rule 5 failure expected)
        cases = [
            # Test the base case of evicting fewer than MAX_REPLACEMENT_LIMIT
            # transactions.
            ((MAX_REPLACEMENT_LIMIT // num_tx_graphs) - 1, False),

            # Test hitting the rule 5 eviction limit.
            (MAX_REPLACEMENT_LIMIT // num_tx_graphs, True),
        ]

        for (txs_per_graph, failure_expected) in cases:
            self.log.debug(f"txs_per_graph: {txs_per_graph}, failure: {failure_expected}")
            # "Root" utxos of each txn graph that we will attempt to double-spend with
            # an RBF replacement.
            root_utxos = []

            # For each root UTXO, create a package that contains the spend of that
            # UTXO and `txs_per_graph` children tx.
            for graph_num in range(num_tx_graphs):
                root_utxos.append(wallet.get_utxo())

                optin_parent_tx = wallet.send_self_transfer_multi(
                    from_node=normal_node,
                    sequence=BIP125_SEQUENCE_NUMBER,
                    utxos_to_spend=[root_utxos[graph_num]],
                    num_outputs=txs_per_graph,
                )
                assert_equal(True, normal_node.getmempoolentry(optin_parent_tx['txid'])['bip125-replaceable'])
                new_utxos = optin_parent_tx['new_utxos']

                for utxo in new_utxos:
                    # Create spends for each output from the "root" of this graph.
                    child_tx = wallet.send_self_transfer(
                        from_node=normal_node,
                        utxo_to_spend=utxo,
                    )

                    assert normal_node.getmempoolentry(child_tx['txid'])

            num_txs_invalidated = len(root_utxos) + (num_tx_graphs * txs_per_graph)

            if failure_expected:
                assert num_txs_invalidated > MAX_REPLACEMENT_LIMIT
            else:
                assert num_txs_invalidated <= MAX_REPLACEMENT_LIMIT

            # Now attempt to submit a tx that double-spends all the root tx inputs, which
            # would invalidate `num_txs_invalidated` transactions.
            double_tx = wallet.create_self_transfer_multi(
                utxos_to_spend=root_utxos,
                fee_per_output=10_000_000,  # absurdly high feerate
            )
            tx_hex = double_tx.serialize().hex()

            if failure_expected:
                assert_raises_rpc_error(
                    -26, "too many potential replacements", normal_node.sendrawtransaction, tx_hex, 0)
            else:
                txid = normal_node.sendrawtransaction(tx_hex, 0)
                assert normal_node.getmempoolentry(txid)

        # Clear the mempool once finished, and rescan the other nodes' wallet
        # to account for the spends we've made on `normal_node`.
        self.generate(normal_node, 1)
        self.wallet.rescan_utxos()

    def test_opt_in(self):
        """Replacing should only work if orig tx opted in"""
        tx0_outpoint = self.make_utxo(self.nodes[0], int(1.1 * COIN))

        # Create a non-opting in transaction
        tx1a = CTransaction()
        tx1a.vin = [CTxIn(tx0_outpoint, nSequence=SEQUENCE_FINAL)]
        tx1a.vout = [CTxOut(1 * COIN, DUMMY_P2WPKH_SCRIPT), CTxOut(int(0.1*COIN))]
        tx1a_hex = tx1a.serialize().hex()
        tx1a_txid = self.nodes[0].sendrawtransaction(tx1a_hex, 0)

        # This transaction isn't shown as replaceable
        assert_equal(self.nodes[0].getmempoolentry(tx1a_txid)['bip125-replaceable'], False)

        # Shouldn't be able to double-spend
        tx1b = CTransaction()
        tx1b.vin = [CTxIn(tx0_outpoint, nSequence=0)]
        tx1b.vout = [CTxOut(int(0.9 * COIN), DUMMY_P2WPKH_SCRIPT)]
        tx1b_hex = tx1b.serialize().hex()

        # This will raise an exception
        assert_raises_rpc_error(-26, "txn-mempool-conflict", self.nodes[0].sendrawtransaction, tx1b_hex, 0)

        tx1_outpoint = self.make_utxo(self.nodes[0], int(1.1 * COIN))

        # Create a different non-opting in transaction
        tx2a = CTransaction()
        tx2a.vin = [CTxIn(tx1_outpoint, nSequence=0xfffffffe)]
        tx2a.vout = [CTxOut(1 * COIN, DUMMY_P2WPKH_SCRIPT), CTxOut(int(0.1*COIN))]
        tx2a_hex = tx2a.serialize().hex()
        tx2a_txid = self.nodes[0].sendrawtransaction(tx2a_hex, 0)

        # Still shouldn't be able to double-spend
        tx2b = CTransaction()
        tx2b.vin = [CTxIn(tx1_outpoint, nSequence=0)]
        tx2b.vout = [CTxOut(int(0.9 * COIN), DUMMY_P2WPKH_SCRIPT)]
        tx2b_hex = tx2b.serialize().hex()

        # This will raise an exception
        assert_raises_rpc_error(-26, "txn-mempool-conflict", self.nodes[0].sendrawtransaction, tx2b_hex, 0)

        # Now create a new transaction that spends from tx1a and tx2a
        # opt-in on one of the inputs
        # Transaction should be replaceable on either input

        tx1a_txid = int(tx1a_txid, 16)
        tx2a_txid = int(tx2a_txid, 16)

        tx3a = CTransaction()
        tx3a.vin = [CTxIn(COutPoint(tx1a_txid, 0), nSequence=SEQUENCE_FINAL),
                    CTxIn(COutPoint(tx2a_txid, 0), nSequence=0xfffffffd)]
        tx3a.vout = [CTxOut(int(0.9 * COIN), CScript([b'c'])), CTxOut(int(0.9 * COIN), CScript([b'd']))]
        tx3a.vout.append(CTxOut(int(0.2 * COIN)))
        tx3a_hex = tx3a.serialize().hex()

        tx3a_txid = self.nodes[0].sendrawtransaction(tx3a_hex, 0)

        # This transaction is shown as replaceable
        assert_equal(self.nodes[0].getmempoolentry(tx3a_txid)['bip125-replaceable'], True)

        tx3b = CTransaction()
        tx3b.vin = [CTxIn(COutPoint(tx1a_txid, 0), nSequence=0)]
        tx3b.vout = [CTxOut(int(0.5 * COIN), DUMMY_P2WPKH_SCRIPT), CTxOut(int(0.5*COIN))]
        tx3b_hex = tx3b.serialize().hex()

        tx3c = CTransaction()
        tx3c.vin = [CTxIn(COutPoint(tx2a_txid, 0), nSequence=0)]
        tx3c.vout = [CTxOut(int(0.5 * COIN), DUMMY_P2WPKH_SCRIPT), CTxOut(int(0.5*COIN))]
        tx3c_hex = tx3c.serialize().hex()

        self.nodes[0].sendrawtransaction(tx3b_hex, 0)
        # If tx3b was accepted, tx3c won't look like a replacement,
        # but make sure it is accepted anyway
        self.nodes[0].sendrawtransaction(tx3c_hex, 0)

    def test_prioritised_transactions(self):
        # Ensure that fee deltas used via prioritisetransaction are
        # correctly used by replacement logic

        # 1. Check that feeperkb uses modified fees
        tx0_outpoint = self.make_utxo(self.nodes[0], int(1.1 * COIN))

        tx1a = CTransaction()
        tx1a.vin = [CTxIn(tx0_outpoint, nSequence=0)]
        tx1a.vout = [CTxOut(1 * COIN, DUMMY_P2WPKH_SCRIPT), CTxOut(int(0.1*COIN))]
        tx1a_hex = tx1a.serialize().hex()
        tx1a_txid = self.nodes[0].sendrawtransaction(tx1a_hex, 0)

        # Higher fee, but the actual fee per KB is much lower.
        tx1b = CTransaction()
        tx1b.vin = [CTxIn(tx0_outpoint, nSequence=0)]
        tx1b.vout = [CTxOut(int(0.001 * COIN), CScript([b'a' * 740000])), CTxOut(int(1.1 * COIN - 0.001 * COIN))]
        tx1b_hex = tx1b.serialize().hex()

        # Verify tx1b cannot replace tx1a.
        assert_raises_rpc_error(-26, "insufficient fee", self.nodes[0].sendrawtransaction, tx1b_hex, 0)

        # Use prioritisetransaction to set tx1a's fee to 0.
        self.nodes[0].prioritisetransaction(txid=tx1a_txid, fee_delta=int(-0.1 * COIN))

        # Now tx1b should be able to replace tx1a
        tx1b_txid = self.nodes[0].sendrawtransaction(tx1b_hex, 0)

        assert tx1b_txid in self.nodes[0].getrawmempool()

        # 2. Check that absolute fee checks use modified fee.
        tx1_outpoint = self.make_utxo(self.nodes[0], int(1.1 * COIN))

        tx2a = CTransaction()
        tx2a.vin = [CTxIn(tx1_outpoint, nSequence=0)]
        tx2a.vout = [CTxOut(1 * COIN, DUMMY_P2WPKH_SCRIPT), CTxOut(int(0.1*COIN))]
        tx2a_hex = tx2a.serialize().hex()
        self.nodes[0].sendrawtransaction(tx2a_hex, 0)

        # Lower fee, but we'll prioritise it
        tx2b = CTransaction()
        tx2b.vin = [CTxIn(tx1_outpoint, nSequence=0)]
        tx2b.vout = [CTxOut(int(1.01 * COIN), DUMMY_P2WPKH_SCRIPT), CTxOut(int(1.1*COIN-1.01*COIN))]
        tx2b.rehash()
        tx2b_hex = tx2b.serialize().hex()

        # Verify tx2b cannot replace tx2a.
        assert_raises_rpc_error(-26, "insufficient fee", self.nodes[0].sendrawtransaction, tx2b_hex, 0)

        # Now prioritise tx2b to have a higher modified fee
        self.nodes[0].prioritisetransaction(txid=tx2b.hash, fee_delta=int(0.1 * COIN))

        # tx2b should now be accepted
        tx2b_txid = self.nodes[0].sendrawtransaction(tx2b_hex, 0)

        assert tx2b_txid in self.nodes[0].getrawmempool()

    def test_rpc(self):
        us0 = self.wallet.get_utxo()
        ins = [us0]
        outs = [{ADDRESS_BCRT1_UNSPENDABLE: Decimal(1.0000000)}]
        outs.append({"fee": us0["amount"] - Decimal(1.0000000)})
        rawtx0 = self.nodes[0].createrawtransaction(ins, outs, 0, True)
        rawtx1 = self.nodes[0].createrawtransaction(ins, outs, 0, False)
        json0 = self.nodes[0].decoderawtransaction(rawtx0)
        json1 = self.nodes[0].decoderawtransaction(rawtx1)
        assert_equal(json0["vin"][0]["sequence"], 4294967293)
        assert_equal(json1["vin"][0]["sequence"], 4294967295)

        if self.is_specified_wallet_compiled():
            self.init_wallet(node=0)
            rawtx2 = self.nodes[0].createrawtransaction([], outs)
            frawtx2a = self.nodes[0].fundrawtransaction(rawtx2, {"replaceable": True})
            frawtx2b = self.nodes[0].fundrawtransaction(rawtx2, {"replaceable": False})

            json0 = self.nodes[0].decoderawtransaction(frawtx2a['hex'])
            json1 = self.nodes[0].decoderawtransaction(frawtx2b['hex'])
            assert_equal(json0["vin"][0]["sequence"], 4294967293)
            assert_equal(json1["vin"][0]["sequence"], 4294967294)

    def test_no_inherited_signaling(self):
        confirmed_utxo = self.wallet.get_utxo()

        # Create an explicitly opt-in parent transaction
        optin_parent_tx = self.wallet.send_self_transfer(
            from_node=self.nodes[0],
            utxo_to_spend=confirmed_utxo,
            sequence=BIP125_SEQUENCE_NUMBER,
            fee_rate=Decimal('0.01'),
        )
        assert_equal(True, self.nodes[0].getmempoolentry(optin_parent_tx['txid'])['bip125-replaceable'])

        replacement_parent_tx = self.wallet.create_self_transfer(
            utxo_to_spend=confirmed_utxo,
            sequence=BIP125_SEQUENCE_NUMBER,
            fee_rate=Decimal('0.02'),
        )

        # Test if parent tx can be replaced.
        res = self.nodes[0].testmempoolaccept(rawtxs=[replacement_parent_tx['hex']])[0]

        # Parent can be replaced.
        assert_equal(res['allowed'], True)

        # Create an opt-out child tx spending the opt-in parent
        parent_utxo = self.wallet.get_utxo(txid=optin_parent_tx['txid'])
        optout_child_tx = self.wallet.send_self_transfer(
            from_node=self.nodes[0],
            utxo_to_spend=parent_utxo,
            sequence=SEQUENCE_FINAL,
            fee_rate=Decimal('0.01'),
        )

        # Reports true due to inheritance
        assert_equal(True, self.nodes[0].getmempoolentry(optout_child_tx['txid'])['bip125-replaceable'])

        replacement_child_tx = self.wallet.create_self_transfer(
            utxo_to_spend=parent_utxo,
            sequence=SEQUENCE_FINAL,
            fee_rate=Decimal('0.02'),
        )

        # Broadcast replacement child tx
        # BIP 125 :
        # 1. The original transactions signal replaceability explicitly or through inheritance as described in the above
        # Summary section.
        # The original transaction (`optout_child_tx`) doesn't signal RBF but its parent (`optin_parent_tx`) does.
        # The replacement transaction (`replacement_child_tx`) should be able to replace the original transaction.
        # See CVE-2021-31876 for further explanations.
        assert_equal(True, self.nodes[0].getmempoolentry(optin_parent_tx['txid'])['bip125-replaceable'])
        assert_raises_rpc_error(-26, 'txn-mempool-conflict', self.nodes[0].sendrawtransaction, replacement_child_tx["hex"], 0)

        self.log.info('Check that the child tx can still be replaced (via a tx that also replaces the parent)')
        replacement_parent_tx = self.wallet.send_self_transfer(
            from_node=self.nodes[0],
            utxo_to_spend=confirmed_utxo,
            sequence=SEQUENCE_FINAL,
            fee_rate=Decimal('0.03'),
        )
        # Check that child is removed and update wallet utxo state
        assert_raises_rpc_error(-5, 'Transaction not in mempool', self.nodes[0].getmempoolentry, optout_child_tx['txid'])
        self.wallet.get_utxo(txid=optout_child_tx['txid'])

    def test_replacement_relay_fee(self):
        tx = self.wallet.send_self_transfer(from_node=self.nodes[0])['tx']

        # Higher fee, higher feerate, different txid, but the replacement does not provide a relay
        # fee conforming to node's `incrementalrelayfee` policy of 1000 sat per KB.
        assert_equal(self.nodes[0].getmempoolinfo()["incrementalrelayfee"], Decimal("0.00001"))
        tx.vout[0].nValue = CTxOutValue(tx.vout[0].nValue.getAmount() - 1)
        tx.vout[1].nValue = CTxOutValue(tx.vout[1].nValue.getAmount() + 1)
        assert_raises_rpc_error(-26, "insufficient fee", self.nodes[0].sendrawtransaction, tx.serialize().hex())

if __name__ == '__main__':
    ReplaceByFeeTest().main()
