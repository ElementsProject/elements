#!/usr/bin/env python3
# Copyright (c) 2014-2021 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Test descendant package tracking code."""

from decimal import Decimal

from test_framework.blocktools import COINBASE_MATURITY
from test_framework.messages import COIN
from test_framework.p2p import P2PTxInvStore
from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import (
    assert_equal,
    assert_greater_than,
    assert_raises_rpc_error,
    chain_transaction,
)
import time

# default limits
MAX_ANCESTORS = 25
MAX_DESCENDANTS = 25

# custom limits for node1
MAX_ANCESTORS_CUSTOM = 5
MAX_DESCENDANTS_CUSTOM = 10
assert MAX_DESCENDANTS_CUSTOM >= MAX_ANCESTORS_CUSTOM

class MempoolPackagesTest(BitcoinTestFramework):
    def set_test_params(self):
        self.num_nodes = 2
        self.extra_args = [
            [
                "-maxorphantx=1000",
                "-whitelist=noban@127.0.0.1",  # immediate tx relay
            ],
            [
                "-maxorphantx=1000",
                "-limitancestorcount={}".format(MAX_ANCESTORS_CUSTOM),
                "-limitdescendantcount={}".format(MAX_DESCENDANTS_CUSTOM),
            ],
        ]

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def run_test(self):

        # Create transaction with 3-second block delay, should fail to enter the template
        txid = self.nodes[0].sendtoaddress(self.nodes[0].getnewaddress(), 1)
        block = self.nodes[0].getnewblockhex(min_tx_age=3)
        self.nodes[0].submitblock(block)
        assert txid in self.nodes[0].getrawmempool()
        time.sleep(3)
        block = self.nodes[0].getnewblockhex(min_tx_age=3)
        self.nodes[0].submitblock(block)
        assert txid not in self.nodes[0].getrawmempool()
        # Once more with no delay (default is 0, just testing default arg)
        txid = self.nodes[0].sendtoaddress(self.nodes[0].getnewaddress(), 1)
        block = self.nodes[0].getnewblockhex(min_tx_age=0)
        self.nodes[0].submitblock(block)
        assert txid not in self.nodes[0].getrawmempool()
        assert_raises_rpc_error(-8, "min_tx_age must be non-negative.", self.nodes[0].getnewblockhex, -1)

        # Mine some blocks and have them mature.
        peer_inv_store = self.nodes[0].add_p2p_connection(P2PTxInvStore()) # keep track of invs
        self.generate(self.nodes[0], COINBASE_MATURITY + 1)
        utxos = []
        for utxo in self.nodes[0].listunspent(10):
            # Skip change/fees we scooped up
            if utxo['amount'] != Decimal(50):
                continue
            utxos.append(utxo)
        assert_greater_than(len(utxos), 1)

        txid = utxos[0]['txid']
        vout = utxos[0]['vout']
        value = utxos[0]['amount']
        assert 'ancestorcount' not in utxos[0]
        assert 'ancestorsize' not in utxos[0]
        assert 'ancestorfees' not in utxos[0]

        fee = Decimal("0.0001")
        # MAX_ANCESTORS transactions off a confirmed tx should be fine
        chain = []
        witness_chain = []
        ancestor_vsize = 0
        ancestor_fees = Decimal(0)
        for i in range(MAX_ANCESTORS):
            (txid, sent_value) = chain_transaction(self.nodes[0], [txid], [0], value, fee, 1)
            value = sent_value
            chain.append(txid)
            # We need the wtxids to check P2P announcements
            witnesstx = self.nodes[0].gettransaction(txid=txid, verbose=True)['decoded']
            witness_chain.append(witnesstx['hash'])

            # Check that listunspent ancestor{count, size, fees} yield the correct results
            wallet_unspent = self.nodes[0].listunspent(minconf=0)
            this_unspent = next(utxo_info for utxo_info in wallet_unspent if utxo_info['txid'] == txid)
            assert_equal(this_unspent['ancestorcount'], i + 1)
            ancestor_vsize += self.nodes[0].getrawtransaction(txid=txid, verbose=True)['vsize']
            assert_equal(this_unspent['ancestorsize'], ancestor_vsize)
            print(self.nodes[0].gettransaction(txid=txid))
            ancestor_fees -= self.nodes[0].gettransaction(txid=txid)['fee']['bitcoin']
            assert_equal(this_unspent['ancestorfees'], ancestor_fees * COIN)

        # Wait until mempool transactions have passed initial broadcast (sent inv and received getdata)
        # Otherwise, getrawmempool may be inconsistent with getmempoolentry if unbroadcast changes in between
        peer_inv_store.wait_for_broadcast(witness_chain)

        # Check mempool has MAX_ANCESTORS transactions in it, and descendant and ancestor
        # count and fees should look correct
        mempool = self.nodes[0].getrawmempool(True)
        assert_equal(len(mempool), MAX_ANCESTORS)
        descendant_count = 1
        descendant_fees = 0
        descendant_vsize = 0

        assert_equal(ancestor_vsize, sum([mempool[tx]['vsize'] for tx in mempool]))
        ancestor_count = MAX_ANCESTORS
        assert_equal(ancestor_fees, sum([mempool[tx]['fees']['base'] for tx in mempool]))

        descendants = []
        ancestors = list(chain)
        for x in reversed(chain):
            # Check that getmempoolentry is consistent with getrawmempool
            entry = self.nodes[0].getmempoolentry(x)
            assert_equal(entry, mempool[x])

            # Check that gettxspendingprevout is consistent with getrawmempool
            witnesstx = self.nodes[0].gettransaction(txid=x, verbose=True)['decoded']
            for tx_in in witnesstx["vin"]:
                spending_result = self.nodes[0].gettxspendingprevout([ {'txid' : tx_in["txid"], 'vout' : tx_in["vout"]} ])
                assert_equal(spending_result, [ {'txid' : tx_in["txid"], 'vout' : tx_in["vout"], 'spendingtxid' : x} ])

            # Check that the descendant calculations are correct
            assert_equal(entry['descendantcount'], descendant_count)
            descendant_fees += entry['fees']['base']
            assert_equal(entry['fees']['modified'], entry['fees']['base'])
            assert_equal(entry['fees']['descendant'], descendant_fees)
            descendant_vsize += entry['vsize']
            assert_equal(entry['descendantsize'], descendant_vsize)
            descendant_count += 1

            # Check that ancestor calculations are correct
            assert_equal(entry['ancestorcount'], ancestor_count)
            assert_equal(entry['fees']['ancestor'], ancestor_fees)
            assert_equal(entry['ancestorsize'], ancestor_vsize)
            ancestor_vsize -= entry['vsize']
            ancestor_fees -= entry['fees']['base']
            ancestor_count -= 1

            # Check that parent/child list is correct
            assert_equal(entry['spentby'], descendants[-1:])
            assert_equal(entry['depends'], ancestors[-2:-1])

            # Check that getmempooldescendants is correct
            assert_equal(sorted(descendants), sorted(self.nodes[0].getmempooldescendants(x)))

            # Check getmempooldescendants verbose output is correct
            for descendant, dinfo in self.nodes[0].getmempooldescendants(x, True).items():
                assert_equal(dinfo['depends'], [chain[chain.index(descendant)-1]])
                if dinfo['descendantcount'] > 1:
                    assert_equal(dinfo['spentby'], [chain[chain.index(descendant)+1]])
                else:
                    assert_equal(dinfo['spentby'], [])
            descendants.append(x)

            # Check that getmempoolancestors is correct
            ancestors.remove(x)
            assert_equal(sorted(ancestors), sorted(self.nodes[0].getmempoolancestors(x)))

            # Check that getmempoolancestors verbose output is correct
            for ancestor, ainfo in self.nodes[0].getmempoolancestors(x, True).items():
                assert_equal(ainfo['spentby'], [chain[chain.index(ancestor)+1]])
                if ainfo['ancestorcount'] > 1:
                    assert_equal(ainfo['depends'], [chain[chain.index(ancestor)-1]])
                else:
                    assert_equal(ainfo['depends'], [])


        # Check that getmempoolancestors/getmempooldescendants correctly handle verbose=true
        v_ancestors = self.nodes[0].getmempoolancestors(chain[-1], True)
        assert_equal(len(v_ancestors), len(chain)-1)
        for x in v_ancestors.keys():
            assert_equal(mempool[x], v_ancestors[x])
        assert chain[-1] not in v_ancestors.keys()

        v_descendants = self.nodes[0].getmempooldescendants(chain[0], True)
        assert_equal(len(v_descendants), len(chain)-1)
        for x in v_descendants.keys():
            assert_equal(mempool[x], v_descendants[x])
        assert chain[0] not in v_descendants.keys()

        # Check that ancestor modified fees includes fee deltas from
        # prioritisetransaction
        self.nodes[0].prioritisetransaction(txid=chain[0], fee_delta=1000)
        ancestor_fees = 0
        for x in chain:
            entry = self.nodes[0].getmempoolentry(x)
            ancestor_fees += entry['fees']['base']
            assert_equal(entry['fees']['ancestor'], ancestor_fees + Decimal('0.00001'))

        # Undo the prioritisetransaction for later tests
        self.nodes[0].prioritisetransaction(txid=chain[0], fee_delta=-1000)

        # Check that descendant modified fees includes fee deltas from
        # prioritisetransaction
        self.nodes[0].prioritisetransaction(txid=chain[-1], fee_delta=1000)

        descendant_fees = 0
        for x in reversed(chain):
            entry = self.nodes[0].getmempoolentry(x)
            descendant_fees += entry['fees']['base']
            assert_equal(entry['fees']['descendant'], descendant_fees + Decimal('0.00001'))

        # Adding one more transaction on to the chain should fail.
        assert_raises_rpc_error(-26, "too-long-mempool-chain", chain_transaction, self.nodes[0], [txid], [vout], value, fee, 1)

        # Check that prioritising a tx before it's added to the mempool works
        # First clear the mempool by mining a block.
        self.generate(self.nodes[0], 1)
        assert_equal(len(self.nodes[0].getrawmempool()), 0)
        # Prioritise a transaction that has been mined, then add it back to the
        # mempool by using invalidateblock.
        self.nodes[0].prioritisetransaction(txid=chain[-1], fee_delta=2000)
        self.nodes[0].invalidateblock(self.nodes[0].getbestblockhash())
        # Keep node1's tip synced with node0
        self.nodes[1].invalidateblock(self.nodes[1].getbestblockhash())

        # Now check that the transaction is in the mempool, with the right modified fee
        descendant_fees = 0
        for x in reversed(chain):
            entry = self.nodes[0].getmempoolentry(x)
            descendant_fees += entry['fees']['base']
            if (x == chain[-1]):
                assert_equal(entry['fees']['modified'], entry['fees']['base'] + Decimal("0.00002"))
            assert_equal(entry['fees']['descendant'], descendant_fees + Decimal("0.00002"))

        # Check that node1's mempool is as expected (-> custom ancestor limit)
        mempool0 = self.nodes[0].getrawmempool(False)
        mempool1 = self.nodes[1].getrawmempool(False)
        assert_equal(len(mempool1), MAX_ANCESTORS_CUSTOM)
        assert set(mempool1).issubset(set(mempool0))
        for tx in chain[:MAX_ANCESTORS_CUSTOM]:
            assert tx in mempool1
        # TODO: more detailed check of node1's mempool (fees etc.)
        # check transaction unbroadcast info (should be false if in both mempools)
        mempool = self.nodes[0].getrawmempool(True)
        for tx in mempool:
            assert_equal(mempool[tx]['unbroadcast'], False)

        # TODO: test ancestor size limits

        # Now test descendant chain limits
        txid = utxos[1]['txid']
        value = utxos[1]['amount']
        vout = utxos[1]['vout']

        transaction_package = []
        tx_children = []
        # First create one parent tx with 10 children
        (txid, sent_value) = chain_transaction(self.nodes[0], [txid], [vout], value, fee, 10)
        parent_transaction = txid
        for i in range(10):
            transaction_package.append({'txid': txid, 'vout': i, 'amount': sent_value})

        # Sign and send up to MAX_DESCENDANT transactions chained off the parent tx
        chain = [] # save sent txs for the purpose of checking node1's mempool later (see below)
        for _ in range(MAX_DESCENDANTS - 1):
            utxo = transaction_package.pop(0)
            (txid, sent_value) = chain_transaction(self.nodes[0], [utxo['txid']], [utxo['vout']], utxo['amount'], fee, 10)
            chain.append(txid)
            if utxo['txid'] is parent_transaction:
                tx_children.append(txid)
            for j in range(10):
                transaction_package.append({'txid': txid, 'vout': j, 'amount': sent_value})

        mempool = self.nodes[0].getrawmempool(True)
        assert_equal(mempool[parent_transaction]['descendantcount'], MAX_DESCENDANTS)
        assert_equal(sorted(mempool[parent_transaction]['spentby']), sorted(tx_children))

        for child in tx_children:
            assert_equal(mempool[child]['depends'], [parent_transaction])

        # Sending one more chained transaction will fail
        utxo = transaction_package.pop(0)
        assert_raises_rpc_error(-26, "too-long-mempool-chain", chain_transaction, self.nodes[0], [utxo['txid']], [utxo['vout']], utxo['amount'], fee, 10)

        # Check that node1's mempool is as expected, containing:
        # - txs from previous ancestor test (-> custom ancestor limit)
        # - parent tx for descendant test
        # - txs chained off parent tx (-> custom descendant limit)
        self.wait_until(lambda: len(self.nodes[1].getrawmempool()) ==
                                MAX_ANCESTORS_CUSTOM + 1 + MAX_DESCENDANTS_CUSTOM, timeout=10)
        mempool0 = self.nodes[0].getrawmempool(False)
        mempool1 = self.nodes[1].getrawmempool(False)
        assert set(mempool1).issubset(set(mempool0))
        assert parent_transaction in mempool1
        for tx in chain[:MAX_DESCENDANTS_CUSTOM]:
            assert tx in mempool1
        for tx in chain[MAX_DESCENDANTS_CUSTOM:]:
            assert tx not in mempool1
        # TODO: more detailed check of node1's mempool (fees etc.)

        # TODO: test descendant size limits

        # Test reorg handling
        # First, the basics:
        self.generate(self.nodes[0], 1)
        self.nodes[1].invalidateblock(self.nodes[0].getbestblockhash())
        self.nodes[1].reconsiderblock(self.nodes[0].getbestblockhash())

        # Now test the case where node1 has a transaction T in its mempool that
        # depends on transactions A and B which are in a mined block, and the
        # block containing A and B is disconnected, AND B is not accepted back
        # into node1's mempool because its ancestor count is too high.

        # Create 8 transactions, like so:
        # Tx0 -> Tx1 (vout0)
        #   \--> Tx2 (vout1) -> Tx3 -> Tx4 -> Tx5 -> Tx6 -> Tx7
        #
        # Mine them in the next block, then generate a new tx8 that spends
        # Tx1 and Tx7, and add to node1's mempool, then disconnect the
        # last block.

        # Create tx0 with 2 outputs
        utxo = self.nodes[0].listunspent()
        txid = utxo[0]['txid']
        value = utxo[0]['amount']
        vout = utxo[0]['vout']

        send_value = (value - fee) / 2
        inputs = [ {'txid' : txid, 'vout' : vout} ]
        outputs = []
        for _ in range(2):
            outputs.append({self.nodes[0].getnewaddress():send_value})
        outputs.append({"fee": fee})
        rawtx = self.nodes[0].createrawtransaction(inputs, outputs)
        signedtx = self.nodes[0].signrawtransactionwithwallet(rawtx)
        txid = self.nodes[0].sendrawtransaction(signedtx['hex'])
        tx0_id = txid
        value = send_value

        # Create tx1
        tx1_id, _ = chain_transaction(self.nodes[0], [tx0_id], [0], value, fee, 1)

        # Create tx2-7
        vout = 1
        txid = tx0_id
        for _ in range(6):
            (txid, sent_value) = chain_transaction(self.nodes[0], [txid], [vout], value, fee, 1)
            vout = 0
            value = sent_value

        # Mine these in a block
        self.generate(self.nodes[0], 1)

        # Now generate tx8, with a big fee
        inputs = [ {'txid' : tx1_id, 'vout': 0}, {'txid' : txid, 'vout': 0} ]
        outputs = [{ self.nodes[0].getnewaddress() : send_value + value - 4*fee }, {"fee": 3*fee}]
        rawtx = self.nodes[0].createrawtransaction(inputs, outputs)
        signedtx = self.nodes[0].signrawtransactionwithwallet(rawtx)
        txid = self.nodes[0].sendrawtransaction(signedtx['hex'])
        self.sync_mempools()

        # Now try to disconnect the tip on each node...
        self.nodes[1].invalidateblock(self.nodes[1].getbestblockhash())
        self.nodes[0].invalidateblock(self.nodes[0].getbestblockhash())
        self.sync_blocks()

if __name__ == '__main__':
    MempoolPackagesTest().main()
