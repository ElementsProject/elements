#!/usr/bin/env python3
# Copyright (c) 2020-2022 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Test mempool descendants/ancestors information update.

Test mempool update of transaction descendants/ancestors information (count, size)
when transactions have been re-added from a disconnected block to the mempool.
"""
import time

from decimal import Decimal
from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import assert_equal
from test_framework.address import key_to_p2pkh
from test_framework.wallet_util import bytes_to_wif
from test_framework.key import ECKey


class MempoolUpdateFromBlockTest(BitcoinTestFramework):
    def set_test_params(self):
        self.num_nodes = 1
        # ELEMENTS: limitancestorsize needs to be a bit larger than bitcoin because elements transactions are larger
        # 1000 is the default for bitcoin, so we set it to 1100 to account for the larger elements transactions
        self.extra_args = [['-limitdescendantsize=1000', '-limitancestorsize=1100', '-limitancestorcount=100']]

    def get_new_address(self):
        key = ECKey()
        key.generate()
        pubkey = key.get_pubkey().get_bytes()
        address = key_to_p2pkh(pubkey)
        self.priv_keys.append(bytes_to_wif(key.get_bytes()))
        return address

    def transaction_graph_test(self, size, n_tx_to_mine=None, start_input_txid='', end_address='', fee=Decimal(0.00100000)):
        """Create an acyclic tournament (a type of directed graph) of transactions and use it for testing.

        Keyword arguments:
        size -- the order N of the tournament which is equal to the number of the created transactions
        n_tx_to_mine -- the number of transaction that should be mined into a block

        If all of the N created transactions tx[0]..tx[N-1] reside in the mempool,
        the following holds:
            the tx[K] transaction:
            - has N-K descendants (including this one), and
            - has K+1 ancestors (including this one)

        More details: https://en.wikipedia.org/wiki/Tournament_(graph_theory)
        """

        self.priv_keys = [self.nodes[0].get_deterministic_priv_key().key]
        if not start_input_txid:
            start_input_txid = self.nodes[0].getblock(self.nodes[0].getblockhash(1))['tx'][0]

        if not end_address:
            end_address = self.get_new_address()

        first_block_hash = ''
        tx_id = []
        tx_size = []
        self.log.info('Creating {} transactions...'.format(size))
        for i in range(0, size):
            self.log.debug('Preparing transaction #{}...'.format(i))
            # Prepare inputs.
            if i == 0:
                inputs = [{'txid': start_input_txid, 'vout': 0}]
                inputs_value = self.nodes[0].gettxout(start_input_txid, 0)['value']
            else:
                inputs = []
                inputs_value = 0
                for j, tx in enumerate(tx_id[0:i]):
                    # Transaction tx[K] is a child of each of previous transactions tx[0]..tx[K-1] at their output K-1.
                    vout = i - j - 1
                    inputs.append({'txid': tx_id[j], 'vout': vout})
                    inputs_value += self.nodes[0].gettxout(tx, vout)['value']

            self.log.debug('inputs={}'.format(inputs))
            self.log.debug('inputs_value={}'.format(inputs_value))

            # Prepare outputs.
            tx_count = i + 1
            outputs_value = 0
            if tx_count < size:
                # Transaction tx[K] is an ancestor of each of subsequent transactions tx[K+1]..tx[N-1].
                n_outputs = size - tx_count
                output_value = ((inputs_value - fee) / Decimal(n_outputs)).quantize(Decimal('0.00000001'))
                outputs = []
                for _ in range(n_outputs):
                    outputs_value += output_value
                    outputs.append({self.get_new_address(): output_value})
            else:
                output_value = (inputs_value - fee).quantize(Decimal('0.00000001'))
                outputs_value += output_value
                outputs = [{end_address: output_value}]
            outputs.append({'fee': (inputs_value - outputs_value).quantize(Decimal('0.00000001'))})

            self.log.debug('outputs_value={}'.format(outputs_value))
            self.log.debug('output_value={}'.format(output_value))
            self.log.debug('outputs={}'.format(outputs))

            # Create a new transaction.
            unsigned_raw_tx = self.nodes[0].createrawtransaction(inputs, outputs)
            signed_raw_tx = self.nodes[0].signrawtransactionwithkey(unsigned_raw_tx, self.priv_keys)
            tx_id.append(self.nodes[0].sendrawtransaction(signed_raw_tx['hex']))
            tx_size.append(self.nodes[0].getmempoolentry(tx_id[-1])['vsize'])

            if tx_count in n_tx_to_mine:
                # The created transactions are mined into blocks by batches.
                self.log.info('The batch of {} transactions has been accepted into the mempool.'.format(len(self.nodes[0].getrawmempool())))
                block_hash = self.generate(self.nodes[0], 1)[0]
                if not first_block_hash:
                    first_block_hash = block_hash
                assert_equal(len(self.nodes[0].getrawmempool()), 0)
                self.log.info('All of the transactions from the current batch have been mined into a block.')
            elif tx_count == size:
                # At the end all of the mined blocks are invalidated, and all of the created
                # transactions should be re-added from disconnected blocks to the mempool.
                self.log.info('The last batch of {} transactions has been accepted into the mempool.'.format(len(self.nodes[0].getrawmempool())))
                start = time.time()

                self.nodes[0].invalidateblock(first_block_hash)

                end = time.time()

                assert_equal(len(self.nodes[0].getrawmempool()), size)
                self.log.info('All of the recently mined transactions have been re-added into the mempool in {} seconds.'.format(end - start))

        self.log.info('Checking descendants/ancestors properties of all of the in-mempool transactions...')
        for k, tx in enumerate(tx_id):
            self.log.debug('Check transaction #{}.'.format(k))
            entry = self.nodes[0].getmempoolentry(tx)
            assert_equal(entry['descendantcount'], size - k)
            assert_equal(entry['descendantsize'], sum(tx_size[k:size]))
            assert_equal(entry['ancestorcount'], k + 1)
            assert_equal(entry['ancestorsize'], sum(tx_size[0:(k + 1)]))

    def run_test(self):
        # Use batch size limited by DEFAULT_ANCESTOR_LIMIT = 25 to not fire "too many unconfirmed parents" error.
        self.transaction_graph_test(size=100, n_tx_to_mine=[25, 50, 75])


if __name__ == '__main__':
    MempoolUpdateFromBlockTest().main()
