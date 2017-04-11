#!/usr/bin/env python2
# Copyright (c) 2014 The Bitcoin Core developers
# Distributed under the MIT/X11 software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

"""
Exercise the wallet backup code.  Ported from walletbackup.sh.

Test case is:
4 nodes. 1 2 and 3 send transactions between each other,
fourth node is a miner.
1 2 3 each mine a block to start, then
5 iterations of 1/2/3 sending coins amongst
themselves to get transactions in the wallets,
and the miner mining one block.

Wallets are backed up using dumpwallet/backupwallet.

Miner then generates 101 more blocks, so any
transaction fees paid mature.

Sanity check:
  Sum(1,2,3,4 balances) == genesis_balance

1/2/3 are shutdown, and their wallets erased.
Then restore using wallet.dat backup. And
confirm 1/2/3/4 balances are same as before.

Shutdown again, restore using importwallet,
and confirm again balances are correct.
"""

from test_framework import BitcoinTestFramework
from util import *
from random import randint
import logging
logging.basicConfig(format='%(levelname)s:%(message)s', level=logging.INFO)

class WalletBackupTest(BitcoinTestFramework):

    def setup_chain(self):
        logging.info("Initializing test directory "+self.options.tmpdir)
        initialize_chain_clean(self.options.tmpdir, 4)

    # This mirrors how the network was setup in the bash test
    def setup_network(self, split=False):
        # nodes 1, 2,3 are spenders, let's give them a keypool=100
        extra_args = [["-keypool=100"], ["-keypool=100"], ["-keypool=100"], []]
        self.nodes = start_nodes(4, self.options.tmpdir, extra_args)
        connect_nodes(self.nodes[0], 3)
        connect_nodes(self.nodes[1], 3)
        connect_nodes(self.nodes[2], 3)
        connect_nodes(self.nodes[2], 0)
        self.is_network_split=False
        self.sync_all()

    def one_send(self, from_node, to_address):
        if (randint(1,2) == 1):
            amount = Decimal(randint(1,10)) / Decimal(10)
            self.nodes[from_node].sendtoaddress(to_address, amount)

    def do_one_round(self):
        a0 = self.nodes[0].getnewaddress()
        a1 = self.nodes[1].getnewaddress()
        a2 = self.nodes[2].getnewaddress()

        self.one_send(0, a1)
        self.one_send(0, a2)
        self.one_send(1, a0)
        self.one_send(1, a2)
        self.one_send(2, a0)
        self.one_send(2, a1)

        # Have the miner (node3) mine a block.
        # Must sync mempools before mining.
        sync_mempools(self.nodes)
        self.nodes[3].setgenerate(True, 1)

    # As above, this mirrors the original bash test.
    def start_three(self):
        self.nodes[0] = start_node(0, self.options.tmpdir)
        self.nodes[1] = start_node(1, self.options.tmpdir)
        self.nodes[2] = start_node(2, self.options.tmpdir)
        connect_nodes(self.nodes[0], 3)
        connect_nodes(self.nodes[1], 3)
        connect_nodes(self.nodes[2], 3)
        connect_nodes(self.nodes[2], 0)

    def stop_three(self):
        stop_node(self.nodes[0], 0)
        stop_node(self.nodes[1], 1)
        stop_node(self.nodes[2], 2)

    def erase_three(self):
        os.remove(self.options.tmpdir + "/node0/alpharegtest/wallet.dat")
        os.remove(self.options.tmpdir + "/node1/alpharegtest/wallet.dat")
        os.remove(self.options.tmpdir + "/node2/alpharegtest/wallet.dat")

    def run_test(self):
        logging.info("Generating initial blockchain")
        self.nodes[0].setgenerate(True, 1)
        sync_blocks(self.nodes)

        genesis_balance = 10500000
        assert_equal(self.nodes[0].getbalance(), genesis_balance)
        assert_equal(self.nodes[1].getbalance(), genesis_balance)
        assert_equal(self.nodes[2].getbalance(), genesis_balance)
        assert_equal(self.nodes[3].getbalance(), genesis_balance)

        self.nodes[0].sendtoaddress(self.nodes[1].getnewaddress(), 50)
        self.nodes[0].sendtoaddress(self.nodes[2].getnewaddress(), 50)
        self.nodes[0].setgenerate(True, 101)
        self.sync_all()

        assert_equal(self.nodes[0].getbalance(), genesis_balance - 100)
        assert_equal(self.nodes[1].getbalance(), 50)
        assert_equal(self.nodes[2].getbalance(), 50)
        assert_equal(self.nodes[3].getbalance(), 0)


        logging.info("Creating transactions")
        # Five rounds of sending each other transactions.
        for i in range(5):
            self.do_one_round()

        logging.info("Backing up")
        tmpdir = self.options.tmpdir
        blinding_keys = [{}, {}, {}]

        def backup(i):
            self.nodes[i].backupwallet(tmpdir + "/node%s/wallet.bak" % i)
            self.nodes[i].dumpwallet(tmpdir + "/node%s/wallet.dump" % i)
            # Export blinding keys
            for addrs in self.nodes[i].listaddressgroupings():
                for addr in addrs:
                    blinding_keys[i][addr[0]] = self.nodes[i].dumpblindingkey(addr[0])
        backup(0)
        backup(1)
        backup(2)

        # Generate 101 more blocks, so any fees paid mature
        self.nodes[3].setgenerate(True, 101)
        self.sync_all()

        balance0 = self.nodes[0].getbalance()
        balance1 = self.nodes[1].getbalance()
        balance2 = self.nodes[2].getbalance()
        balance3 = self.nodes[3].getbalance()
        total = balance0 + balance1 + balance2 + balance3

        assert_equal(total, genesis_balance)

        ##
        # Test restoring spender wallets from backups
        ##
        logging.info("Restoring using wallet.dat")
        self.stop_three()
        self.erase_three()

        # Start node2 with no chain
        shutil.rmtree(self.options.tmpdir + "/node2/alpharegtest/blocks")
        shutil.rmtree(self.options.tmpdir + "/node2/alpharegtest/chainstate")

        # Restore wallets from backup
        shutil.copyfile(tmpdir + "/node0/wallet.bak", tmpdir + "/node0/alpharegtest/wallet.dat")
        shutil.copyfile(tmpdir + "/node1/wallet.bak", tmpdir + "/node1/alpharegtest/wallet.dat")
        shutil.copyfile(tmpdir + "/node2/wallet.bak", tmpdir + "/node2/alpharegtest/wallet.dat")

        logging.info("Re-starting nodes")
        self.start_three()
        sync_blocks(self.nodes)

        assert_equal(self.nodes[0].getbalance(), balance0)
        assert_equal(self.nodes[1].getbalance(), balance1)
        assert_equal(self.nodes[2].getbalance(), balance2)

        logging.info("Restoring using dumped wallet")
        self.stop_three()
        self.erase_three()

        #start node2 with no chain
        shutil.rmtree(self.options.tmpdir + "/node2/alpharegtest/blocks")
        shutil.rmtree(self.options.tmpdir + "/node2/alpharegtest/chainstate")

        self.start_three()

        assert_equal(self.nodes[0].getbalance(), genesis_balance)
        assert_equal(self.nodes[1].getbalance(), genesis_balance)
        assert_equal(self.nodes[2].getbalance(), 0)

        self.nodes[0].importwallet(tmpdir + "/node0/wallet.dump")
        self.nodes[1].importwallet(tmpdir + "/node1/wallet.dump")
        self.nodes[2].importwallet(tmpdir + "/node2/wallet.dump")

        # import blinding keys, one for for each address
        for i, per_node_keys in enumerate(blinding_keys):
            for addr in per_node_keys:
                self.nodes[i].importblindingkey(addr, per_node_keys[addr])

        sync_blocks(self.nodes)

        assert_equal(self.nodes[0].getbalance(), balance0)
        assert_equal(self.nodes[1].getbalance(), balance1)
        assert_equal(self.nodes[2].getbalance(), balance2)


if __name__ == '__main__':
    WalletBackupTest().main()
