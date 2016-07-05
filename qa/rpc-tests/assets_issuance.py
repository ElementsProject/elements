#!/usr/bin/env python2
try:
    # alpha
    from test_framework import BitcoinTestFramework
    from bitcoinrpc.authproxy import AuthServiceProxy, JSONRPCException
    import util
    BETA_MODULES = False
except ImportError:
    # beta
    from test_framework.test_framework import BitcoinTestFramework
    from test_framework.authproxy import AuthServiceProxy, JSONRPCException
    from test_framework import util
    BETA_MODULES = True

# ------ BEGIN MONKEY PATCHES
def initialize_datadir(dirname, n):
    datadir = os.path.join(dirname, "node"+str(n))
    if not os.path.isdir(datadir):
        os.makedirs(datadir)
    with open(os.path.join(datadir, "bitcoin.conf"), 'w') as f:
        f.write("regtest=1\n");
        f.write("testnet=0\n");
        f.write("rpcuser=rt\n");
        f.write("rpcpassword=rt\n");
        f.write("port="+str(p2p_port(n))+"\n");
        f.write("rpcport="+str(rpc_port(n))+"\n");
    return datadir
BETA = False
def log_filename(dirname, n_node, logname):
    global BETA
    return os.path.join(
        dirname,
        "node"+str(n_node),
        "assetsregtest" if BETA else "alpharegtest",
        logname
    )
util.initialize_datadir = initialize_datadir
util.log_filename = log_filename
# ------ END MONKEY PATCHES

if BETA_MODULES:
    from test_framework.util import *
else:
    from util import *
import os
import subprocess
import shutil


def call_bitcoin_tx(*args):
    name = os.environ['BITCOINTX']
    (stdout, stderr) = subprocess.Popen(
        [name] + ["-regtest=1", "-testnet=0"] + list(args),
        stdout=subprocess.PIPE, stderr=subprocess.PIPE
    ).communicate()
    if stderr:
        print '%s failed: %s' % (name, stderr)
        assert False
    return stdout.strip()

class AssetsIssuanceTest(BitcoinTestFramework):

    def setup_chain(self):
        # set the global var for monkey patches above:
        global BETA
        BETA = self.options.beta

        # update env vars for util.py:
        bitcoind = 'betad' if self.options.beta else 'alphad'
        bitcoincli = 'beta-cli' if self.options.beta else 'alpha-cli'
        bitcointx = 'beta-tx' if self.options.beta else 'alpha-tx'
        print ('Setting BITCOIND, BITCOINCLI and BITCOINTX env vars to ' \
               '"%s", "%s" and "%s".' % (
            bitcoind, bitcoincli, bitcointx
        ))
        os.environ['BITCOIND'] = bitcoind
        os.environ['BITCOINCLI'] = bitcoincli
        os.environ['BITCOINTX'] = bitcointx

        # setup either the default chain or simple empty data directory
        if self.options.setup_chain:
            super(AssetsIssuanceTest, self).setup_chain()
        else:
            if not os.path.isdir(os.path.join("cache", "node0")):
                # Create cache directories, run bitcoinds:
                datadir = initialize_datadir("cache", 0)

            from_dir = os.path.join("cache", "node0")
            to_dir = os.path.join(self.options.tmpdir, "node0")
            shutil.copytree(from_dir, to_dir)
            # Overwrite port/rpcport in bitcoin.conf:
            initialize_datadir(self.options.tmpdir, 0)

    def add_options(self, parser):
        parser.add_option(
            "--beta", dest="beta", default=False, action="store_true",
            help="Run tests for beta (0.12-assets) instead of alpha "
                 "(alpha-0.10-multi-asset)"
        )
        # FIXME: this is just a workaround for the node crashing on restart
        # (--setup-chain should probably be the only case supported when it's
        #  fixed)
        parser.add_option(
            "--setup-chain", dest="setup_chain", default=False,
            action="store_true",
            help=("Also try to run the default test framework initialization "
                  "with 4 cached nodes instead of generating one from scratch "
                  "on each run (currently both alpha and beta fail when cache"
                  "is used due to some block db inconsistencies)")
        )

    def setup_network(self):
        # Just need one node for this test
        args = ["-regtest=1", "-testnet=0"]
        self.nodes = []
        self.nodes.append(start_node(0, self.options.tmpdir, args))
        self.is_network_split = False

        if not self.options.setup_chain:
            # Chain not set up by the test framework -- do it here.
            # Create a 200-block-long chain;
            # blocks are created with timestamps 10 minutes apart, starting
            # at 1 Jan 2014
            block_time = 1388534400
            for i in range(2):
                for j in range(100):
                    set_node_times(self.nodes, block_time)
                    if self.options.beta:
                        self.nodes[0].generate(1)
                    else:
                        self.nodes[0].setgenerate(True, 1)
                    block_time += 10 * 60
                # Must sync before next peer starts generating blocks
                sync_blocks(self.nodes)

    def create_tx(self, from_txid, to_address, amount):
        inputs = [{ "txid" : from_txid, "vout" : 0}]
        outputs = { to_address : amount }
        rawtx = self.nodes[0].createrawtransaction(inputs, outputs)
        signresult = self.nodes[0].signrawtransaction(rawtx)
        assert_equal(signresult["complete"], True)
        return signresult["hex"]

    def run_test(self):
        chain_height = self.nodes[0].getblockcount()
        assert_equal(chain_height, 200)

        # 1. Get a CT addr. For simplicity of these tests we convert it to
        #    a non-CT address below.
        # FIXME: test with CT too
        ct_addr = self.nodes[0].getnewaddress()

        if self.options.beta:
            genesis_hash_hex = '3a7fb786c8b4bc814c8eb64029555afd686c406f3c15f80d667831192da524a0'
            genesis_tx_hex = '6542aec5da9ee5130865b7e31eaa056bcbbf4b39bf46d8317c8d712a1d1b8e1e'
        else:
            genesis_hash_hex = '095cdb4b50450887a3fba5fa77bdd7ce969868b78e2e7a75886d8e324c9e331d'
            genesis_tx_hex = '391520a77b69186b518aea58ab6c0aba64fa9b167fa102b7971074011873c87a'

        some_random_p2sh = '2NAe7WLuaDtK9ddfybFPS4dry7kqRaAr6HM'



        # 2. Prepare helper values for supporting alpha/beta together
        # Differences in Beta from the Alpha case:
        # (a) Sequence is not an argument for "in=".
        # (b) The input value for genesis transaction is 210k, not 10.5M,
        #     because the beta genesis tx has 100 outputs intead of 2.
        seq_option = '' if self.options.beta else ':0'
        amount0 = '210000.00000000' if self.options.beta else '10500000.0000'
        amount1 = '209999.99990000' if self.options.beta else '10499999.9999'
        amount2 = '209999.99980000' if self.options.beta else '10499999.9998'
        amount3 = '209990.99970000' if self.options.beta else '10499990.9997'

        # 3. Lame way of getting non-CT addr (via bitcoin-tx + decoderawtx)
        ct_raw_tx = call_bitcoin_tx(
            '-create',
            'newasset=1',
            'outaddr=%s:%s:%s' % (amount1, ct_addr, genesis_hash_hex),
            'outaddr=111:%s:0000000000000000000000000000000000000000000000000000000000000000' % some_random_p2sh,
            'in=%s:1:%s%s:%s' % (genesis_tx_hex, amount0, seq_option, genesis_hash_hex)
        )
        decoded_ct_raw_tx = self.nodes[0].decoderawtransaction(
            ct_raw_tx.strip()
        )
        non_ct_addr = decoded_ct_raw_tx['vout'][0]['scriptPubKey']['addresses'][0]

        # 4. Issue the first asset:
        asset1_tx = call_bitcoin_tx(
            '-create',
            'newasset=1',
            'outaddr=%s:%s:%s' % (amount1, non_ct_addr, genesis_hash_hex),
            'outaddr=111:%s:0000000000000000000000000000000000000000000000000000000000000000' % some_random_p2sh,
            'in=%s:1:%s%s:%s' % (genesis_tx_hex, amount0, seq_option, genesis_hash_hex)
        )
        # Send the first tx
        # (no signature required because it's spending the OP_TRUE):
        asset1_txhash = self.nodes[0].sendrawtransaction(asset1_tx)

        # 5. Issue the second asset:
        asset2_tx = call_bitcoin_tx(
            '-create',
            'newasset=1',
            'outaddr=%s:%s:%s' % (amount2, non_ct_addr, genesis_hash_hex),
            'outaddr=222:%s:0000000000000000000000000000000000000000000000000000000000000000' % some_random_p2sh,
            'in=%s:0:%s%s:%s' % (asset1_txhash, amount1, seq_option, genesis_hash_hex)
        )
        asset2_tx = self.nodes[0].signrawtransaction(asset2_tx)['hex']
        # Send the second tx
        asset2_txhash = self.nodes[0].sendrawtransaction(asset2_tx)


        # 6. Send some feeasset:
        feeasset_tx = call_bitcoin_tx(
            '-create',
            'outaddr=%s:%s:%s' % (amount3, non_ct_addr, genesis_hash_hex),
            'outaddr=9:%s:%s' % (some_random_p2sh, genesis_hash_hex),
            'in=%s:0:%s%s:%s' % (asset2_txhash, amount2, seq_option, genesis_hash_hex)
        )
        feeasset_tx = self.nodes[0].signrawtransaction(feeasset_tx)['hex']
        # Send the second tx
        feeasset_txhash = self.nodes[0].sendrawtransaction(feeasset_tx)

        print 'Sent transactions:'
        print 'Asset 1:', asset1_txhash
        print 'Asset 2:', asset2_txhash
        print 'Feeasset:', feeasset_txhash
        print 'Checking mempoool.'

        # 7. Check the mempool:
        mempool = self.nodes[0].getrawmempool()
        def assert_contains(container, item):
            if item not in container:
                raise AssertionError("%s not in %s"%(str(item),str(container)))
        for txhash in [asset1_txhash, asset2_txhash, feeasset_txhash]:
            assert_contains(mempool, txhash)

        # 8. Try confirming: (Currently it fails.)
        if self.options.beta:
            self.nodes[0].generate(1)
        else:
            self.nodes[0].setgenerate(True, 1)


if __name__ == '__main__':
    AssetsIssuanceTest().main()
