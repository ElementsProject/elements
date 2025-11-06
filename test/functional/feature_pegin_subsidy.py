#!/usr/bin/env python3

# can be run with parent bitcoind node
# tested with bitcoind v28.2 and v29.0
# test/functional/feature_pegin_subsidy.py --parent_bitcoin --parent_binpath="/path/to/bitcoind" --nosandbox

from decimal import Decimal
from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import (
    assert_raises_rpc_error,
    find_vout_for_address,
    get_auth_cookie,
    get_datadir_path,
    rpc_port,
    p2p_port,
    assert_equal,
)
from test_framework import util

PEGIN_MINIMUM_HEIGHT = 102
PEGIN_SUBSIDY_HEIGHT = 150


def get_new_unconfidential_address(node, addr_type="bech32"):
    addr = node.getnewaddress("", addr_type)
    val_addr = node.getaddressinfo(addr)
    if "unconfidential" in val_addr:
        return val_addr["unconfidential"]
    return val_addr["address"]


class PeginSubsidyTest(BitcoinTestFramework):
    def set_test_params(self):
        self.setup_clean_chain = True
        self.num_nodes = 3
        self.disable_syscall_sandbox = True

    def add_options(self, parser):
        parser.add_argument(
            "--parent_binpath",
            dest="parent_binpath",
            default="",
            help="Use a different binary for launching nodes",
        )
        parser.add_argument(
            "--parent_bitcoin",
            dest="parent_bitcoin",
            default=False,
            action="store_true",
            help="Parent nodes are Bitcoin",
        )

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def setup_network(self, split=False):
        if self.options.parent_bitcoin and self.options.parent_binpath == "":
            raise Exception("Can't run with --parent_bitcoin without specifying --parent_binpath")

        self.nodes = []
        # Setup parent nodes
        parent_chain = "elementsregtest" if not self.options.parent_bitcoin else "regtest"
        parent_binary = [self.options.parent_binpath] if self.options.parent_binpath != "" else None

        extra_args = [
            "-port=" + str(p2p_port(0)),
            "-rpcport=" + str(rpc_port(0)),
            # to test minimum parent tx fee
            "-minrelaytxfee=0.00000100",
            "-blockmintxfee=0.00000100",
            "-mintxfee=0.00000100",
        ]
        if self.options.parent_bitcoin:
            # bitcoind can't read elements.conf config files
            extra_args.extend(
                [
                    "-regtest=1",
                    "-printtoconsole=0",
                    "-server=1",
                    "-discover=0",
                    "-keypool=1",
                    "-listenonion=0",
                    "-addresstype=legacy",  # To make sure bitcoind gives back p2pkh no matter version
                    "-fallbackfee=0.0002",
                    "-deprecatedrpc=create_bdb",
                ]
            )
            self.expected_stderr = (
                f"Error: Unable to bind to 127.0.0.1:{p2p_port(1)} on this computer. Elements Core is probably already running."
            )
        else:
            extra_args.extend(
                [
                    "-validatepegin=0",
                    "-initialfreecoins=0",
                    "-anyonecanspendaremine=1",
                    "-signblockscript=51",  # OP_TRUE
                    "-dustrelayfee=0.00003000",  # use the Bitcoin default dust relay fee rate for the parent nodes
                ]
            )
            self.expected_stderr = ""

        self.add_nodes(1, [extra_args], chain=[parent_chain], binary=parent_binary)
        self.start_node(0)
        self.log.info(f"Node 0 started (mainchain: {'bitcoind' if self.options.parent_bitcoin else 'elementsd'})")

        # set hard-coded mining keys for non-Elements chains
        if self.options.parent_bitcoin:
            self.nodes[0].set_deterministic_priv_key(
                "2Mysp7FKKe52eoC2JmU46irt1dt58TpCvhQ",
                "cTNbtVJmhx75RXomhYWSZAafuNNNKPd1cr2ZiUcAeukLNGrHWjvJ",
            )

        self.parentgenesisblockhash = self.nodes[0].getblockhash(0)
        if not self.options.parent_bitcoin:
            parent_pegged_asset = self.nodes[0].getsidechaininfo()["pegged_asset"]

        # Setup sidechain nodes
        # use the current liquidv1 fedpegscript for testing purposes
        self.fedpegscript = "5b21020e0338c96a8870479f2396c373cc7696ba124e8635d41b0ea581112b678172612102675333a4e4b8fb51d9d4e22fa5a8eaced3fdac8a8cbf9be8c030f75712e6af992102896807d54bc55c24981f24a453c60ad3e8993d693732288068a23df3d9f50d4821029e51a5ef5db3137051de8323b001749932f2ff0d34c82e96a2c2461de96ae56c2102a4e1a9638d46923272c266631d94d36bdb03a64ee0e14c7518e49d2f29bc401021031c41fdbcebe17bec8d49816e00ca1b5ac34766b91c9f2ac37d39c63e5e008afb2103079e252e85abffd3c401a69b087e590a9b86f33f574f08129ccbd3521ecf516b2103111cf405b627e22135b3b3733a4a34aa5723fb0f58379a16d32861bf576b0ec2210318f331b3e5d38156da6633b31929c5b220349859cc9ca3d33fb4e68aa08401742103230dae6b4ac93480aeab26d000841298e3b8f6157028e47b0897c1e025165de121035abff4281ff00660f99ab27bb53e6b33689c2cd8dcd364bc3c90ca5aea0d71a62103bd45cddfacf2083b14310ae4a84e25de61e451637346325222747b157446614c2103cc297026b06c71cbfa52089149157b5ff23de027ac5ab781800a578192d175462103d3bde5d63bdb3a6379b461be64dad45eabff42f758543a9645afd42f6d4248282103ed1e8d5109c9ed66f7941bc53cc71137baa76d50d274bda8d5e8ffbd6e61fe9a5fae736402c00fb269522103aab896d53a8e7d6433137bbba940f9c521e085dd07e60994579b64a6d992cf79210291b7d0b1b692f8f524516ed950872e5da10fb1b808b5a526dedc6fed1cf29807210386aa9372fbab374593466bc5451dc59954e90787f08060964d95c87ef34ca5bb53ae68"
        for n in range(2):
            validatepegin = "1" if n == 0 else "0"
            extra_args = [
                "-printtoconsole=0",
                "-port=" + str(p2p_port(1 + n)),
                "-rpcport=" + str(rpc_port(1 + n)),
                "-validatepegin=%s" % validatepegin,
                "-fallbackfee=0.00001000",
                "-fedpegscript=%s" % self.fedpegscript,
                "-minrelaytxfee=0",
                "-blockmintxfee=0",
                "-initialfreecoins=0",
                "-peginconfirmationdepth=10",
                "-mainchainrpchost=127.0.0.1",
                "-mainchainrpcport=%s" % rpc_port(0),
                "-parentgenesisblockhash=%s" % self.parentgenesisblockhash,
                "-parentpubkeyprefix=111",
                "-parentscriptprefix=196",
                "-parent_bech32_hrp=bcrt",
                # Turn of consistency checks that can cause assert when parent node stops
                # and a peg-in transaction fails this belt-and-suspenders check.
                # NOTE: This can cause spurious problems in regtest, and should be dealt with in a better way.
                "-checkmempool=0",
                "-peginsubsidyheight=%s" % PEGIN_SUBSIDY_HEIGHT,
                "-peginsubsidythreshold=2.0",
                "-peginminheight=%s" % PEGIN_MINIMUM_HEIGHT,
                "-peginminamount=1.0",
            ]
            if not self.options.parent_bitcoin:
                extra_args.extend(
                    [
                        "-parentpubkeyprefix=235",
                        "-parentscriptprefix=75",
                        "-parent_bech32_hrp=ert",
                        "-con_parent_chain_signblockscript=51",
                        "-con_parent_pegged_asset=%s" % parent_pegged_asset,
                    ]
                )

            # Use rpcuser auth only for first parent.
            if n == 0:
                # Extract username and password from cookie file and use directly.
                datadir = get_datadir_path(self.options.tmpdir, n)
                rpc_u, rpc_p = get_auth_cookie(datadir, parent_chain)
                extra_args.extend(
                    [
                        "-mainchainrpcuser=%s" % rpc_u,
                        "-mainchainrpcpassword=%s" % rpc_p,
                    ]
                )
            else:
                # Need to specify where to find parent cookie file
                datadir = get_datadir_path(self.options.tmpdir, n)
                extra_args.append("-mainchainrpccookiefile=" + datadir + "/" + parent_chain + "/.cookie")

            self.add_nodes(1, [extra_args], chain=["elementsregtest"])
            self.start_node(1 + n)
            self.log.info(f"Node {1 + n} started (sidechain: elementsd)")

        # We only connect the same-chain nodes, so sync_all works correctly
        self.connect_nodes(1, 2)
        self.node_groups = [
            [self.nodes[0]],
            [self.nodes[1], self.nodes[2]],
        ]
        for node_group in self.node_groups:
            self.sync_all(node_group)
        self.log.info("Setting up network done")

    def run_test(self):
        self.import_deterministic_coinbase_privkeys()  # Create wallets for all nodes

        parent = self.nodes[0]
        sidechain = self.nodes[1]
        sidechain2 = self.nodes[2]

        assert_equal(sidechain.getsidechaininfo()["pegin_confirmation_depth"], 10)  # 10+2 confirms required to get into mempool and confirm

        parent.importprivkey(privkey=parent.get_deterministic_priv_key().key, label="mining")
        sidechain.importprivkey(privkey=sidechain.get_deterministic_priv_key().key, label="mining")
        util.node_fastmerkle = sidechain

        self.generate(parent, 101, sync_fun=self.no_op)
        self.generate(sidechain, 101, sync_fun=self.no_op)

        def sync_sidechain():
            return self.sync_all([sidechain, sidechain2])

        DEFAULT_FEERATE = 1.0

        def parent_pegin(parent, node, amount=1.0, feerate=DEFAULT_FEERATE):
            address = node.getpeginaddress()
            mainchain_address, claim_script = (
                address["mainchain_address"],
                address["claim_script"],
            )
            txid = parent.sendtoaddress(address=mainchain_address, amount=amount, fee_rate=feerate)
            vout = find_vout_for_address(parent, txid, mainchain_address)
            self.generate(parent, 12, sync_fun=self.no_op)
            txoutproof = parent.gettxoutproof([txid])
            bitcoin_txhex = parent.gettransaction(txid)["hex"]
            return (
                txid,
                vout,
                txoutproof,
                bitcoin_txhex,
                claim_script,
            )

        self.log.info("check new fields for getpeginaddress and getsidechaininfo")
        result = sidechain.getpeginaddress()
        assert_equal(result["pegin_min_amount"], "1.00")
        assert_equal(result["pegin_min_height"], PEGIN_MINIMUM_HEIGHT)
        assert_equal(result["pegin_min_active"], False)
        assert_equal(result["pegin_subsidy_threshold"], "2.00")
        assert_equal(result["pegin_subsidy_height"], PEGIN_SUBSIDY_HEIGHT)
        assert_equal(result["pegin_subsidy_active"], False)
        result = sidechain.getsidechaininfo()
        assert_equal(result["pegin_min_amount"], "1.00")
        assert_equal(result["pegin_min_height"], PEGIN_MINIMUM_HEIGHT)
        assert_equal(result["pegin_min_active"], False)
        assert_equal(result["pegin_subsidy_threshold"], "2.00")
        assert_equal(result["pegin_subsidy_height"], PEGIN_SUBSIDY_HEIGHT)
        assert_equal(result["pegin_subsidy_active"], False)

        self.log.info("check min pegin amount before minimum pegin height")
        assert_equal(sidechain.getblockchaininfo()["blocks"], PEGIN_MINIMUM_HEIGHT - 1)
        txid, vout, txoutproof, bitcoin_txhex, claim_script = parent_pegin(parent, sidechain, amount=0.5)
        pegin_txid = sidechain.claimpegin(bitcoin_txhex, txoutproof, claim_script)
        self.generate(sidechain, 1, sync_fun=sync_sidechain)
        pegin_tx = sidechain.gettransaction(pegin_txid, True, True)
        assert_equal(pegin_tx["confirmations"], 1)

        assert_equal(sidechain.getblockchaininfo()["blocks"], PEGIN_MINIMUM_HEIGHT)
        result = sidechain.getpeginaddress()
        assert_equal(result["pegin_min_amount"], "1.00")
        assert_equal(result["pegin_min_height"], PEGIN_MINIMUM_HEIGHT)
        assert_equal(result["pegin_min_active"], True)
        assert_equal(result["pegin_subsidy_threshold"], "2.00")
        assert_equal(result["pegin_subsidy_height"], PEGIN_SUBSIDY_HEIGHT)
        assert_equal(result["pegin_subsidy_active"], False)
        result = sidechain.getsidechaininfo()
        assert_equal(result["pegin_min_amount"], "1.00")
        assert_equal(result["pegin_min_height"], PEGIN_MINIMUM_HEIGHT)
        assert_equal(result["pegin_min_active"], True)
        assert_equal(result["pegin_subsidy_threshold"], "2.00")
        assert_equal(result["pegin_subsidy_height"], PEGIN_SUBSIDY_HEIGHT)
        assert_equal(result["pegin_subsidy_active"], False)

        self.log.info("check min pegin amount after minimum pegin height")
        txid, vout, txoutproof, bitcoin_txhex, claim_script = parent_pegin(parent, sidechain, amount=0.5)
        assert_raises_rpc_error(
            -4,
            "Pegin amount (0.50) is lower than the minimum pegin amount for this chain (1.00).",
            sidechain.claimpegin,
            bitcoin_txhex,
            txoutproof,
            claim_script,
        )
        # check manually constructed
        inputs = [
            {
                "txid": txid,
                "vout": vout,
                "pegin_bitcoin_tx": bitcoin_txhex,
                "pegin_txout_proof": txoutproof,
                "pegin_claim_script": claim_script,
            },
        ]
        fee = Decimal("0.00000363")
        outputs = [
            {sidechain.getnewaddress(): Decimal("0.5") - fee},
            {"fee": fee},
        ]
        raw = sidechain.createrawtransaction(inputs, outputs)
        signed = sidechain.signrawtransactionwithwallet(raw)
        assert_equal(signed["complete"], True)
        accept = sidechain.testmempoolaccept([signed["hex"]])
        assert_equal(accept[0]["allowed"], False)
        assert_equal(accept[0]["reject-reason"], "pegin-value-too-low")

        self.log.info("createrawpegin before enforcement, with validatepegin, below threshold")
        txid, vout, txoutproof, bitcoin_txhex, claim_script = parent_pegin(parent, sidechain, amount=1.0, feerate=2.0)
        pegintx = sidechain.createrawpegin(bitcoin_txhex, txoutproof, claim_script)
        signed = sidechain.signrawtransactionwithwallet(pegintx["hex"])
        assert_equal(signed["complete"], True)
        pegin_txid = sidechain.sendrawtransaction(signed["hex"])
        pegin_tx = sidechain.gettransaction(pegin_txid, True, True)
        assert_equal(len(pegin_tx["decoded"]["vout"]), 2)
        self.generate(sidechain, 1, sync_fun=sync_sidechain)

        self.log.info("createrawpegin before enforcement, with validatepegin, above threshold")
        txid, vout, txoutproof, bitcoin_txhex, claim_script = parent_pegin(parent, sidechain, amount=2.0, feerate=2.0)
        pegintx = sidechain.createrawpegin(bitcoin_txhex, txoutproof, claim_script)
        signed = sidechain.signrawtransactionwithwallet(pegintx["hex"])
        assert_equal(signed["complete"], True)
        pegin_txid = sidechain.sendrawtransaction(signed["hex"])
        pegin_tx = sidechain.gettransaction(pegin_txid, True, True)
        assert_equal(len(pegin_tx["decoded"]["vout"]), 2)
        self.generate(sidechain, 1, sync_fun=sync_sidechain)

        self.log.info("createrawpegin before enforcement, without validatepegin, below threshold")
        txid, vout, txoutproof, bitcoin_txhex, claim_script = parent_pegin(parent, sidechain2, amount=1.0, feerate=2.0)
        pegintx = sidechain2.createrawpegin(bitcoin_txhex, txoutproof, claim_script)
        signed = sidechain2.signrawtransactionwithwallet(pegintx["hex"])
        assert_equal(signed["complete"], True)
        pegin_txid = sidechain2.sendrawtransaction(signed["hex"])
        pegin_tx = sidechain2.gettransaction(pegin_txid, True, True)
        assert_equal(len(pegin_tx["decoded"]["vout"]), 2)
        self.generate(sidechain2, 1, sync_fun=sync_sidechain)

        self.log.info("createrawpegin before enforcement, without validatepegin, above threshold")
        txid, vout, txoutproof, bitcoin_txhex, claim_script = parent_pegin(parent, sidechain2, amount=2.0, feerate=2.0)
        pegintx = sidechain2.createrawpegin(bitcoin_txhex, txoutproof, claim_script)
        signed = sidechain2.signrawtransactionwithwallet(pegintx["hex"])
        assert_equal(signed["complete"], True)
        pegin_txid = sidechain2.sendrawtransaction(signed["hex"])
        pegin_tx = sidechain2.gettransaction(pegin_txid, True, True)
        assert_equal(len(pegin_tx["decoded"]["vout"]), 2)
        self.generate(sidechain2, 1, sync_fun=sync_sidechain)

        self.log.info("claimpegin before enforcement, with validatepegin, below threshold")
        txid, vout, txoutproof, bitcoin_txhex, claim_script = parent_pegin(parent, sidechain, amount=1.0, feerate=2.0)
        pegin_txid = sidechain.claimpegin(bitcoin_txhex, txoutproof, claim_script)
        pegin_tx = sidechain.gettransaction(pegin_txid, True, True)
        assert_equal(len(pegin_tx["decoded"]["vout"]), 2)
        self.generate(sidechain, 1, sync_fun=sync_sidechain)

        self.log.info("claimpegin before enforcement, with validatepegin, above threshold")
        txid, vout, txoutproof, bitcoin_txhex, claim_script = parent_pegin(parent, sidechain, amount=2.0, feerate=2.0)
        pegin_txid = sidechain.claimpegin(bitcoin_txhex, txoutproof, claim_script)
        pegin_tx = sidechain.gettransaction(pegin_txid, True, True)
        assert_equal(len(pegin_tx["decoded"]["vout"]), 2)
        self.generate(sidechain, 1, sync_fun=sync_sidechain)

        self.log.info("claimpegin before enforcement, without validatepegin, below threshold")
        txid, vout, txoutproof, bitcoin_txhex, claim_script = parent_pegin(parent, sidechain2, amount=1.0, feerate=2.0)
        pegin_txid = sidechain2.claimpegin(bitcoin_txhex, txoutproof, claim_script)
        pegin_tx = sidechain2.gettransaction(pegin_txid, True, True)
        assert_equal(len(pegin_tx["decoded"]["vout"]), 2)
        self.generate(sidechain2, 1, sync_fun=sync_sidechain)

        self.log.info("claimpegin before enforcement, without validatepegin, above threshold")
        txid, vout, txoutproof, bitcoin_txhex, claim_script = parent_pegin(parent, sidechain2, amount=2.0, feerate=2.0)
        pegin_txid = sidechain2.claimpegin(bitcoin_txhex, txoutproof, claim_script)
        pegin_tx = sidechain2.gettransaction(pegin_txid, True, True)
        assert_equal(len(pegin_tx["decoded"]["vout"]), 2)
        self.generate(sidechain2, 1, sync_fun=sync_sidechain)

        num = PEGIN_SUBSIDY_HEIGHT - sidechain.getblockchaininfo()["blocks"]
        assert num > 0
        self.generate(sidechain, num, sync_fun=sync_sidechain)

        self.log.info(f"===== peg-in subsidy enforcement at height {PEGIN_SUBSIDY_HEIGHT} =====")
        assert_equal(sidechain.getblockchaininfo()["blocks"], PEGIN_SUBSIDY_HEIGHT)

        self.log.info("check new fields for getpeginaddress and getsidechaininfo")
        result = sidechain.getpeginaddress()
        assert_equal(result["pegin_min_amount"], "1.00")
        assert_equal(result["pegin_min_height"], PEGIN_MINIMUM_HEIGHT)
        assert_equal(result["pegin_min_active"], True)
        assert_equal(result["pegin_subsidy_threshold"], "2.00")
        assert_equal(result["pegin_subsidy_height"], PEGIN_SUBSIDY_HEIGHT)
        assert_equal(result["pegin_subsidy_active"], True)
        result = sidechain.getsidechaininfo()
        assert_equal(result["pegin_min_amount"], "1.00")
        assert_equal(result["pegin_min_height"], PEGIN_MINIMUM_HEIGHT)
        assert_equal(result["pegin_min_active"], True)
        assert_equal(result["pegin_subsidy_threshold"], "2.00")
        assert_equal(result["pegin_subsidy_height"], PEGIN_SUBSIDY_HEIGHT)
        assert_equal(result["pegin_subsidy_active"], True)

        # blinded pegins
        self.log.info("blinded pegin below threshold, with validatepegin, subsidy too low")
        txid, vout, txoutproof, bitcoin_txhex, claim_script = parent_pegin(parent, sidechain, amount=1.0, feerate=1.0)
        addr = sidechain.getnewaddress(address_type="blech32")
        utxo = sidechain.listunspent()[0]
        changeaddr = sidechain.getrawchangeaddress(address_type="blech32")
        inputs = [
            {
                "txid": txid,
                "vout": vout,
                "pegin_bitcoin_tx": bitcoin_txhex,
                "pegin_txout_proof": txoutproof,
                "pegin_claim_script": claim_script,
            },
            {
                "txid": utxo["txid"],
                "vout": utxo["vout"],
            },
        ]
        fee = Decimal("0.00000363")
        subsidy = Decimal("0.00000395")
        outputs = [
            {addr: Decimal("1.0") - fee - subsidy},
            {changeaddr: utxo["amount"]},
            {"burn": subsidy},
            {"fee": fee},
        ]
        raw = sidechain.createrawtransaction(inputs, outputs)
        blinded = sidechain.blindrawtransaction(hexstring=raw, ignoreblindfail=False)
        signed = sidechain.signrawtransactionwithwallet(blinded)
        assert_equal(signed["complete"], True)
        # node 2 can't validatepegin but checks the minimum subsidy
        accept = sidechain2.testmempoolaccept([signed["hex"]])
        assert_equal(accept[0]["allowed"], False)
        assert_equal(accept[0]["reject-reason"], "pegin-subsidy-too-low")
        # node 1 will reject
        accept = sidechain.testmempoolaccept([signed["hex"]])
        assert_equal(accept[0]["allowed"], False)
        assert_equal(accept[0]["reject-reason"], "pegin-subsidy-too-low")
        assert_raises_rpc_error(
            -26,
            "pegin-subsidy-too-low",
            sidechain.sendrawtransaction,
            signed["hex"],
        )

        self.log.info("blinded pegin above threshold, with validatepegin")
        txid, vout, txoutproof, bitcoin_txhex, claim_script = parent_pegin(parent, sidechain, amount=2.0, feerate=1.0)
        addr = sidechain.getnewaddress(address_type="blech32")
        utxo = sidechain.listunspent()[0]
        changeaddr = sidechain.getrawchangeaddress(address_type="blech32")
        inputs = [
            {
                "txid": txid,
                "vout": vout,
                "pegin_bitcoin_tx": bitcoin_txhex,
                "pegin_txout_proof": txoutproof,
                "pegin_claim_script": claim_script,
            },
            {
                "txid": utxo["txid"],
                "vout": utxo["vout"],
            },
        ]
        fee = Decimal("0.00000363")
        outputs = [
            {addr: Decimal("2.0") - fee},
            {changeaddr: utxo["amount"]},
            {"fee": fee},
        ]
        raw = sidechain.createrawtransaction(inputs, outputs)
        blinded = sidechain.blindrawtransaction(hexstring=raw, ignoreblindfail=False)
        signed = sidechain.signrawtransactionwithwallet(blinded)
        assert_equal(signed["complete"], True)
        accept = sidechain.testmempoolaccept([signed["hex"]])
        assert_equal(accept[0]["allowed"], True)
        # =======

        self.log.info("createrawpegin after enforcement, with validatepegin, below threshold")
        txid, vout, txoutproof, bitcoin_txhex, claim_script = parent_pegin(parent, sidechain)
        pegintx = sidechain.createrawpegin(bitcoin_txhex, txoutproof, claim_script)
        signed = sidechain.signrawtransactionwithwallet(pegintx["hex"])
        pegin_txid = sidechain.sendrawtransaction(signed["hex"])
        pegin_tx = sidechain.gettransaction(pegin_txid, True, True)
        assert_equal(len(pegin_tx["decoded"]["vout"]), 3)
        # WSH input 41 bytes * 4 = 164 weight
        # Witness (11 * 72 bytes signatures + 626 bytes script size) = 1418 weight
        # (164 + 1418 + 3) / 4 = 396 vbytes
        assert_equal(pegin_tx["decoded"]["vout"][1]["value"], Decimal("0.00000396"))
        self.generate(sidechain, 1, sync_fun=sync_sidechain)

        self.log.info("createrawpegin after enforcement, with validatepegin, above threshold")
        txid, vout, txoutproof, bitcoin_txhex, claim_script = parent_pegin(parent, sidechain, amount=3.0, feerate=2.0)
        pegintx = sidechain.createrawpegin(bitcoin_txhex, txoutproof, claim_script)
        signed = sidechain.signrawtransactionwithwallet(pegintx["hex"])
        pegin_txid = sidechain.sendrawtransaction(signed["hex"])
        pegin_tx = sidechain.gettransaction(pegin_txid, True, True)
        assert_equal(len(pegin_tx["decoded"]["vout"]), 2)
        self.generate(sidechain, 1, sync_fun=sync_sidechain)

        self.log.info("createrawpegin after enforcement, without validatepegin, below threshold")
        feerate = 2.0
        txid, vout, txoutproof, bitcoin_txhex, claim_script = parent_pegin(parent, sidechain2, 1.0, feerate)
        assert_raises_rpc_error(
            -8,
            "Bitcoin transaction fee rate must be supplied, because validatepegin is off and this peg-in requires a burn subsidy.",
            sidechain2.createrawpegin,
            bitcoin_txhex,
            txoutproof,
            claim_script,
        )

        pegintx = sidechain2.createrawpegin(bitcoin_txhex, txoutproof, claim_script, feerate)
        signed = sidechain2.signrawtransactionwithwallet(pegintx["hex"])
        pegin_txid = sidechain2.sendrawtransaction(signed["hex"])
        pegin_tx = sidechain2.gettransaction(pegin_txid, True, True)
        assert_equal(len(pegin_tx["decoded"]["vout"]), 3)
        assert_equal(pegin_tx["decoded"]["vout"][1]["value"], Decimal("0.00000792"))
        self.generate(sidechain2, 1, sync_fun=sync_sidechain)

        self.log.info("createrawpegin after enforcement, without validatepegin, above threshold")
        txid, vout, txoutproof, bitcoin_txhex, claim_script = parent_pegin(parent, sidechain2, amount=2.0, feerate=2.0)
        pegintx = sidechain2.createrawpegin(bitcoin_txhex, txoutproof, claim_script, feerate)
        signed = sidechain2.signrawtransactionwithwallet(pegintx["hex"])
        assert_equal(signed["complete"], True)
        pegin_txid = sidechain2.sendrawtransaction(signed["hex"])
        pegin_tx = sidechain2.gettransaction(pegin_txid, True, True)
        assert_equal(len(pegin_tx["decoded"]["vout"]), 2)
        self.generate(sidechain2, 1, sync_fun=sync_sidechain)

        self.log.info("claimpegin after enforcement, with validatepegin, below threshold")
        txid, vout, txoutproof, bitcoin_txhex, claim_script = parent_pegin(parent, sidechain, amount=1.0, feerate=2.0)
        pegin_txid = sidechain.claimpegin(bitcoin_txhex, txoutproof, claim_script)
        pegin_tx = sidechain.gettransaction(pegin_txid, True, True)
        assert_equal(len(pegin_tx["decoded"]["vout"]), 3)
        assert_equal(pegin_tx["decoded"]["vout"][1]["value"], Decimal("0.00000792"))
        self.generate(sidechain, 1, sync_fun=sync_sidechain)

        self.log.info("claimpegin after enforcement, with validatepegin, above threshold")
        txid, vout, txoutproof, bitcoin_txhex, claim_script = parent_pegin(parent, sidechain, amount=2.0, feerate=2.0)
        pegin_txid = sidechain.claimpegin(bitcoin_txhex, txoutproof, claim_script)
        pegin_tx = sidechain.gettransaction(pegin_txid, True, True)
        assert_equal(len(pegin_tx["decoded"]["vout"]), 2)
        self.generate(sidechain, 1, sync_fun=sync_sidechain)

        self.log.info("claimpegin after enforcement, without validatepegin, below threshold")
        feerate = 2.0
        txid, vout, txoutproof, bitcoin_txhex, claim_script = parent_pegin(parent, sidechain2, 1.0, feerate)
        assert_raises_rpc_error(
            -8,
            "Bitcoin transaction fee rate must be supplied, because validatepegin is off and this peg-in requires a burn subsidy.",
            sidechain2.claimpegin,
            bitcoin_txhex,
            txoutproof,
            claim_script,
        )

        pegin_txid = sidechain2.claimpegin(bitcoin_txhex, txoutproof, claim_script, feerate)
        pegin_tx = sidechain2.gettransaction(pegin_txid, True, True)
        assert_equal(len(pegin_tx["decoded"]["vout"]), 3)
        assert_equal(pegin_tx["decoded"]["vout"][1]["value"], Decimal("0.00000792"))
        self.generate(sidechain2, 1, sync_fun=sync_sidechain)

        self.log.info("claimpegin after enforcement, without validatepegin, above threshold")
        feerate = 2.0
        txid, vout, txoutproof, bitcoin_txhex, claim_script = parent_pegin(parent, sidechain2, 2.0, feerate)
        pegin_txid = sidechain2.claimpegin(bitcoin_txhex, txoutproof, claim_script, feerate)
        pegin_tx = sidechain2.gettransaction(pegin_txid, True, True)
        assert_equal(len(pegin_tx["decoded"]["vout"]), 2)
        self.generate(sidechain2, 1, sync_fun=sync_sidechain)

        self.log.info("claimpegin after enforcement, without validatepegin, below threshold, with incorrect subsidy output")
        # should be accepted by sidechain2 but rejected by the node that is validating pegins
        txid, vout, txoutproof, bitcoin_txhex, claim_script = parent_pegin(parent, sidechain2, amount=1.0, feerate=2.0)
        assert_raises_rpc_error(
            -8,
            "Bitcoin transaction fee rate must be supplied, because validatepegin is off and this peg-in requires a burn subsidy.",
            sidechain2.claimpegin,
            bitcoin_txhex,
            txoutproof,
            claim_script,
        )

        low_feerate = 1.0
        pegin_txid = sidechain2.claimpegin(bitcoin_txhex, txoutproof, claim_script, low_feerate)
        pegin_tx = sidechain2.gettransaction(pegin_txid, True, True)
        assert_equal(len(pegin_tx["decoded"]["vout"]), 3)

        accept = sidechain.testmempoolaccept([pegin_tx["hex"]])
        assert_equal(accept[0]["allowed"], False)
        assert_equal(accept[0]["reject-reason"], "pegin-subsidy-too-low")
        self.generate(sidechain2, 1, sync_fun=sync_sidechain)

        txid, vout, txoutproof, bitcoin_txhex, claim_script = parent_pegin(parent, sidechain2, amount=1.99999999, feerate=2.0)
        assert_raises_rpc_error(
            -8,
            "Bitcoin transaction fee rate must be supplied, because validatepegin is off and this peg-in requires a burn subsidy.",
            sidechain2.claimpegin,
            bitcoin_txhex,
            txoutproof,
            claim_script,
        )

        low_feerate = 1.0
        pegin_txid = sidechain2.claimpegin(bitcoin_txhex, txoutproof, claim_script, low_feerate)
        pegin_tx = sidechain2.gettransaction(pegin_txid, True, True)
        assert_equal(len(pegin_tx["decoded"]["vout"]), 3)

        accept = sidechain.testmempoolaccept([pegin_tx["hex"]])
        assert_equal(accept[0]["allowed"], False)
        assert_equal(accept[0]["reject-reason"], "pegin-subsidy-too-low")
        self.generate(sidechain2, 1, sync_fun=sync_sidechain)

        # sidechain2 should accept a 1 sat/vb subsidy for a higher feerate parent, but validating node should reject
        txid, vout, txoutproof, bitcoin_txhex, claim_script = parent_pegin(parent, sidechain2, amount=1.0, feerate=2.0)
        # first try with less than 1 sat/vb subsidy
        inputs = [
            {
                "txid": txid,
                "vout": vout,
                "pegin_bitcoin_tx": bitcoin_txhex,
                "pegin_txout_proof": txoutproof,
                "pegin_claim_script": claim_script,
            },
        ]
        fee = Decimal("0.00000363")
        addr = get_new_unconfidential_address(sidechain)
        # subsidy less than 1 sat/vb
        subsidy = Decimal("0.00000395")
        outputs = [
            {addr: Decimal("1.0") - fee - subsidy},
            {"burn": subsidy},
            {"fee": fee},
        ]

        raw = sidechain2.createrawtransaction(inputs, outputs)
        signed = sidechain2.signrawtransactionwithwallet(raw)
        assert_equal(signed["complete"], True)

        accept = sidechain2.testmempoolaccept([signed["hex"]])
        assert_equal(accept[0]["allowed"], False)
        assert_equal(accept[0]["reject-reason"], "pegin-subsidy-too-low")

        accept = sidechain.testmempoolaccept([signed["hex"]])
        assert_equal(accept[0]["allowed"], False)
        assert_equal(accept[0]["reject-reason"], "pegin-subsidy-too-low")

        # subsidy for 1 sat/vb accepted by sidechain2, but rejected by validating node
        subsidy = Decimal("0.00000396")
        outputs = [
            {addr: Decimal("1.0") - fee - subsidy},
            {"burn": subsidy},
            {"fee": fee},
        ]

        raw = sidechain2.createrawtransaction(inputs, outputs)
        signed = sidechain2.signrawtransactionwithwallet(raw)
        assert_equal(signed["complete"], True)

        accept = sidechain2.testmempoolaccept([signed["hex"]])
        assert_equal(accept[0]["allowed"], True)

        accept = sidechain.testmempoolaccept([signed["hex"]])
        assert_equal(accept[0]["allowed"], False)
        assert_equal(accept[0]["reject-reason"], "pegin-subsidy-too-low")

        # sub 1 sat/vb parent feerate should use 1 sat/vb for subsidy calculation
        self.log.info("claimpegin after enforcement, with validatepegin, below threshold, sub 1 sat/vb parent")
        txid, vout, txoutproof, bitcoin_txhex, claim_script = parent_pegin(parent, sidechain, amount=1, feerate=0.1)
        pegin_txid = sidechain.claimpegin(bitcoin_txhex, txoutproof, claim_script)
        pegin_tx = sidechain.gettransaction(pegin_txid, True, True)
        assert_equal(len(pegin_tx["decoded"]["vout"]), 3)
        assert_equal(pegin_tx["decoded"]["vout"][1]["value"], Decimal("0.00000396"))

        # check manually constructed pegin from a sub 1 sat/vb parent
        txid, vout, txoutproof, bitcoin_txhex, claim_script = parent_pegin(parent, sidechain, amount=1, feerate=0.1)
        inputs = [
            {
                "txid": txid,
                "vout": vout,
                "pegin_bitcoin_tx": bitcoin_txhex,
                "pegin_txout_proof": txoutproof,
                "pegin_claim_script": claim_script,
            },
        ]
        fee = Decimal("0.00000363")
        addr = get_new_unconfidential_address(sidechain)
        # subsidy too low
        subsidy = Decimal("0.00000395")
        outputs = [
            {addr: Decimal("1.0") - fee - subsidy},
            {"burn": subsidy},
            {"fee": fee},
        ]

        raw = sidechain.createrawtransaction(inputs, outputs)
        signed = sidechain.signrawtransactionwithwallet(raw)
        assert_equal(signed["complete"], True)
        accept = sidechain.testmempoolaccept([signed["hex"]])
        assert_equal(accept[0]["allowed"], False)
        assert_equal(accept[0]["reject-reason"], "pegin-subsidy-too-low")

        # subsidy accepted
        subsidy = Decimal("0.00000396")
        outputs = [
            {addr: Decimal("1.0") - fee - subsidy},
            {"burn": subsidy},
            {"fee": fee},
        ]

        raw = sidechain.createrawtransaction(inputs, outputs)
        signed = sidechain.signrawtransactionwithwallet(raw)
        assert_equal(signed["complete"], True)
        accept = sidechain.testmempoolaccept([signed["hex"]])
        assert_equal(accept[0]["allowed"], True)
        sidechain.sendrawtransaction(signed["hex"])
        self.generate(sidechain, 1, sync_fun=sync_sidechain)
        # =================================

        self.log.info("construct a multi-pegin tx, below threshold")
        feerate = 2.0
        txid1, vout1, txoutproof1, bitcoin_txhex1, claim_script1 = parent_pegin(parent, sidechain, 0.5, feerate)
        txid2, vout2, txoutproof2, bitcoin_txhex2, claim_script2 = parent_pegin(parent, sidechain, 1.0, feerate)

        addr1 = get_new_unconfidential_address(sidechain)
        addr2 = get_new_unconfidential_address(sidechain)

        inputs = [
            {
                "txid": txid1,
                "vout": vout1,
                "pegin_bitcoin_tx": bitcoin_txhex1,
                "pegin_txout_proof": txoutproof1,
                "pegin_claim_script": claim_script1,
            },
            {
                "txid": txid2,
                "vout": vout2,
                "pegin_bitcoin_tx": bitcoin_txhex2,
                "pegin_txout_proof": txoutproof2,
                "pegin_claim_script": claim_script2,
            },
        ]
        fee = Decimal("0.00000363")
        subsidy = Decimal("0.00001583")
        outputs = [
            {addr1: Decimal("0.5") - fee - subsidy},
            {addr2: 1.0},
            {"burn": subsidy},
            {"fee": fee},
        ]
        raw = sidechain.createrawtransaction(inputs, outputs)
        signed = sidechain.signrawtransactionwithwallet(raw)
        assert_equal(signed["complete"], True)
        accept = sidechain.testmempoolaccept([signed["hex"]])
        assert_equal(accept[0]["allowed"], False)
        assert_equal(accept[0]["reject-reason"], "pegin-subsidy-too-low")

        subsidy = Decimal("0.00001584")
        outputs = [
            {addr1: Decimal("0.5") - fee - subsidy},
            {addr2: 1.0},
            {"burn": subsidy},
            {"fee": fee},
        ]
        raw = sidechain.createrawtransaction(inputs, outputs)
        signed = sidechain.signrawtransactionwithwallet(raw)
        assert_equal(signed["complete"], True)
        accept = sidechain.testmempoolaccept([signed["hex"]])
        assert_equal(accept[0]["allowed"], True)
        sidechain.sendrawtransaction(signed["hex"])
        self.generate(sidechain2, 1, sync_fun=sync_sidechain)

        self.log.info("construct a multi-pegin tx, above threshold")
        txid1, vout1, txoutproof1, bitcoin_txhex1, claim_script1 = parent_pegin(parent, sidechain, amount=0.5, feerate=1.0)
        txid2, vout2, txoutproof2, bitcoin_txhex2, claim_script2 = parent_pegin(parent, sidechain, amount=1.5, feerate=2.0)
        addr1 = get_new_unconfidential_address(sidechain)
        addr2 = get_new_unconfidential_address(sidechain)

        inputs = [
            {
                "txid": txid1,
                "vout": vout1,
                "pegin_bitcoin_tx": bitcoin_txhex1,
                "pegin_txout_proof": txoutproof1,
                "pegin_claim_script": claim_script1,
            },
            {
                "txid": txid2,
                "vout": vout2,
                "pegin_bitcoin_tx": bitcoin_txhex2,
                "pegin_txout_proof": txoutproof2,
                "pegin_claim_script": claim_script2,
            },
        ]
        fee = Decimal("0.00000363")
        outputs = [
            {addr1: 0.5},
            {addr2: Decimal("1.5") - fee},
            {"fee": fee},
        ]
        raw = sidechain.createrawtransaction(inputs, outputs)
        signed = sidechain.signrawtransactionwithwallet(raw)
        accept = sidechain.testmempoolaccept([signed["hex"]])
        assert_equal(accept[0]["allowed"], True)
        sidechain.sendrawtransaction(signed["hex"])
        self.generate(sidechain2, 1, sync_fun=sync_sidechain)

        # minimum pegin amount is 1.0
        self.log.info("claimpegin below minimum pegin amount")
        txid, vout, txoutproof, bitcoin_txhex, claim_script = parent_pegin(parent, sidechain, amount=0.99999999)
        assert_raises_rpc_error(
            -4,
            "Pegin amount (0.99999999) is lower than the minimum pegin amount for this chain (1.00).",
            sidechain2.claimpegin,
            bitcoin_txhex,
            txoutproof,
            claim_script,
        )

        # check minimum pegin amount in mempool validation by constructing manually
        self.log.info("rawtransaction below minimum pegin amount")
        txid, vout, txoutproof, bitcoin_txhex, claim_script = parent_pegin(parent, sidechain2, amount=0.99999999)
        addr = sidechain2.getnewaddress()
        inputs = [
            {
                "txid": txid,
                "vout": vout,
                "pegin_bitcoin_tx": bitcoin_txhex,
                "pegin_txout_proof": txoutproof,
                "pegin_claim_script": claim_script,
            },
        ]
        fee = Decimal("0.00000363")
        subsidy = Decimal("0.00000396")
        outputs = [
            {addr: Decimal("0.99999999") - fee - subsidy},
            {"burn": subsidy},
            {"fee": fee},
        ]

        raw = sidechain2.createrawtransaction(inputs, outputs)
        signed = sidechain2.signrawtransactionwithwallet(raw)
        assert_equal(signed["complete"], True)
        accept = sidechain2.testmempoolaccept([signed["hex"]])
        # node2 can check the min pegin amount as the pegin amount is in the witness
        assert_equal(accept[0]["allowed"], False)
        assert_equal(accept[0]["reject-reason"], "pegin-value-too-low")
        # node1 rejects below the min pegin amount with validatepegin
        accept = sidechain.testmempoolaccept([signed["hex"]])
        assert_equal(accept[0]["allowed"], False)
        assert_equal(accept[0]["reject-reason"], "pegin-value-too-low")
        assert_raises_rpc_error(
            -26,
            "pegin-value-too-low",
            sidechain.sendrawtransaction,
            signed["hex"],
        )
        self.generate(sidechain, 1, sync_fun=sync_sidechain)

        # test various feerates
        self.log.info("claimpegin with validatepegin, below threshold, at various feerates")
        for feerate in [1.0, 1.5, 2.0, 2.3, 3.9, 4.6, 5.2, 6.1, 10.01, 20.7, 22.22, 24.18]:
            txid, vout, txoutproof, bitcoin_txhex, claim_script = parent_pegin(parent, sidechain, 1.0, feerate)
            pegin_txid = sidechain.claimpegin(bitcoin_txhex, txoutproof, claim_script)
            pegin_tx = sidechain.gettransaction(pegin_txid, True, True)
            assert_equal(len(pegin_tx["decoded"]["vout"]), 3)
            self.generate(sidechain, 1, sync_fun=sync_sidechain)

        # dust error
        # restart node1 with no min pegin amount
        self.stop_node(1, expected_stderr=self.expected_stderr)  # when running with bitcoind as parent node this stderr can occur
        self.start_node(1, extra_args=sidechain.extra_args + ["-peginminamount=0"])
        self.log.info("claimpegin dust error")
        amount = Decimal("0.00000546") if self.options.parent_bitcoin else Decimal("0.00000645")
        txid, vout, txoutproof, bitcoin_txhex, claim_script = parent_pegin(parent, sidechain, amount)
        assert_raises_rpc_error(
            -4,
            "Peg-in transaction would create dust output.",
            sidechain.claimpegin,
            bitcoin_txhex,
            txoutproof,
            claim_script,
        )
        # check dust mempool validation by constructing manually
        txid, vout, txoutproof, bitcoin_txhex, claim_script = parent_pegin(parent, sidechain2, amount=0.00001570)
        addr = sidechain2.getnewaddress()
        inputs = [
            {
                "txid": txid,
                "vout": vout,
                "pegin_bitcoin_tx": bitcoin_txhex,
                "pegin_txout_proof": txoutproof,
                "pegin_claim_script": claim_script,
            },
        ]
        fee = Decimal("0.00000363")
        subsidy = Decimal("0.00001194")
        outputs = [
            {addr: Decimal("0.00001570") - fee - subsidy},  # 14 sats is dust at 0.1 sat/vb dustrelayfee
            {"burn": subsidy},
            {"fee": fee},
        ]

        raw = sidechain2.createrawtransaction(inputs, outputs)
        signed = sidechain2.signrawtransactionwithwallet(raw)
        assert_equal(signed["complete"], True)
        accept = sidechain2.testmempoolaccept([signed["hex"]])
        # mempool validation already checks for dust outputs
        assert_equal(accept[0]["allowed"], False)
        assert_equal(accept[0]["reject-reason"], "dust")
        accept = sidechain.testmempoolaccept([signed["hex"]])
        assert_equal(accept[0]["allowed"], False)
        assert_equal(accept[0]["reject-reason"], "dust")
        assert_raises_rpc_error(
            -26,
            "dust",
            sidechain.sendrawtransaction,
            signed["hex"],
        )

        # Manually stop sidechains first, then the parent chain.
        self.stop_node(2)
        self.stop_node(1, expected_stderr=self.expected_stderr)  # when running with bitcoind as parent node this stderr can occur
        self.stop_node(0)


if __name__ == "__main__":
    PeginSubsidyTest().main()
