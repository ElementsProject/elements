#!/usr/bin/env python3
# Copyright (c) 2021 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
from decimal import Decimal
from io import BytesIO

from test_framework.messages import CTransaction, CTxInWitness
from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import assert_equal, assert_raises_rpc_error


class AnnexPaddingTest(BitcoinTestFramework):
    """Test exact annex padding for Simplicity spends."""

    def set_test_params(self):
        self.setup_clean_chain = True
        self.num_nodes = 1
        self.extra_args = [["-evbparams=simplicity:-1:::"]] * self.num_nodes

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def run_test(self):
        self.log.info("Check that Simplicity is active")
        simplicity = self.nodes[0].getdeploymentinfo()["deployments"]["simplicity"]
        assert simplicity["active"]
        self.generate(self.nodes[0], 101)

        utxo = self.nodes[0].listunspent()[0]
        assert_equal(utxo["amount"], Decimal("50.00000000"))
        fee = Decimal("0.00001000")
        amount = utxo["amount"] - fee

        # this elementsregtest address is generated from the "hash loop" SimplicityHL template
        addr = "ert1pzp4xccn92zvhh44z9qwh3ap3jnv677ympuaafmyv4urgfrp2lafsdap5ha"
        # ---
        # fn hash_counter_8(ctx: Ctx8, unused: (), byte: u8) -> Either<u256, Ctx8> {
        #     let new_ctx: Ctx8 = jet::sha_256_ctx_8_add_1(ctx, byte);
        #     match jet::all_8(byte) {
        #         true => Left(jet::sha_256_ctx_8_finalize(new_ctx)),
        #         false => Right(new_ctx),
        #     }
        # }
        # fn main() {
        #     // Hash bytes 0x00 to 0xff
        #     let ctx: Ctx8 = jet::sha_256_ctx_8_init();
        #     let out: Either<u256, Ctx8> = for_while::<hash_counter_8>(ctx, ());
        #     let expected: u256 = 0x40aff2e9d2d8922e47afd4648e6967497158785fbd1da870e7110266bf944880;
        #     assert!(jet::eq_256(expected, unwrap_left::<Ctx8>(out)));
        # }
        # ---

        self.log.info("Fund the contract address")
        raw = self.nodes[0].createrawtransaction([{"txid": utxo["txid"], "vout": utxo["vout"]}], [{addr: amount}, {"fee": fee}])
        signed = self.nodes[0].signrawtransactionwithwallet(raw)
        assert signed["complete"]
        txid = self.nodes[0].sendrawtransaction(signed["hex"])
        self.generate(self.nodes[0], 1)

        in_witness = CTxInWitness()
        simplicity_witness = ""
        simplicity_program = "e8144eac81081420c48a0f9128a0590da107248150b21b79b8118720e30e3e070a85a02d8370c41c920542c86e2341c920542c86e2a36e30e3f0b30e3f0e38542cc2d6371b1b8e4c39071871f038542d016c1b906839240a8590dc8a41c920542c86e489b71871f90461c7e429c2a16616b1b93a839240a8590dca441c920542c86e559b71871f93861c7e4f9c2a16616b1b96e6e3430e3f204c38fc8438542cc2d6373066e618c39071871f038542d016c1b99041c70b06aa0420507cb3650420506e678e2b5620a203801a00dc0708038980e33039001390ac5f8bdd59a0d0ed8d3bb22cb0ef50f71e3a577040de5bfe99608095e7d53356765e430b9101722c0661c40cc0e4804e4a9792a2e4b85c9a01907681901c9f03958139625e588b966172d80641e0c064072ec273005e6005cc105cc280c83c380c80e6280e6600e694273545e6a85cd605cd780c83c5006407368139b92f3722e6ec2e6f80641e30032039c3039d109ceb179d6173b0173b60320f1c81901cf004e790bcf38b9e60b9ea01907902064073d840a136940aff2e9d2d8922e47afd4648e6967497158785fbd1da870e7110266bf944880042050831061c9160366ce8867390b3cffedf1a67f35f4e6e69c39210d09fddb9189a14c225a77e6c262e1806006616b66dd008c0212283f4060201c180e180740780"
        cmr = "988c6d7a1c50012028523debc8ec575ce96920c46a45f663051aa3309f6fc539"
        control_block = "be50929b74c1a04954b78b4b6035e97a5e078a5a0f28ec96d547bfee9ace803ac0"

        self.log.info("Try to spend without no annex")
        addr = self.nodes[0].getnewaddress(address_type="bech32")
        fee = Decimal("0.00003000")
        raw = self.nodes[0].createrawtransaction([{"txid": txid, "vout": 0}], [{addr: amount - fee}, {"fee": fee}])
        ctx = CTransaction()
        ctx.deserialize(BytesIO(bytes.fromhex(raw)))

        in_witness.scriptWitness.stack = [
            bytes.fromhex(simplicity_witness),
            bytes.fromhex(simplicity_program),
            bytes.fromhex(cmr),
            bytes.fromhex(control_block),
        ]
        ctx.wit.vtxinwit.append(in_witness)
        raw = ctx.serialize().hex()
        assert_raises_rpc_error(-26, "Program's execution cost could exceed budget", self.nodes[0].sendrawtransaction, raw)

        EXACT_PADDING = 7423
        # FIXME: investigate why rust-simplicity `Cost::get_padding` gives exact padding as 7426
        # https://github.com/BlockstreamResearch/rust-simplicity/blob/d28440bc0c6be333aa84fa441844541c14dbb563/src/analysis.rs#L148

        self.log.info("Try to spend with non-zero padded annex")
        annex = [0x50] + [0x01] * EXACT_PADDING
        in_witness.scriptWitness.stack = [
            bytes.fromhex(simplicity_witness),
            bytes.fromhex(simplicity_program),
            bytes.fromhex(cmr),
            bytes.fromhex(control_block),
            bytes(annex),
        ]
        ctx.wit.vtxinwit[0] = in_witness
        raw = ctx.serialize().hex()
        assert_raises_rpc_error(-26, "Simplicity annex padding must be all zeros", self.nodes[0].sendrawtransaction, raw)

        self.log.info("Try to spend with under-padded annex")
        annex = [0x50] + [0x00] * (EXACT_PADDING - 1)
        in_witness.scriptWitness.stack = [
            bytes.fromhex(simplicity_witness),
            bytes.fromhex(simplicity_program),
            bytes.fromhex(cmr),
            bytes.fromhex(control_block),
            bytes(annex),
        ]
        ctx.wit.vtxinwit[0] = in_witness
        raw = ctx.serialize().hex()
        assert_raises_rpc_error(-26, "Program's execution cost could exceed budget", self.nodes[0].sendrawtransaction, raw)

        self.log.info("Try to spend with over-padded annex")
        annex = [0x50] + [0x00] * (EXACT_PADDING + 1)
        in_witness.scriptWitness.stack = [
            bytes.fromhex(simplicity_witness),
            bytes.fromhex(simplicity_program),
            bytes.fromhex(cmr),
            bytes.fromhex(control_block),
            bytes(annex),
        ]
        ctx.wit.vtxinwit[0] = in_witness
        raw = ctx.serialize().hex()
        assert_raises_rpc_error(-26, "Program's budget is too large", self.nodes[0].sendrawtransaction, raw)

        self.log.info("Spend with exact padded annex")
        annex = [0x50] + [0x00] * EXACT_PADDING
        in_witness.scriptWitness.stack = [
            bytes.fromhex(simplicity_witness),
            bytes.fromhex(simplicity_program),
            bytes.fromhex(cmr),
            bytes.fromhex(control_block),
            bytes(annex),
        ]
        ctx.wit.vtxinwit[0] = in_witness
        raw = ctx.serialize().hex()
        txid = self.nodes[0].sendrawtransaction(raw)
        self.generate(self.nodes[0], 1)
        tx = self.nodes[0].gettransaction(txid)
        assert_equal(tx["confirmations"], 1)


if __name__ == "__main__":
    AnnexPaddingTest().main()
