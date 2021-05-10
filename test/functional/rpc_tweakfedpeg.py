#!/usr/bin/env python3

import re

from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import assert_equal

# Example script templates that we get proper responses from elements-0.14 based software
OP_TRUE_SCRIPT="51"
OP_CMS_SCRIPT="52210307fd375ed7cced0f50723e3e1a97bbe7ccff7318c815df4e99a59bc94dbcd819210367c4f666f18279009c941e57fab3e42653c6553e5ca092c104d1db279e328a2852ae"
LIQUID_SCRIPT="745c87635b21020e0338c96a8870479f2396c373cc7696ba124e8635d41b0ea581112b678172612102675333a4e4b8fb51d9d4e22fa5a8eaced3fdac8a8cbf9be8c030f75712e6af992102896807d54bc55c24981f24a453c60ad3e8993d693732288068a23df3d9f50d4821029e51a5ef5db3137051de8323b001749932f2ff0d34c82e96a2c2461de96ae56c2102a4e1a9638d46923272c266631d94d36bdb03a64ee0e14c7518e49d2f29bc40102102f8a00b269f8c5e59c67d36db3cdc11b11b21f64b4bffb2815e9100d9aa8daf072103079e252e85abffd3c401a69b087e590a9b86f33f574f08129ccbd3521ecf516b2103111cf405b627e22135b3b3733a4a34aa5723fb0f58379a16d32861bf576b0ec2210318f331b3e5d38156da6633b31929c5b220349859cc9ca3d33fb4e68aa08401742103230dae6b4ac93480aeab26d000841298e3b8f6157028e47b0897c1e025165de121035abff4281ff00660f99ab27bb53e6b33689c2cd8dcd364bc3c90ca5aea0d71a62103bd45cddfacf2083b14310ae4a84e25de61e451637346325222747b157446614c2103cc297026b06c71cbfa52089149157b5ff23de027ac5ab781800a578192d175462103d3bde5d63bdb3a6379b461be64dad45eabff42f758543a9645afd42f6d4248282103ed1e8d5109c9ed66f7941bc53cc71137baa76d50d274bda8d5e8ffbd6e61fe9a5f6702c00fb275522103aab896d53a8e7d6433137bbba940f9c521e085dd07e60994579b64a6d992cf79210291b7d0b1b692f8f524516ed950872e5da10fb1b808b5a526dedc6fed1cf29807210386aa9372fbab374593466bc5451dc59954e90787f08060964d95c87ef34ca5bb5368ae"
DYNAFED_SCRIPT = "75"+LIQUID_SCRIPT # Add non-OP_DEPTH opcode to make parseable non-liquid script


class TweakFedpegTest(BitcoinTestFramework):

    def set_test_params(self):
        self.num_nodes = 3
        self.setup_clean_chain = True
        self.extra_args = [[
            "-fedpegscript="+OP_TRUE_SCRIPT
        ],
        [
            "-fedpegscript="+OP_CMS_SCRIPT
        ],
        [
            "-fedpegscript="+LIQUID_SCRIPT,
            "-con_dyna_deploy_signal=1",
            "-con_dyna_deploy_start=0", # test dynafed derivation
        ]]

    def setup_network(self):
        self.setup_nodes()

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def run_test(self):
        # Test that OP_TRUE mainchain_addr/claim_script never changes
        assert_equal(self.nodes[0].getsidechaininfo()["fedpegscript"], OP_TRUE_SCRIPT)
        pegin_addr = self.nodes[0].getpeginaddress()
        for _ in range(5):
            assert_equal(pegin_addr["mainchain_address"], self.nodes[0].getpeginaddress()["mainchain_address"])
            assert_equal(self.nodes[0].tweakfedpegscript(pegin_addr["claim_script"])["script"], OP_TRUE_SCRIPT)

        # Test that OP_CMS has all keys change and matches elements-0.14 example
        pegin_addr = self.nodes[1].getpeginaddress()
        assert_equal(self.nodes[1].getsidechaininfo()["fedpegscript"], OP_CMS_SCRIPT)
        nontweak_decoded = self.nodes[1].decodescript(OP_CMS_SCRIPT)["asm"]
        tweak_decoded = self.nodes[1].decodescript(self.nodes[1].tweakfedpegscript(pegin_addr["claim_script"])["script"])["asm"]
        for nontweak, tweak in zip(re.split(" ", nontweak_decoded), re.split(" ", tweak_decoded)):
            assert_equal(len(nontweak), len(tweak)) # same opcodes/push sizes
            # All pubkeys must be different
            if len(nontweak) == 66:
                assert nontweak != tweak
            else:
                assert_equal(tweak, nontweak)

        # Elements 0.14 Daemon example
        assert_equal(self.nodes[1].tweakfedpegscript("0014008b1fdbaec5a82a9322af1640e871727245bce1")["script"],
                "522102f5bc6bc407187d06854005c366b84b411534757f4503587cf335645a620f896a2102fd90164e4e7d53417e4eacfa3f86fd39fe40594791758739e8af31eeea4e79c552ae")

        # Test Liquid-style fedpegscript with CSV emergency keys(which don't get tweaked!)
        pegin_addr = self.nodes[2].getpeginaddress()
        assert_equal(self.nodes[2].getsidechaininfo()["fedpegscript"], LIQUID_SCRIPT)
        nontweak_decoded = self.nodes[2].decodescript(LIQUID_SCRIPT)["asm"]
        tweak_decoded = self.nodes[2].decodescript(self.nodes[2].tweakfedpegscript(pegin_addr["claim_script"])["script"])["asm"]
        assert_equal(len(nontweak_decoded), len(tweak_decoded))
        tweak_match = False # All pubkeys for now must differ
        for nontweak, tweak in zip(re.split(" ", nontweak_decoded), re.split(" ", tweak_decoded)):
            assert_equal(len(nontweak), len(tweak)) # same opcodes/push sizes
            if nontweak == "OP_ELSE":
                tweak_match = True
            # All pubkeys must be different
            if len(nontweak) == 66:
                assert tweak_match == (nontweak == tweak)
            else:
                assert_equal(tweak, nontweak)


        # Liquid Daemon example:
        claim_script = "0014008b1fdbaec5a82a9322af1640e871727245bce1"
        liquid_tweaked = "745c87635b2103258857ed88024e5296436f851337451d3d68522fbb21dc5a047b965cd2f790932103ab43d77e8706a799cee3c14678574bccaca98c101217369cee987073cd2546492102ee5c8dfdf742bcc2b08386a6a3ec4b6087d39a6fd7e6f0fdeb82ecc30b11d0342102b104b6a469d8b3ccf0a671198e5f7d7010dbf2eb5587733b168f6e0d3be75760210207fc37d4877529fb0d63b1de352689627400a43f18717fa182fe0eea283bdd7921025d8724d82c61708458bc1a08ec9a7fcaf0ab6747ccf0a7d378faea07a261ab3e2102af6859d48d0a4518a4811f12adb974bbd051931e3f96f0b6ae16142c43ae6fd12102458215967f7977effc21b964bd92d870ae7eca98f343801031639150139e63ed2102cdef66bf4b5d26d0be22cabd5761970cfa84be905dc0137ad08ab634f104cb9e210297fb764f808c126f46ce0444124213bdc6a18f2904e75c9144f53bed4c19376e2103c631e77d14a5eb2fc61496ee3e9ea19d1e56e7e65a07aaa786f25ffc2921efde210270addb9011a4b41987b0848a8dc52e5442964fe5188c6a4c9320fbb9016390772103bf9aa75444d0013c46dcf10d70831b75b46a25d901fb7c6360beb2f6cac9c503210278f303dbaad1410a26d99e4dca8925fae4c90532a156c29e8ab1abf5ccaa663d210394cc0983add2dc60aa988c9faedebdc5463106184d72dd430ef24d215daf8b935f6702c00fb275522103aab896d53a8e7d6433137bbba940f9c521e085dd07e60994579b64a6d992cf79210291b7d0b1b692f8f524516ed950872e5da10fb1b808b5a526dedc6fed1cf29807210386aa9372fbab374593466bc5451dc59954e90787f08060964d95c87ef34ca5bb5368ae"
        assert_equal(self.nodes[2].tweakfedpegscript(claim_script)["script"], liquid_tweaked)

        # Advance to dynamic federations activation, which has pubkeys
        # after OP_ELSE get tweaked except the exact liquidv1 template to
        # maintain compatibility
        self.nodes[2].generate(433)
        assert_equal(self.nodes[2].getblockchaininfo()['softforks']['dynafed']['bip9']['status'], 'active')
        assert_equal(self.nodes[2].tweakfedpegscript(claim_script)["script"], liquid_tweaked)

        WSH_OP_TRUE = self.nodes[2].decodescript("51")["segwit"]["hex"]
        for i in range(20):
            block = self.nodes[2].getnewblockhex(0, {"signblockscript":WSH_OP_TRUE, "max_block_witness":3, "fedpegscript":DYNAFED_SCRIPT, "extension_space":[]})
            self.nodes[2].submitblock(block)

        assert_equal(self.nodes[2].getblockcount(), 433+20)
        # Now it will be different because emergency keys are tweaked as well
        # A bunch is the same before the OP_ELSE however
        assert_equal(self.nodes[2].tweakfedpegscript(claim_script)["script"][:1050], ("75"+liquid_tweaked)[:1050])
        assert self.nodes[2].tweakfedpegscript(claim_script)["script"] != "75"+liquid_tweaked

        # Example computed to protect against regressions
        dyna_fed_tweaked = "75745c87635b2103258857ed88024e5296436f851337451d3d68522fbb21dc5a047b965cd2f790932103ab43d77e8706a799cee3c14678574bccaca98c101217369cee987073cd2546492102ee5c8dfdf742bcc2b08386a6a3ec4b6087d39a6fd7e6f0fdeb82ecc30b11d0342102b104b6a469d8b3ccf0a671198e5f7d7010dbf2eb5587733b168f6e0d3be75760210207fc37d4877529fb0d63b1de352689627400a43f18717fa182fe0eea283bdd7921025d8724d82c61708458bc1a08ec9a7fcaf0ab6747ccf0a7d378faea07a261ab3e2102af6859d48d0a4518a4811f12adb974bbd051931e3f96f0b6ae16142c43ae6fd12102458215967f7977effc21b964bd92d870ae7eca98f343801031639150139e63ed2102cdef66bf4b5d26d0be22cabd5761970cfa84be905dc0137ad08ab634f104cb9e210297fb764f808c126f46ce0444124213bdc6a18f2904e75c9144f53bed4c19376e2103c631e77d14a5eb2fc61496ee3e9ea19d1e56e7e65a07aaa786f25ffc2921efde210270addb9011a4b41987b0848a8dc52e5442964fe5188c6a4c9320fbb9016390772103bf9aa75444d0013c46dcf10d70831b75b46a25d901fb7c6360beb2f6cac9c503210278f303dbaad1410a26d99e4dca8925fae4c90532a156c29e8ab1abf5ccaa663d210394cc0983add2dc60aa988c9faedebdc5463106184d72dd430ef24d215daf8b935f6702c00fb275522102892d66841804e5ad236f9e012bd8f1082857c9355f83aa4cd64dbe19e487d50821032d090e7b1d5047a3ac626de4b2a18e210501734895c5b7717412dac0234dd97b21026a693f0278011a09d56c04cf6b62ce8253c92a5f03a5010e6633b497ce3989085368ae"
        assert_equal(self.nodes[2].tweakfedpegscript(claim_script)["script"], dyna_fed_tweaked)

        # Optional fedpegscript arg (same arg as active script!)
        assert_equal(self.nodes[2].tweakfedpegscript(claim_script, DYNAFED_SCRIPT)["script"], dyna_fed_tweaked)

        # Older script should result in same as before
        assert_equal(self.nodes[2].tweakfedpegscript(claim_script, LIQUID_SCRIPT)["script"], liquid_tweaked)

if __name__ == '__main__':
    TweakFedpegTest().main()
