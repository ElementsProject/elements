// Copyright (c) 2017-2017 Blockstream
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <boost/test/unit_test.hpp>
#include <dynafed.h>
#include <primitives/block.h>
#include <script/script.h>
#include <serialize.h>
#include <string>
#include <test/util/setup_common.h>


BOOST_FIXTURE_TEST_SUITE(dynafed_tests, BasicTestingSetup)

// Ensure the paam roots doesn't change unexpectedly.
BOOST_AUTO_TEST_CASE(dynafed_params_root)
{
    CScript signblockscript(opcodetype(1));
    uint32_t signblock_wl(2);
    CScript fp_program(opcodetype(3));
    CScript fp_script(opcodetype(4));
    std::vector<std::vector<unsigned char>> ext{ {5, 6}, {7} };

    DynaFedParamEntry compact_entry = DynaFedParamEntry(signblockscript, signblock_wl, uint256());
    BOOST_CHECK_EQUAL(
        compact_entry.CalculateRoot().GetHex(),
        "f98f149fd11da6fbe26d0ee53cadd28372fa9eed2cb7080f41da7ca311531777"
    );

    DynaFedParamEntry full_entry =
        DynaFedParamEntry(signblockscript, signblock_wl, fp_program, fp_script, ext);
    BOOST_CHECK_EQUAL(
        full_entry.CalculateRoot().GetHex(),
        "8eb1b83cce69a3d8b0bfb7fbe77ae8f1d24b57a9cae047b8c0aba084ad878249"
    );

    DynaFedParams params = DynaFedParams(compact_entry, full_entry);
    BOOST_CHECK_EQUAL(
        params.CalculateRoot().GetHex(),
        "113160f76dc17fe367a2def79aefe06feeea9c795310c9e88aeedc23e145982e"
    );
}

BOOST_AUTO_TEST_CASE(parse_fedpegscript_multisig)
{
    int t = 0;
    int n = 0;

    auto simplebytes = ParseHex("512103dff4923d778550cc13ce0d887d737553b4b58f4e8e886507fc39f5e447b2186451ae");

    CScript simple{simplebytes.begin(), simplebytes.end()};

    BOOST_CHECK(ParseFedPegQuorum(simple, t, n));
    BOOST_CHECK_EQUAL(t, 1);
    BOOST_CHECK_EQUAL(n, 1);

    auto liquidv1bytes = ParseHex("5b21020e0338c96a8870479f2396c373cc7696ba124e8635d41b0ea581112b678172612102675333a4e4b8fb51d9d4e22fa5a8eaced3fdac8a8cbf9be8c030f75712e6af992102896807d54bc55c24981f24a453c60ad3e8993d693732288068a23df3d9f50d4821029e51a5ef5db3137051de8323b001749932f2ff0d34c82e96a2c2461de96ae56c2102a4e1a9638d46923272c266631d94d36bdb03a64ee0e14c7518e49d2f29bc401021031c41fdbcebe17bec8d49816e00ca1b5ac34766b91c9f2ac37d39c63e5e008afb2103079e252e85abffd3c401a69b087e590a9b86f33f574f08129ccbd3521ecf516b2103111cf405b627e22135b3b3733a4a34aa5723fb0f58379a16d32861bf576b0ec2210318f331b3e5d38156da6633b31929c5b220349859cc9ca3d33fb4e68aa08401742103230dae6b4ac93480aeab26d000841298e3b8f6157028e47b0897c1e025165de121035abff4281ff00660f99ab27bb53e6b33689c2cd8dcd364bc3c90ca5aea0d71a62103bd45cddfacf2083b14310ae4a84e25de61e451637346325222747b157446614c2103cc297026b06c71cbfa52089149157b5ff23de027ac5ab781800a578192d175462103d3bde5d63bdb3a6379b461be64dad45eabff42f758543a9645afd42f6d4248282103ed1e8d5109c9ed66f7941bc53cc71137baa76d50d274bda8d5e8ffbd6e61fe9a5fae736402c00fb269522103aab896d53a8e7d6433137bbba940f9c521e085dd07e60994579b64a6d992cf79210291b7d0b1b692f8f524516ed950872e5da10fb1b808b5a526dedc6fed1cf29807210386aa9372fbab374593466bc5451dc59954e90787f08060964d95c87ef34ca5bb53ae68");

    CScript liquidv1{liquidv1bytes.begin(), liquidv1bytes.end()};

    t = 0;
    n = 0;
    BOOST_CHECK(ParseFedPegQuorum(liquidv1, t, n));
    BOOST_CHECK_EQUAL(t, 11);
    BOOST_CHECK_EQUAL(n, 15);

    auto optruebytes = ParseHex("51");

    CScript optrue{optruebytes.begin(), optruebytes.end()};

    t = 0;
    n = 0;
    BOOST_CHECK(ParseFedPegQuorum(optrue, t, n));
    BOOST_CHECK_EQUAL(t, 1);
    BOOST_CHECK_EQUAL(n, 0);

    auto op3bytes = ParseHex("53");

    CScript op3{op3bytes.begin(), op3bytes.end()};

    t = 0;
    n = 0;
    BOOST_CHECK(ParseFedPegQuorum(op3, t, n));
    BOOST_CHECK_EQUAL(t, 3);
    BOOST_CHECK_EQUAL(n, 0);
}

BOOST_AUTO_TEST_SUITE_END()
