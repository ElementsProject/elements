// Copyright (c) 2017-2017 Blockstream
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <test/util/setup_common.h>
#include <string>
#include <boost/test/unit_test.hpp>
#include <primitives/block.h>
#include <script/script.h>
#include <serialize.h>


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

BOOST_AUTO_TEST_SUITE_END()


