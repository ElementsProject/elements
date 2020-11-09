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

    DynaFedParamEntry compact_entry = DynaFedParamEntry(signblockscript, signblock_wl);
    BOOST_CHECK_EQUAL(
        compact_entry.CalculateRoot().GetHex(),
        "dff5f3793abc06a6d75e80fe3cfd47406f732fa4ec9305960ae2a229222a1ad5"
    );

    DynaFedParamEntry full_entry =
        DynaFedParamEntry(signblockscript, signblock_wl, fp_program, fp_script, ext);
    BOOST_CHECK_EQUAL(
        full_entry.CalculateRoot().GetHex(),
        "175be2087ba7cc0e33348bef493bd3e34f31f64bf9226e5881ab310dafa432ff"
    );

    DynaFedParams params = DynaFedParams(compact_entry, full_entry);
    BOOST_CHECK_EQUAL(
        params.CalculateRoot().GetHex(),
        "e56cf79487952dfa85fe6a85829600adc19714ba6ab1157fdff02b25ae60cee2"
    );
}

BOOST_AUTO_TEST_SUITE_END()


