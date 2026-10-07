// Copyright (c) 2026 The Elements Core developers
// Distributed under the MIT/X11 software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <mainchainrpc.h>

#include <common/args.h>
#include <test/util/setup_common.h>

#include <boost/test/unit_test.hpp>
#include <tinyformat.h>

BOOST_FIXTURE_TEST_SUITE(mainchainrpc_tests, BasicTestingSetup)

BOOST_AUTO_TEST_CASE(validation_rpc_timeout)
{
    ArgsManager argsman;

    // Unset -mainchainrpctimeout: the 900s default is capped
    BOOST_CHECK_EQUAL(GetValidationRPCTimeout(argsman), MAX_VALIDATION_RPC_TIMEOUT);

    // Values below the cap are honored
    argsman.ForceSetArg("-mainchainrpctimeout", "10");
    BOOST_CHECK_EQUAL(GetValidationRPCTimeout(argsman), 10);

    // Values above the cap are clamped to it
    argsman.ForceSetArg("-mainchainrpctimeout", "3600");
    BOOST_CHECK_EQUAL(GetValidationRPCTimeout(argsman), MAX_VALIDATION_RPC_TIMEOUT);

    // The cap boundary itself is honored
    argsman.ForceSetArg("-mainchainrpctimeout", strprintf("%d", MAX_VALIDATION_RPC_TIMEOUT));
    BOOST_CHECK_EQUAL(GetValidationRPCTimeout(argsman), MAX_VALIDATION_RPC_TIMEOUT);

    // 0 does not mean "no timeout" (libevent substitutes its own internal
    // defaults for 0), so it is clamped to the lower bound instead
    argsman.ForceSetArg("-mainchainrpctimeout", "0");
    BOOST_CHECK_EQUAL(GetValidationRPCTimeout(argsman), 1);
}

BOOST_AUTO_TEST_SUITE_END()
