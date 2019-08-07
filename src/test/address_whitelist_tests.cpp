// Copyright (c) 2019 CommerceBlock developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "test/test_bitcoin.h"
#include "request.h"
#include "policy/policy.h"
#include "policy/requestlist.h"
#include "chainparams.h"
#include "validation.h"
#include "init.h"

#include <boost/test/unit_test.hpp>

struct WhitelistTestingSetup : public TestingSetup {
    WhitelistTestingSetup() : TestingSetup(CBaseChainParams::REGTEST, "", "76a914567884b53d417d36b37a0409521f4644a7f46ffe88ac") {}
    //WhitelistTestingSetup() : TestingSetup(CBaseChainParams::REGTEST, "", "") {}
};

BOOST_FIXTURE_TEST_SUITE(address_whitelist_tests, WhitelistTestingSetup)

BOOST_AUTO_TEST_CASE(mandatory_coinbase_destination)
{
    BOOST_CHECK(Params().GetConsensus().mandatory_coinbase_destination != CScript());
    	CTxDestination man_con_dest;
    	BOOST_CHECK(ExtractDestination(Params().GetConsensus().mandatory_coinbase_destination, man_con_dest));
    	BOOST_CHECK(fRequireWhitelistCheck);
	InitWhitelistDefaults();
	BOOST_CHECK(addressWhitelist.is_whitelisted(man_con_dest));


}

BOOST_AUTO_TEST_SUITE_END()
