// Copyright (c) 2011-2015 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "chainparams.h"
#include "coins.h"
#include "consensus/consensus.h"
#include "consensus/merkle.h"
#include "consensus/validation.h"
#include "main.h"
#include "miner.h"
#include "pubkey.h"
#include "script/standard.h"
#include "txmempool.h"
#include "uint256.h"
#include "util.h"
#include "utilstrencodings.h"

#include "txdb.h"

#include "test/test_bitcoin.h"

#include <boost/test/unit_test.hpp>

BOOST_FIXTURE_TEST_SUITE(withdrawspent_tests, TestingSetup)

class CCoinsViewTester : public CCoinsView {
public:
    bool IsWithdrawSpentCalled;
    bool IsWithdrawSpent(const std::pair<uint256, COutPoint> &outpoint) const {
        const_cast<bool&>(IsWithdrawSpentCalled) = true;
        return CCoinsView::IsWithdrawSpent(outpoint);
    }

    CCoinsMap mapCoinsWritten;
    bool BatchWrite(CCoinsMap &mapCoins, const uint256 &hashBlock) {
        mapCoinsWritten = mapCoins;
        return CCoinsView::BatchWrite(mapCoins, hashBlock);
    }

    CCoinsViewTester() : IsWithdrawSpentCalled(false) {}
};

BOOST_AUTO_TEST_CASE(withdrawspent_validity)
{
    CCoinsViewTester coins;
    CCoinsViewCache coinsCache(&coins);
    CCoins ret;

    //Basic insert of blank outpoint pair, blank COutPoint allows for checking coinsCache

    std::pair<uint256, COutPoint> outpoint = std::make_pair(GetRandHash(), COutPoint(GetRandHash(), 42));
    BOOST_CHECK(!coinsCache.GetCoins(uint256(), ret));

    //Checking for withdraw spentness should not create an entry
    BOOST_CHECK(!coinsCache.IsWithdrawSpent(outpoint));
    BOOST_CHECK(coins.IsWithdrawSpentCalled);
    coins.IsWithdrawSpentCalled = false;
    BOOST_CHECK(!coinsCache.IsWithdrawSpent(outpoint));
    BOOST_CHECK(!coins.IsWithdrawSpentCalled);

    coinsCache.SetWithdrawSpent(outpoint, true);
    BOOST_CHECK(coinsCache.IsWithdrawSpent(outpoint));
    coinsCache.SetWithdrawSpent(outpoint, false);
    BOOST_CHECK(!coinsCache.IsWithdrawSpent(outpoint));
    coinsCache.SetWithdrawSpent(outpoint, true);
    BOOST_CHECK(coinsCache.IsWithdrawSpent(outpoint));

    //Check for slightly similar non-existent entries
    std::pair<uint256, COutPoint> outpoint2(outpoint);
    outpoint2.second.n = 0;
    BOOST_CHECK(!coinsCache.IsWithdrawSpent(outpoint2));

    CCoinsMap mapCoins;
    CCoinsCacheEntry entry;
    std::pair<uint256, COutPoint> outpoint3(std::make_pair(GetRandHash(), COutPoint(GetRandHash(), 42)));

    //Attempt batch write of non-dirty withdraw, no effect
    entry.flags = CCoinsCacheEntry::WITHDRAW;
    entry.withdrawSpent = true;
    mapCoins.insert(std::make_pair(outpoint3, entry));
    coinsCache.BatchWrite(mapCoins, uint256());
    //Check for effect
    coins.IsWithdrawSpentCalled = false;
    BOOST_CHECK(!coinsCache.IsWithdrawSpent(outpoint3));
    BOOST_CHECK(coins.IsWithdrawSpentCalled);
    BOOST_CHECK(mapCoins.size() == 0);

    //Write again with withdraw, dirty && fresh flags, but unspent. No effect.
    entry.withdrawSpent = false;
    entry.flags |= CCoinsCacheEntry::DIRTY | CCoinsCacheEntry::FRESH;
    mapCoins.insert(std::make_pair(outpoint3, entry));
    coinsCache.BatchWrite(mapCoins, uint256());
    //Check for effect
    coins.IsWithdrawSpentCalled = false;
    BOOST_CHECK(!coinsCache.IsWithdrawSpent(outpoint3));
    BOOST_CHECK(coins.IsWithdrawSpentCalled);
    BOOST_CHECK(mapCoins.size() == 0);

    //Re-mark as spent. It's super effective.
    entry.withdrawSpent = true;
    mapCoins.insert(std::make_pair(outpoint3, entry));
    coinsCache.BatchWrite(mapCoins, uint256());
    //Check for effect
    coins.IsWithdrawSpentCalled = false;
    BOOST_CHECK(coinsCache.IsWithdrawSpent(outpoint3));
    BOOST_CHECK(!coins.IsWithdrawSpentCalled);
    BOOST_CHECK(mapCoins.size() == 0);

    //Add an entry we never IsWithdrawSpent'd first (ie added to cache via SetWithdrawSpent)
    std::pair<uint256, COutPoint> outpoint4(std::make_pair(GetRandHash(), COutPoint(GetRandHash(), 42)));
    coinsCache.SetWithdrawSpent(outpoint4, true);

    // Check the final state of coinsCache.mapCoins is sane.
    BOOST_CHECK_EQUAL(coins.mapCoinsWritten.size(), 0);
    coinsCache.Flush();
    BOOST_CHECK_EQUAL(coins.mapCoinsWritten.size(), 4);
    BOOST_CHECK_EQUAL(coins.mapCoinsWritten[outpoint].flags, CCoinsCacheEntry::DIRTY | CCoinsCacheEntry::FRESH | CCoinsCacheEntry::WITHDRAW);
    BOOST_CHECK_EQUAL(coins.mapCoinsWritten[outpoint].withdrawSpent, true);
    BOOST_CHECK_EQUAL(coins.mapCoinsWritten[outpoint2].flags, CCoinsCacheEntry::FRESH | CCoinsCacheEntry::WITHDRAW);
    BOOST_CHECK_EQUAL(coins.mapCoinsWritten[outpoint2].withdrawSpent, false);
    BOOST_CHECK_EQUAL(coins.mapCoinsWritten[outpoint3].flags, CCoinsCacheEntry::DIRTY | CCoinsCacheEntry::FRESH | CCoinsCacheEntry::WITHDRAW);
    BOOST_CHECK_EQUAL(coins.mapCoinsWritten[outpoint3].withdrawSpent, true);
    BOOST_CHECK_EQUAL(coins.mapCoinsWritten[outpoint4].flags, CCoinsCacheEntry::DIRTY | CCoinsCacheEntry::FRESH | CCoinsCacheEntry::WITHDRAW);
    BOOST_CHECK_EQUAL(coins.mapCoinsWritten[outpoint3].withdrawSpent, true);

    // CCoinsViewCache should lose outpoint2 in BatchWrite logic
    CCoinsViewTester coins2;
    CCoinsViewCache coinsCache2(&coins2);
    BOOST_CHECK(coinsCache2.BatchWrite(coins.mapCoinsWritten, uint256()));
    coinsCache2.Flush();
    BOOST_CHECK_EQUAL(coins2.mapCoinsWritten.size(), 3);
    BOOST_CHECK_EQUAL(coins2.mapCoinsWritten[outpoint].flags, CCoinsCacheEntry::DIRTY | CCoinsCacheEntry::FRESH | CCoinsCacheEntry::WITHDRAW);
    BOOST_CHECK_EQUAL(coins2.mapCoinsWritten[outpoint].withdrawSpent, true);
    BOOST_CHECK_EQUAL(coins2.mapCoinsWritten[outpoint3].flags, CCoinsCacheEntry::DIRTY | CCoinsCacheEntry::FRESH | CCoinsCacheEntry::WITHDRAW);
    BOOST_CHECK_EQUAL(coins2.mapCoinsWritten[outpoint3].withdrawSpent, true);
    BOOST_CHECK_EQUAL(coins2.mapCoinsWritten[outpoint4].flags, CCoinsCacheEntry::DIRTY | CCoinsCacheEntry::FRESH | CCoinsCacheEntry::WITHDRAW);
    BOOST_CHECK_EQUAL(coins2.mapCoinsWritten[outpoint4].withdrawSpent, true);
}

BOOST_AUTO_TEST_SUITE_END()
