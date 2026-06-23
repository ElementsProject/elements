// Copyright (c) 2011-2015 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <chainparams.h>
#include <coins.h>
#include <consensus/consensus.h>
#include <consensus/merkle.h>
#include <consensus/validation.h>
#include <validation.h>
#include <node/miner.h>
#include <pubkey.h>
#include <random.h>
#include <txmempool.h>
#include <uint256.h>
#include <util/strencodings.h>

#include <txdb.h>

#include <test/util/setup_common.h>

#include <boost/test/unit_test.hpp>

BOOST_FIXTURE_TEST_SUITE(pegin_spent_tests, TestingSetup)

class CCoinsViewTester : public CCoinsView {
public:
    bool IsPeginSpentCalled{false};
    bool IsPeginSpent(const std::pair<uint256, COutPoint> &outpoint) const override {
        const_cast<bool&>(IsPeginSpentCalled) = true;
        return CCoinsView::IsPeginSpent(outpoint);
    }

    CoinsCachePair m_written_sentinel{};
    CCoinsMapMemoryResource resource;
    CCoinsMap mapCoinsWritten{0, CCoinsMap::hasher{}, CCoinsMap::key_equal{}, &resource};
    bool BatchWrite(CoinsViewCacheCursor& cursor, const uint256 &hashBlock) override {
        mapCoinsWritten.clear();
        m_written_sentinel.second.SelfRef(m_written_sentinel);
        for (auto it{cursor.Begin()}; it != cursor.End(); it = cursor.NextAndMaybeErase(*it)) {
            auto [dest_it, inserted] = mapCoinsWritten.try_emplace(it->first);
            dest_it->second.coin = it->second.coin;
            dest_it->second.peginSpent = it->second.peginSpent;
            if (it->second.IsDirty()) CCoinsCacheEntry::SetDirty(*dest_it, m_written_sentinel);
            if (it->second.IsFresh()) CCoinsCacheEntry::SetFresh(*dest_it, m_written_sentinel);
            if (it->second.IsPegin()) CCoinsCacheEntry::SetPegin(*dest_it, m_written_sentinel);
        }
        return true;
    }

    CCoinsViewTester() {
        m_written_sentinel.second.SelfRef(m_written_sentinel);
    }
};

BOOST_AUTO_TEST_CASE(PeginSpent_validity)
{
    CCoinsViewTester coins;
    CCoinsViewCache coinsCache(&coins);
    Coin ret;

    //Basic insert of blank outpoint pair, blank COutPoint allows for checking coinsCache

    std::pair<uint256, COutPoint> outpoint = std::make_pair(GetRandHash(), COutPoint(Txid::FromUint256(GetRandHash()), 42));
    BOOST_CHECK(!coinsCache.GetCoin(outpoint.second));

    //Checking for pegin spentness should not create an entry
    BOOST_CHECK(!coinsCache.IsPeginSpent(outpoint));
    BOOST_CHECK(coins.IsPeginSpentCalled);
    coins.IsPeginSpentCalled = false;
    BOOST_CHECK(!coinsCache.IsPeginSpent(outpoint));
    BOOST_CHECK(!coins.IsPeginSpentCalled);

    coinsCache.SetPeginSpent(outpoint, true);
    BOOST_CHECK(coinsCache.IsPeginSpent(outpoint));
    coinsCache.SetPeginSpent(outpoint, false);
    BOOST_CHECK(!coinsCache.IsPeginSpent(outpoint));
    coinsCache.SetPeginSpent(outpoint, true);
    BOOST_CHECK(coinsCache.IsPeginSpent(outpoint));

    //Check for slightly similar non-existent entries
    std::pair<uint256, COutPoint> outpoint2(outpoint);
    outpoint2.second.n = 0;
    BOOST_CHECK(!coinsCache.IsPeginSpent(outpoint2));

    CCoinsMapMemoryResource resource;
    CCoinsMap mapCoins{0, CCoinsMap::hasher{}, CCoinsMap::key_equal{}, &resource};
    CoinsCachePair sentinel{};
    sentinel.second.SelfRef(sentinel);
    size_t usage{0};
    std::pair<uint256, COutPoint> outpoint3(std::make_pair(GetRandHash(), COutPoint(Txid::FromUint256(GetRandHash()), 42)));

    //Attempt batch write of non-dirty pegin, no effect
    {
        auto [it, inserted] = mapCoins.try_emplace(outpoint3);
        it->second.peginSpent = true;
        CCoinsCacheEntry::SetPegin(*it, sentinel);
    }
    {
        auto cursor{CoinsViewCacheCursor(usage, sentinel, mapCoins, /*will_erase=*/true)};
        coinsCache.BatchWrite(cursor, uint256());
    }
    //Check for effect
    coins.IsPeginSpentCalled = false;
    BOOST_CHECK(!coinsCache.IsPeginSpent(outpoint3));
    BOOST_CHECK(coins.IsPeginSpentCalled);
    mapCoins.clear();
    sentinel.second.SelfRef(sentinel);

    //Write again with pegin, dirty && fresh flags, but unspent. No effect.
    {
        auto [it, inserted] = mapCoins.try_emplace(outpoint3);
        it->second.peginSpent = false;
        CCoinsCacheEntry::SetPegin(*it, sentinel);
        CCoinsCacheEntry::SetDirty(*it, sentinel);
        CCoinsCacheEntry::SetFresh(*it, sentinel);
    }
    {
        auto cursor{CoinsViewCacheCursor(usage, sentinel, mapCoins, /*will_erase=*/true)};
        coinsCache.BatchWrite(cursor, uint256());
    }
    //Check for effect
    coins.IsPeginSpentCalled = false;
    BOOST_CHECK(!coinsCache.IsPeginSpent(outpoint3));
    BOOST_CHECK(coins.IsPeginSpentCalled);
    mapCoins.clear();
    sentinel.second.SelfRef(sentinel);

    //Re-mark as spent. It's super effective.
    {
        auto [it, inserted] = mapCoins.try_emplace(outpoint3);
        it->second.peginSpent = true;
        CCoinsCacheEntry::SetPegin(*it, sentinel);
        CCoinsCacheEntry::SetDirty(*it, sentinel);
        CCoinsCacheEntry::SetFresh(*it, sentinel);
    }
    {
        auto cursor{CoinsViewCacheCursor(usage, sentinel, mapCoins, /*will_erase=*/true)};
        coinsCache.BatchWrite(cursor, uint256());
    }
    //Check for effect
    coins.IsPeginSpentCalled = false;
    BOOST_CHECK(coinsCache.IsPeginSpent(outpoint3));
    BOOST_CHECK(!coins.IsPeginSpentCalled);
    mapCoins.clear();
    sentinel.second.SelfRef(sentinel);

    //Add an entry we never IsPeginSpent'd first (ie added to cache via SetPeginSpent)
    std::pair<uint256, COutPoint> outpoint4(std::make_pair(GetRandHash(), COutPoint(Txid::FromUint256(GetRandHash()), 42)));
    coinsCache.SetPeginSpent(outpoint4, true);

    // Check the final state of coinsCache.mapCoins is sane.
    BOOST_CHECK_EQUAL(coins.mapCoinsWritten.size(), 0U);
    coinsCache.Flush();
    BOOST_CHECK_EQUAL(coins.mapCoinsWritten.size(), 4U);
    BOOST_CHECK(coins.mapCoinsWritten[outpoint].IsDirty());
    BOOST_CHECK(coins.mapCoinsWritten[outpoint].IsFresh());
    BOOST_CHECK(coins.mapCoinsWritten[outpoint].IsPegin());
    BOOST_CHECK_EQUAL(coins.mapCoinsWritten[outpoint].peginSpent, true);
    BOOST_CHECK(!coins.mapCoinsWritten[outpoint2].IsDirty());
    BOOST_CHECK(coins.mapCoinsWritten[outpoint2].IsFresh());
    BOOST_CHECK(coins.mapCoinsWritten[outpoint2].IsPegin());
    BOOST_CHECK_EQUAL(coins.mapCoinsWritten[outpoint2].peginSpent, false);
    BOOST_CHECK(coins.mapCoinsWritten[outpoint3].IsDirty());
    BOOST_CHECK(coins.mapCoinsWritten[outpoint3].IsFresh());
    BOOST_CHECK(coins.mapCoinsWritten[outpoint3].IsPegin());
    BOOST_CHECK_EQUAL(coins.mapCoinsWritten[outpoint3].peginSpent, true);
    BOOST_CHECK(coins.mapCoinsWritten[outpoint4].IsDirty());
    BOOST_CHECK(coins.mapCoinsWritten[outpoint4].IsFresh());
    BOOST_CHECK(coins.mapCoinsWritten[outpoint4].IsPegin());
    BOOST_CHECK_EQUAL(coins.mapCoinsWritten[outpoint3].peginSpent, true);

    // CCoinsViewCache should lose outpoint2 in BatchWrite logic
    CCoinsViewTester coins2;
    CCoinsViewCache coinsCache2(&coins2);
    {
        size_t written_usage{0};
        for (auto& [key, entry] : coins.mapCoinsWritten) {
            written_usage += entry.coin.DynamicMemoryUsage();
        }
        auto cursor{CoinsViewCacheCursor(written_usage, coins.m_written_sentinel, coins.mapCoinsWritten, /*will_erase=*/true)};
        BOOST_CHECK(coinsCache2.BatchWrite(cursor, uint256()));
    }
    coinsCache2.Flush();
    BOOST_CHECK_EQUAL(coins2.mapCoinsWritten.size(), 3U);
    BOOST_CHECK(coins2.mapCoinsWritten[outpoint].IsDirty());
    BOOST_CHECK(coins2.mapCoinsWritten[outpoint].IsFresh());
    BOOST_CHECK(coins2.mapCoinsWritten[outpoint].IsPegin());
    BOOST_CHECK_EQUAL(coins2.mapCoinsWritten[outpoint].peginSpent, true);
    BOOST_CHECK(coins2.mapCoinsWritten[outpoint3].IsDirty());
    BOOST_CHECK(coins2.mapCoinsWritten[outpoint3].IsFresh());
    BOOST_CHECK(coins2.mapCoinsWritten[outpoint3].IsPegin());
    BOOST_CHECK_EQUAL(coins2.mapCoinsWritten[outpoint3].peginSpent, true);
    BOOST_CHECK(coins2.mapCoinsWritten[outpoint4].IsDirty());
    BOOST_CHECK(coins2.mapCoinsWritten[outpoint4].IsFresh());
    BOOST_CHECK(coins2.mapCoinsWritten[outpoint4].IsPegin());
    BOOST_CHECK_EQUAL(coins2.mapCoinsWritten[outpoint4].peginSpent, true);
}

BOOST_AUTO_TEST_SUITE_END()
