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
#include "random.h"

#include "txdb.h"

#include "test/test_bitcoin.h"

#include <boost/test/unit_test.hpp>

BOOST_FIXTURE_TEST_SUITE(lockedutxo_tests, TestingSetup)

BOOST_AUTO_TEST_CASE(Getlocked_validity)
{
    std::multimap<uint256, std::pair<COutPoint, CAmount> > mLocksCreated;

    uint256 gen0 = uint256S("0");

    CMutableTransaction mtx0;
    mtx0.vout.push_back(CTxOut(CTxOutValue(1000), CScript()));
    CMutableTransaction mtx1;
    mtx1.vout.push_back(CTxOut(CTxOutValue(100), CScript()));
    CMutableTransaction mtx2;
    mtx2.vout.push_back(CTxOut(CTxOutValue(10), CScript()));
    CMutableTransaction mtx3;
    mtx3.vout.push_back(CTxOut(CTxOutValue(1), CScript()));

    //Push vout of size 1 for each CCoin
    pcoinsTip->ModifyCoins(uint256S("0"))->FromTx(CTransaction(mtx0), 0);
    pcoinsTip->ModifyCoins(uint256S("1"))->FromTx(CTransaction(mtx1), 0);
    pcoinsTip->ModifyCoins(uint256S("2"))->FromTx(CTransaction(mtx2), 0);
    pcoinsTip->ModifyCoins(uint256S("3"))->FromTx(CTransaction(mtx3), 0);

    //These coins need to exist, otherwise they will be deleted during GetLockedOutputs call
    CAmount value = 1000;
    mLocksCreated.insert(std::make_pair(gen0, std::make_pair(COutPoint(uint256S("0"), 0), value)));
    value = 100;
    mLocksCreated.insert(std::make_pair(gen0, std::make_pair(COutPoint(uint256S("1"), 0), value)));
    value = 10;
    mLocksCreated.insert(std::make_pair(gen0, std::make_pair(COutPoint(uint256S("2"), 0), value)));
    value = 1;
    mLocksCreated.insert(std::make_pair(gen0, std::make_pair(COutPoint(uint256S("3"), 0), value)));

    //Write list of 4
    pblocktree->WriteLocksCreated(mLocksCreated);

    //Read the list back, ensure it was written correctly
    std::vector<std::pair<COutPoint, CAmount> > locksCreated;
    assert(pblocktree->ReadLocksCreated(gen0, locksCreated));
    assert(locksCreated.size() == 4);
    std::multimap<uint256, std::pair<COutPoint, CAmount> >::iterator it = mLocksCreated.equal_range(gen0).first;
    assert(locksCreated[0] == it->second);
    std::advance(it, 1);
    assert(locksCreated[1] == it->second);
    std::advance(it, 1);
    assert(locksCreated[2] == it->second);
    std::advance(it, 1);
    assert(locksCreated[3] == it->second);

    //Call GetLockedOutputs to get the single output large enough
    CAmount desiredAmount = 101;
    std::vector<std::pair<COutPoint, CAmount> > res;
    assert(GetLockedOutputs(gen0, desiredAmount, res));
    assert(res.size() == 1 && res[0].second == 1000);

    //Read it back again
    std::vector<std::pair<COutPoint, CAmount> > locksCreated2;
    assert(pblocktree->ReadLocksCreated(gen0, locksCreated2));
    assert(locksCreated2.size() == 4);

    //Write a blank list and read it back
    std::vector<std::pair<COutPoint, CAmount> > locksCreated3;
    pblocktree->ReWriteLocksCreated(gen0, locksCreated3);
    assert(pblocktree->ReadLocksCreated(gen0, locksCreated3));
    assert(locksCreated3.size() == 0);

    //Delete the largest element, and read back
    locksCreated.erase(locksCreated.begin());
    pblocktree->ReWriteLocksCreated(gen0, locksCreated);
    assert(pblocktree->ReadLocksCreated(gen0, locksCreated));
    assert(locksCreated.size() == 3);

    //Find at least 2 utxos to fulfill amount
    std::vector<std::pair<COutPoint, CAmount> > res2;
    assert(GetLockedOutputs(gen0, desiredAmount, res2));
    assert(res2.size() > 1);

    //Delete the second-largest element, and read back
    locksCreated.erase(locksCreated.begin());
    pblocktree->ReWriteLocksCreated(gen0, locksCreated);
    assert(pblocktree->ReadLocksCreated(gen0, locksCreated));
    assert(locksCreated.size() == 2);

    //Will not find enough, but will return the last 2
    std::vector<std::pair<COutPoint, CAmount> > res3;
    assert(!GetLockedOutputs(gen0, desiredAmount, res3));
    assert(res3.size() == 2);


    // Make sure this terminates
    for (unsigned int i = 0; i < 10000; i++) {
        // Make random set of 100 utxos
        std::vector<std::pair<COutPoint, CAmount> > locksCreated4;
        for (unsigned int j = 0; j < GetRand(100); j++) {
            locksCreated4.push_back(std::make_pair(COutPoint(GetRandHash(), GetRand(10)), GetRand(100000)));
        }
        pblocktree->ReWriteLocksCreated(gen0, locksCreated4);
        CAmount desiredAmount = GetRand(1000000);
        std::vector<std::pair<COutPoint, CAmount> > res;
        GetLockedOutputs(gen0, desiredAmount, res);
    }
}

BOOST_AUTO_TEST_SUITE_END()
