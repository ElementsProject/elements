// Copyright (c) 2015-2016 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_TEST_TEST_BITCOIN_H
#define BITCOIN_TEST_TEST_BITCOIN_H

#include "chainparamsbase.h"
#include "key.h"
#include "pubkey.h"
#include "txdb.h"
#include "txmempool.h"

#include <boost/filesystem.hpp>
#include <boost/thread.hpp>

/** Basic testing setup.
 * This just configures logging and chain parameters.
 */
struct BasicTestingSetup {
    ECCVerifyHandle globalVerifyHandle;

    BasicTestingSetup(const std::string& chainName = CBaseChainParams::MAIN, const std::string& fedpegscript = "", const std::string& con_mandatorycoinbase="");
    ~BasicTestingSetup();
};

/** Testing setup that configures a complete environment.
 * Included are data directory, coins database, script check threads setup.
 */
class CConnman;
struct TestingSetup: public BasicTestingSetup {
    CCoinsViewDB *pcoinsdbview;
    boost::filesystem::path pathTemp;
    boost::thread_group threadGroup;
    CConnman* connman;
    CKey coinbaseKey; // private/public key needed to spend coinbase transactions

    TestingSetup(const std::string& chainName = CBaseChainParams::MAIN, const std::string& fedpegscript = "", const std::string& con_mandatorycoinbase = "");
    ~TestingSetup();
};

class CBlock;
struct CMutableTransaction;
class CScript;

//
// Testing fixture that pre-creates a
// 100-block REGTEST-mode block chain
//
struct TestChain100Setup : public TestingSetup {
    TestChain100Setup();

    // Create a new block with just given transactions, coinbase paying to
    // scriptPubKey, and try to add it to the current chain.
    CBlock CreateAndProcessBlock(const std::vector<CMutableTransaction>& txns,
                                 const CScript& scriptPubKey);

    ~TestChain100Setup();

    std::vector<CTransaction> coinbaseTxns; // For convenience, coinbase transactions
};

class CTxMemPoolEntry;
class CTxMemPool;

struct TestMemPoolEntryHelper
{
    // Default values
    CAmount nFee;
    CAsset feeAsset;
    int64_t nTime;
    double dPriority;
    unsigned int nHeight;
    bool spendsCoinbase;
    unsigned int sigOpCost;
    LockPoints lp;
    std::set<std::pair<uint256, COutPoint> > setPeginsSpent;

    TestMemPoolEntryHelper() :
        nFee(0), feeAsset(CAsset()), nTime(0), dPriority(0.0), nHeight(1),
        spendsCoinbase(false), sigOpCost(4) { }

    CTxMemPoolEntry FromTx(const CMutableTransaction &tx, CTxMemPool *pool = NULL);
    CTxMemPoolEntry FromTx(const CTransaction &tx, CTxMemPool *pool = NULL);

    // Change the default value
    TestMemPoolEntryHelper &Fee(CAmount _fee) { nFee = _fee; return *this; }
    TestMemPoolEntryHelper &FeeAsset(CAsset _feeAsset) { feeAsset = _feeAsset; return *this; }
    TestMemPoolEntryHelper &Time(int64_t _time) { nTime = _time; return *this; }
    TestMemPoolEntryHelper &Priority(double _priority) { dPriority = _priority; return *this; }
    TestMemPoolEntryHelper &Height(unsigned int _height) { nHeight = _height; return *this; }
    TestMemPoolEntryHelper &SpendsCoinbase(bool _flag) { spendsCoinbase = _flag; return *this; }
    TestMemPoolEntryHelper &SigOpsCost(unsigned int _sigopsCost) { sigOpCost = _sigopsCost; return *this; }
    TestMemPoolEntryHelper &WithdrawsSpent(std::set<std::pair<uint256, COutPoint> >& _setPeginsSpent) { setPeginsSpent = _setPeginsSpent; return *this; }
};
#endif
