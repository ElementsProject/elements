// Copyright (c) 2011-2016 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#define BOOST_TEST_MODULE Bitcoin Test Suite

#include "test_bitcoin.h"

#include "chainparams.h"
#include "consensus/consensus.h"
#include "consensus/validation.h"
#include "consensus/merkle.h"
#include "key.h"
#include "validation.h"
#include "miner.h"
#include "net_processing.h"
#include "pubkey.h"
#include "random.h"
#include "txdb.h"
#include "txmempool.h"
#include "ui_interface.h"
#include "rpc/server.h"
#include "rpc/register.h"
#include "script/sigcache.h"

#include "test/testutil.h"

#include <memory>

#include <boost/filesystem.hpp>
#include <boost/test/unit_test.hpp>
#include <boost/thread.hpp>

std::unique_ptr<CConnman> g_connman;
FastRandomContext insecure_rand_ctx(true);

extern bool fPrintToConsole;
extern void noui_connect();

BasicTestingSetup::BasicTestingSetup(const std::string& chainName, const std::string& fedpegscript)
{
        ECC_Start();
        SetupEnvironment();
        SetupNetworking();
        InitSignatureCache();
        InitRangeproofCache();
        InitSurjectionproofCache();
        fPrintToDebugLog = false; // don't want to write to debug.log file
        fCheckBlockIndex = true;
        // Hack to allow testing of fedpeg args
        if (!fedpegscript.empty()) {
            SoftSetArg("-fedpegscript", fedpegscript);
        }
        // MAX_MONEY
        SoftSetArg("-initialfreecoins", "2100000000000000");
        SoftSetArg("-policycoins", "2100000000000000");
        SelectParams(chainName);
        noui_connect();
}

BasicTestingSetup::~BasicTestingSetup()
{
        ECC_Stop();
        g_connman.reset();
}

TestingSetup::TestingSetup(const std::string& chainName, const std::string& fedpegscript) : BasicTestingSetup(chainName, fedpegscript)
{
    const CChainParams& chainparams = Params();
        // Ideally we'd move all the RPC tests to the functional testing framework
        // instead of unit tests, but for now we need these here.

        RegisterAllCoreRPCCommands(tableRPC);

    int gen_size = Params().GenesisBlock().vtx.size();

    // Make genesis second transaction(with spendable outputs) use out spend-key
    coinbaseKey.MakeNewKey(true);
    CScript scriptPubKey = CScript() <<  ToByteVector(coinbaseKey.GetPubKey()) << OP_CHECKSIG;
    CMutableTransaction newTransaction(*(Params().GenesisBlock().vtx[gen_size-1]));
    for (unsigned int i = 0; i < Params().GenesisBlock().vtx[gen_size-1]->vout.size(); i++)
        newTransaction.vout[i].scriptPubKey = scriptPubKey;
    const_cast<CBlock&>(Params().GenesisBlock()).vtx[gen_size-1] = MakeTransactionRef(newTransaction);
    const_cast<CBlock&>(Params().GenesisBlock()).hashMerkleRoot = BlockMerkleRoot(Params().GenesisBlock());
    const_cast<CBlock&>(Params().GenesisBlock()).proof = CProof(CScript()<<OP_TRUE, CScript());
    const_cast<Consensus::Params&>(Params().GetConsensus()).hashGenesisBlock = Params().GenesisBlock().GetHash();

        ClearDatadirCache();
        pathTemp = GetTempPath() / strprintf("test_bitcoin_%lu_%i", (unsigned long)GetTime(), (int)(GetRand(100000)));
        boost::filesystem::create_directories(pathTemp);
        ForceSetArg("-datadir", pathTemp.string());
        mempool.setSanityCheck(1.0);
        pblocktree = new CBlockTreeDB(1 << 20, true);
        pcoinsdbview = new CCoinsViewDB(1 << 23, true);
        pcoinsTip = new CCoinsViewCache(pcoinsdbview);
        InitBlockIndex(chainparams);
        {
            CValidationState state;
            bool ok = ActivateBestChain(state, chainparams);
            BOOST_CHECK(ok);
        }
        nScriptCheckThreads = 3;
        for (int i=0; i < nScriptCheckThreads-1; i++)
            threadGroup.create_thread(&ThreadScriptCheck);
        g_connman = std::unique_ptr<CConnman>(new CConnman(0x1337, 0x1337)); // Deterministic randomness for tests.
        connman = g_connman.get();
        RegisterNodeSignals(GetNodeSignals());
}

TestingSetup::~TestingSetup()
{
        UnregisterNodeSignals(GetNodeSignals());
        threadGroup.interrupt_all();
        threadGroup.join_all();
        UnloadBlockIndex();
        delete pcoinsTip;
        delete pcoinsdbview;
        delete pblocktree;
        boost::filesystem::remove_all(pathTemp);
}

TestChain100Setup::TestChain100Setup() : TestingSetup(CBaseChainParams::REGTEST)
{
    // Generate a 100-block chain:
    CScript scriptPubKey = CScript() <<  ToByteVector(coinbaseKey.GetPubKey()) << OP_CHECKSIG;
    assert(Params().GenesisBlock().vtx[Params().GenesisBlock().vtx.size()-1]->vout[0].scriptPubKey == scriptPubKey);
    // Get spendable outputs from genesis block, which is non-coinbase for regtest
    coinbaseTxns.push_back(*(Params().GenesisBlock().vtx[Params().GenesisBlock().vtx.size()-1]));
    for (int i = 0; i < COINBASE_MATURITY; i++)
    {
        std::vector<CMutableTransaction> noTxns;
        CBlock b = CreateAndProcessBlock(noTxns, scriptPubKey);
        coinbaseTxns.push_back(*b.vtx[0]);
    }
}

//
// Create a new block with just given transactions, coinbase paying to
// scriptPubKey, and try to add it to the current chain.
//
CBlock
TestChain100Setup::CreateAndProcessBlock(const std::vector<CMutableTransaction>& txns, const CScript& scriptPubKey)
{
    const CChainParams& chainparams = Params();
    std::unique_ptr<CBlockTemplate> pblocktemplate = BlockAssembler(chainparams).CreateNewBlock(scriptPubKey);
    CBlock& block = pblocktemplate->block;

    // Replace mempool-selected txns with just coinbase plus passed-in txns:
    block.vtx.resize(1);
    BOOST_FOREACH(const CMutableTransaction& tx, txns)
        block.vtx.push_back(MakeTransactionRef(tx));
    // IncrementExtraNonce creates a valid coinbase and merkleRoot
    unsigned int extraNonce = 0;
    IncrementExtraNonce(&block, chainActive.Tip(), extraNonce);

    assert(CheckProof(block, chainparams.GetConsensus()));

    std::shared_ptr<const CBlock> shared_pblock = std::make_shared<const CBlock>(block);
    ProcessNewBlock(chainparams, shared_pblock, true, NULL);

    CBlock result = block;
    return result;
}

TestChain100Setup::~TestChain100Setup()
{
}


CAmount TotalValueOut(const CTransaction& tx) {
    CAmount nTotal = 0;
    BOOST_FOREACH(const CTxOut& txo, tx.vout)
        nTotal += txo.nValue.GetAmount();
    return nTotal;
}

CTxMemPoolEntry TestMemPoolEntryHelper::FromTx(const CMutableTransaction &tx, CTxMemPool *pool) {
    CTransaction txn(tx);
    return FromTx(txn, pool);
}

CTxMemPoolEntry TestMemPoolEntryHelper::FromTx(const CTransaction &txn, CTxMemPool *pool) {
    // Hack to assume either it's completely dependent on other mempool txs or not at all
    CAmount inChainValue = pool && pool->HasNoInputsOf(txn) ? TotalValueOut(txn) : 0;

    return CTxMemPoolEntry(MakeTransactionRef(txn), nFee, feeAsset, nTime, dPriority, nHeight,
                           inChainValue, spendsCoinbase, sigOpCost, lp, setPeginsSpent);
}

void Shutdown(void* parg)
{
  exit(0);
}

void StartShutdown()
{
  exit(0);
}

bool ShutdownRequested()
{
  return false;
}
