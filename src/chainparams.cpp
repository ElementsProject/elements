// Copyright (c) 2010 Satoshi Nakamoto
// Copyright (c) 2009-2018 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <chainparams.h>

#include <chainparamsseeds.h>
#include <consensus/merkle.h>
#include <issuance.h>
#include <primitives/transaction.h>
#include <tinyformat.h>
#include <util.h>
#include <utilstrencodings.h>
#include <crypto/sha256.h>
#include <versionbitsinfo.h>

#include <assert.h>

#include <boost/algorithm/string/classification.hpp>
#include <boost/algorithm/string/split.hpp>
static CScript StrHexToScriptWithDefault(std::string strScript, const CScript defaultScript)
{
    CScript returnScript;
    if (!strScript.empty()) {
        std::vector<unsigned char> scriptData = ParseHex(strScript);
        returnScript = CScript(scriptData.begin(), scriptData.end());
    } else {
        returnScript = defaultScript;
    }
    return returnScript;
}

// Safer for users if they load incorrect parameters via arguments.
static std::vector<unsigned char> CommitToArguments(const Consensus::Params& params, const std::string& networkID)
{
    CSHA256 sha2;
    unsigned char commitment[32];
    sha2.Write((const unsigned char*)networkID.c_str(), networkID.length());
    sha2.Write((const unsigned char*)HexStr(params.fedpegScript).c_str(), HexStr(params.fedpegScript).length());
    sha2.Write((const unsigned char*)HexStr(params.signblockscript).c_str(), HexStr(params.signblockscript).length());
    sha2.Finalize(commitment);
    return std::vector<unsigned char>(commitment, commitment + 32);
}

static CBlock CreateGenesisBlock(const Consensus::Params& params, const CScript& genesisScriptSig, const CScript& genesisOutputScript, uint32_t nTime, uint32_t nNonce, uint32_t nBits, int32_t nVersion, const CAmount& genesisReward)
{
    CMutableTransaction txNew;
    txNew.nVersion = 1;
    txNew.vin.resize(1);
    txNew.vout.resize(1);
    txNew.vin[0].scriptSig = genesisScriptSig;
    txNew.vout[0].nValue = CConfidentialValue(genesisReward);
    txNew.vout[0].scriptPubKey = genesisOutputScript;

    CBlock genesis;
    genesis.nTime    = nTime;
    genesis.nBits    = nBits;
    genesis.nNonce   = nNonce;
    genesis.nVersion = nVersion;
    genesis.vtx.push_back(MakeTransactionRef(std::move(txNew)));
    genesis.hashPrevBlock.SetNull();
    genesis.hashMerkleRoot = BlockMerkleRoot(genesis);
    if (g_signed_blocks) {
        genesis.proof = CProof(params.signblockscript, CScript());
    }
    return genesis;
}

/**
 * Build the genesis block. Note that the output of its generation
 * transaction cannot be spent since it did not originally exist in the
 * database.
 *
 * CBlock(hash=000000000019d6, ver=1, hashPrevBlock=00000000000000, hashMerkleRoot=4a5e1e, nTime=1231006505, nBits=1d00ffff, nNonce=2083236893, vtx=1)
 *   CTransaction(hash=4a5e1e, ver=1, vin.size=1, vout.size=1, nLockTime=0)
 *     CTxIn(COutPoint(000000, -1), coinbase 04ffff001d0104455468652054696d65732030332f4a616e2f32303039204368616e63656c6c6f72206f6e206272696e6b206f66207365636f6e64206261696c6f757420666f722062616e6b73)
 *     CTxOut(nValue=50.00000000, scriptPubKey=0x5F1DF16B2B704C8A578D0B)
 *   vMerkleTree: 4a5e1e
 */
static CBlock CreateGenesisBlock(uint32_t nTime, uint32_t nNonce, uint32_t nBits, int32_t nVersion, const CAmount& genesisReward, const Consensus::Params& params)
{
    const char* pszTimestamp = "The Times 03/Jan/2009 Chancellor on brink of second bailout for banks";
    const CScript genesisScriptSig = CScript() << 486604799 << CScriptNum(4) << std::vector<unsigned char>((const unsigned char*)pszTimestamp, (const unsigned char*)pszTimestamp + strlen(pszTimestamp));
    const CScript genesisOutputScript = CScript() << ParseHex("04678afdb0fe5548271967f1a67130b7105cd6a828e03909a67962e0ea1f61deb649f6bc3f4cef38c4f35504e51ec112de5c384df7ba0b8d578a4c702b6bf11d5f") << OP_CHECKSIG;
    return CreateGenesisBlock(params, genesisScriptSig, genesisOutputScript, nTime, nNonce, nBits, nVersion, genesisReward);
}

/**
 * Main network
 */
class CMainParams : public CChainParams {
public:
    CMainParams() {
        strNetworkID = "main";
        consensus.nSubsidyHalvingInterval = 210000;
        consensus.BIP16Exception = uint256S("0x00000000000002dc756eebf4f49723ed8d30cc28a5f108eb94b1ba88ac4f9c22");
        consensus.BIP34Height = 227931;
        consensus.BIP34Hash = uint256S("0x000000000000024b89b42a942fe0d9fea3bb44ab7bd1b19115dd6a759c0808b8");
        consensus.BIP65Height = 388381; // 000000000000000004c2b624ed5d7756c508d90fd0da2c7c679febfa6c4735f0
        consensus.BIP66Height = 363725; // 00000000000000000379eaa19dce8c9b722d46ae6a57c2f1a988119488b50931
        consensus.powLimit = uint256S("00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffff");
        consensus.nPowTargetTimespan = 14 * 24 * 60 * 60; // two weeks
        consensus.nPowTargetSpacing = 10 * 60;
        consensus.fPowAllowMinDifficultyBlocks = false;
        consensus.fPowNoRetargeting = false;
        consensus.nRuleChangeActivationThreshold = 1916; // 95% of 2016
        consensus.nMinerConfirmationWindow = 2016; // nPowTargetTimespan / nPowTargetSpacing
        consensus.vDeployments[Consensus::DEPLOYMENT_TESTDUMMY].bit = 28;
        consensus.vDeployments[Consensus::DEPLOYMENT_TESTDUMMY].nStartTime = 1199145601; // January 1, 2008
        consensus.vDeployments[Consensus::DEPLOYMENT_TESTDUMMY].nTimeout = 1230767999; // December 31, 2008

        // Deployment of BIP68, BIP112, and BIP113.
        consensus.vDeployments[Consensus::DEPLOYMENT_CSV].bit = 0;
        consensus.vDeployments[Consensus::DEPLOYMENT_CSV].nStartTime = 1462060800; // May 1st, 2016
        consensus.vDeployments[Consensus::DEPLOYMENT_CSV].nTimeout = 1493596800; // May 1st, 2017

        // Deployment of SegWit (BIP141, BIP143, and BIP147)
        consensus.vDeployments[Consensus::DEPLOYMENT_SEGWIT].bit = 1;
        consensus.vDeployments[Consensus::DEPLOYMENT_SEGWIT].nStartTime = 1479168000; // November 15th, 2016.
        consensus.vDeployments[Consensus::DEPLOYMENT_SEGWIT].nTimeout = 1510704000; // November 15th, 2017.

        // The best chain should have at least this much work.
        consensus.nMinimumChainWork = uint256S("0x0000000000000000000000000000000000000000028822fef1c230963535a90d");

        // By default assume that the signatures in ancestors of this block are valid.
        consensus.defaultAssumeValid = uint256S("0x0000000000000000002e63058c023a9a1de233554f28c7b21380b6c9003f36a8"); //534292

        consensus.genesis_subsidy = 50*COIN;
        consensus.connect_genesis_outputs = false;
        consensus.subsidy_asset = CAsset();
        anyonecanspend_aremine = false;
        enforce_pak = false;
        multi_data_permitted = false;
        consensus.has_parent_chain = false;
        g_signed_blocks = false;
        g_con_elementswitness = false;
        g_con_blockheightinheader = false;

        /**
         * The message start string is designed to be unlikely to occur in normal data.
         * The characters are rarely used upper ASCII, not valid as UTF-8, and produce
         * a large 32-bit integer with any alignment.
         */
        pchMessageStart[0] = 0xf9;
        pchMessageStart[1] = 0xbe;
        pchMessageStart[2] = 0xb4;
        pchMessageStart[3] = 0xd9;
        nDefaultPort = 8333;
        nPruneAfterHeight = 100000;

        genesis = CreateGenesisBlock(1231006505, 2083236893, 0x1d00ffff, 1, 50 * COIN, consensus);
        consensus.hashGenesisBlock = genesis.GetHash();
        assert(consensus.hashGenesisBlock == uint256S("0x000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f"));
        assert(genesis.hashMerkleRoot == uint256S("0x4a5e1e4baab89f3a32518a88c31bc87f618f76673e2cc77ab2127b7afdeda33b"));

        // Note that of those which support the service bits prefix, most only support a subset of
        // possible options.
        // This is fine at runtime as we'll fall back to using them as a oneshot if they don't support the
        // service bits we want, but we should get them updated to support all service bits wanted by any
        // release ASAP to avoid it where possible.
        vSeeds.emplace_back("seed.bitcoin.sipa.be"); // Pieter Wuille, only supports x1, x5, x9, and xd
        vSeeds.emplace_back("dnsseed.bluematt.me"); // Matt Corallo, only supports x9
        vSeeds.emplace_back("dnsseed.bitcoin.dashjr.org"); // Luke Dashjr
        vSeeds.emplace_back("seed.bitcoinstats.com"); // Christian Decker, supports x1 - xf
        vSeeds.emplace_back("seed.bitcoin.jonasschnelli.ch"); // Jonas Schnelli, only supports x1, x5, x9, and xd
        vSeeds.emplace_back("seed.btc.petertodd.org"); // Peter Todd, only supports x1, x5, x9, and xd
        vSeeds.emplace_back("seed.bitcoin.sprovoost.nl"); // Sjors Provoost

        base58Prefixes[PUBKEY_ADDRESS] = std::vector<unsigned char>(1,0);
        base58Prefixes[SCRIPT_ADDRESS] = std::vector<unsigned char>(1,5);
        base58Prefixes[SECRET_KEY] =     std::vector<unsigned char>(1,128);
        base58Prefixes[EXT_PUBLIC_KEY] = {0x04, 0x88, 0xB2, 0x1E};
        base58Prefixes[EXT_SECRET_KEY] = {0x04, 0x88, 0xAD, 0xE4};

        bech32_hrp = "bc";

        vFixedSeeds = std::vector<SeedSpec6>(pnSeed6_main, pnSeed6_main + ARRAYLEN(pnSeed6_main));

        fDefaultConsistencyChecks = false;
        fRequireStandard = true;
        fMineBlocksOnDemand = false;

        checkpointData = {
            {
                { 11111, uint256S("0x0000000069e244f73d78e8fd29ba2fd2ed618bd6fa2ee92559f542fdb26e7c1d")},
                { 33333, uint256S("0x000000002dd5588a74784eaa7ab0507a18ad16a236e7b1ce69f00d7ddfb5d0a6")},
                { 74000, uint256S("0x0000000000573993a3c9e41ce34471c079dcf5f52a0e824a81e7f953b8661a20")},
                {105000, uint256S("0x00000000000291ce28027faea320c8d2b054b2e0fe44a773f3eefb151d6bdc97")},
                {134444, uint256S("0x00000000000005b12ffd4cd315cd34ffd4a594f430ac814c91184a0d42d2b0fe")},
                {168000, uint256S("0x000000000000099e61ea72015e79632f216fe6cb33d7899acb35b75c8303b763")},
                {193000, uint256S("0x000000000000059f452a5f7340de6682a977387c17010ff6e6c3bd83ca8b1317")},
                {210000, uint256S("0x000000000000048b95347e83192f69cf0366076336c639f9b7228e9ba171342e")},
                {216116, uint256S("0x00000000000001b4f4b433e81ee46494af945cf96014816a4e2370f11b23df4e")},
                {225430, uint256S("0x00000000000001c108384350f74090433e7fcf79a606b8e797f065b130575932")},
                {250000, uint256S("0x000000000000003887df1f29024b06fc2200b55f8af8f35453d7be294df2d214")},
                {279000, uint256S("0x0000000000000001ae8c72a0b0c301f67e3afca10e819efa9041e458e9bd7e40")},
                {295000, uint256S("0x00000000000000004d9b4ef50f0f9d686fd69db2e03af35a100370c64632a983")},
            }
        };

        chainTxData = ChainTxData{
            // Data from rpc: getchaintxstats 4096 0000000000000000002e63058c023a9a1de233554f28c7b21380b6c9003f36a8
            /* nTime    */ 1532884444,
            /* nTxCount */ 331282217,
            /* dTxRate  */ 2.4
        };

        /* disable fallback fee on mainnet */
        m_fallback_fee_enabled = false;
    }
};

/**
 * Testnet (v3)
 */
class CTestNetParams : public CChainParams {
public:
    CTestNetParams() {
        strNetworkID = "test";
        consensus.nSubsidyHalvingInterval = 210000;
        consensus.BIP16Exception = uint256S("0x00000000dd30457c001f4095d208cc1296b0eed002427aa599874af7a432b105");
        consensus.BIP34Height = 21111;
        consensus.BIP34Hash = uint256S("0x0000000023b3a96d3484e5abb3755c413e7d41500f8e2a5c3f0dd01299cd8ef8");
        consensus.BIP65Height = 581885; // 00000000007f6655f22f98e72ed80d8b06dc761d5da09df0fa1dc4be4f861eb6
        consensus.BIP66Height = 330776; // 000000002104c8c45e99a8853285a3b592602a3ccde2b832481da85e9e4ba182
        consensus.powLimit = uint256S("00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffff");
        consensus.nPowTargetTimespan = 14 * 24 * 60 * 60; // two weeks
        consensus.nPowTargetSpacing = 10 * 60;
        consensus.fPowAllowMinDifficultyBlocks = true;
        consensus.fPowNoRetargeting = false;
        consensus.nRuleChangeActivationThreshold = 1512; // 75% for testchains
        consensus.nMinerConfirmationWindow = 2016; // nPowTargetTimespan / nPowTargetSpacing
        consensus.vDeployments[Consensus::DEPLOYMENT_TESTDUMMY].bit = 28;
        consensus.vDeployments[Consensus::DEPLOYMENT_TESTDUMMY].nStartTime = 1199145601; // January 1, 2008
        consensus.vDeployments[Consensus::DEPLOYMENT_TESTDUMMY].nTimeout = 1230767999; // December 31, 2008

        // Deployment of BIP68, BIP112, and BIP113.
        consensus.vDeployments[Consensus::DEPLOYMENT_CSV].bit = 0;
        consensus.vDeployments[Consensus::DEPLOYMENT_CSV].nStartTime = 1456790400; // March 1st, 2016
        consensus.vDeployments[Consensus::DEPLOYMENT_CSV].nTimeout = 1493596800; // May 1st, 2017

        // Deployment of SegWit (BIP141, BIP143, and BIP147)
        consensus.vDeployments[Consensus::DEPLOYMENT_SEGWIT].bit = 1;
        consensus.vDeployments[Consensus::DEPLOYMENT_SEGWIT].nStartTime = 1462060800; // May 1st 2016
        consensus.vDeployments[Consensus::DEPLOYMENT_SEGWIT].nTimeout = 1493596800; // May 1st 2017

        // The best chain should have at least this much work.
        consensus.nMinimumChainWork = uint256S("0x00000000000000000000000000000000000000000000007dbe94253893cbd463");

        // By default assume that the signatures in ancestors of this block are valid.
        consensus.defaultAssumeValid = uint256S("0x0000000000000037a8cd3e06cd5edbfe9dd1dbcc5dacab279376ef7cfc2b4c75"); //1354312

        consensus.genesis_subsidy = 50*COIN;
        consensus.connect_genesis_outputs = false;
        consensus.subsidy_asset = CAsset();
        anyonecanspend_aremine = false;
        enforce_pak = false;
        multi_data_permitted = false;
        consensus.has_parent_chain = false;
        g_signed_blocks = false;
        g_con_elementswitness = false;
        g_con_blockheightinheader = false;

        pchMessageStart[0] = 0x0b;
        pchMessageStart[1] = 0x11;
        pchMessageStart[2] = 0x09;
        pchMessageStart[3] = 0x07;
        nDefaultPort = 18333;
        nPruneAfterHeight = 1000;

        genesis = CreateGenesisBlock(1296688602, 414098458, 0x1d00ffff, 1, 50 * COIN, consensus);
        consensus.hashGenesisBlock = genesis.GetHash();
        assert(consensus.hashGenesisBlock == uint256S("0x000000000933ea01ad0ee984209779baaec3ced90fa3f408719526f8d77f4943"));
        assert(genesis.hashMerkleRoot == uint256S("0x4a5e1e4baab89f3a32518a88c31bc87f618f76673e2cc77ab2127b7afdeda33b"));

        vFixedSeeds.clear();
        vSeeds.clear();
        // nodes with support for servicebits filtering should be at the top
        vSeeds.emplace_back("testnet-seed.bitcoin.jonasschnelli.ch");
        vSeeds.emplace_back("seed.tbtc.petertodd.org");
        vSeeds.emplace_back("seed.testnet.bitcoin.sprovoost.nl");
        vSeeds.emplace_back("testnet-seed.bluematt.me"); // Just a static list of stable node(s), only supports x9

        base58Prefixes[PUBKEY_ADDRESS] = std::vector<unsigned char>(1,111);
        base58Prefixes[SCRIPT_ADDRESS] = std::vector<unsigned char>(1,196);
        base58Prefixes[SECRET_KEY] =     std::vector<unsigned char>(1,239);
        base58Prefixes[EXT_PUBLIC_KEY] = {0x04, 0x35, 0x87, 0xCF};
        base58Prefixes[EXT_SECRET_KEY] = {0x04, 0x35, 0x83, 0x94};

        bech32_hrp = "tb";

        vFixedSeeds = std::vector<SeedSpec6>(pnSeed6_test, pnSeed6_test + ARRAYLEN(pnSeed6_test));

        fDefaultConsistencyChecks = false;
        fRequireStandard = false;
        fMineBlocksOnDemand = false;


        checkpointData = {
            {
                {546, uint256S("000000002a936ca763904c3c35fce2f3556c559c0214345d31b1bcebf76acb70")},
            }
        };

        chainTxData = ChainTxData{
            // Data from rpc: getchaintxstats 4096 0000000000000037a8cd3e06cd5edbfe9dd1dbcc5dacab279376ef7cfc2b4c75
            /* nTime    */ 1531929919,
            /* nTxCount */ 19438708,
            /* dTxRate  */ 0.626
        };

        /* enable fallback fee on testnet */
        m_fallback_fee_enabled = true;
    }
};

/**
 * Regression test
 */
class CRegTestParams : public CChainParams {
public:
    explicit CRegTestParams(const ArgsManager& args) {
        strNetworkID = "regtest";
        consensus.nSubsidyHalvingInterval = 150;
        consensus.BIP16Exception = uint256();
        consensus.BIP34Height = 100000000; // BIP34 has not activated on regtest (far in the future so block v1 are not rejected in tests)
        consensus.BIP34Hash = uint256();
        consensus.BIP65Height = 1351; // BIP65 activated on regtest (Used in rpc activation tests)
        consensus.BIP66Height = 1251; // BIP66 activated on regtest (Used in rpc activation tests)
        consensus.powLimit = uint256S("7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff");
        consensus.nPowTargetTimespan = 14 * 24 * 60 * 60; // two weeks
        consensus.nPowTargetSpacing = 10 * 60;
        consensus.fPowAllowMinDifficultyBlocks = true;
        consensus.fPowNoRetargeting = true;
        consensus.nRuleChangeActivationThreshold = 108; // 75% for testchains
        consensus.nMinerConfirmationWindow = 144; // Faster than normal for regtest (144 instead of 2016)
        consensus.vDeployments[Consensus::DEPLOYMENT_TESTDUMMY].bit = 28;
        consensus.vDeployments[Consensus::DEPLOYMENT_TESTDUMMY].nStartTime = 0;
        consensus.vDeployments[Consensus::DEPLOYMENT_TESTDUMMY].nTimeout = Consensus::BIP9Deployment::NO_TIMEOUT;
        consensus.vDeployments[Consensus::DEPLOYMENT_CSV].bit = 0;
        consensus.vDeployments[Consensus::DEPLOYMENT_CSV].nStartTime = 0;
        consensus.vDeployments[Consensus::DEPLOYMENT_CSV].nTimeout = Consensus::BIP9Deployment::NO_TIMEOUT;
        consensus.vDeployments[Consensus::DEPLOYMENT_SEGWIT].bit = 1;
        consensus.vDeployments[Consensus::DEPLOYMENT_SEGWIT].nStartTime = Consensus::BIP9Deployment::ALWAYS_ACTIVE;
        consensus.vDeployments[Consensus::DEPLOYMENT_SEGWIT].nTimeout = Consensus::BIP9Deployment::NO_TIMEOUT;

        // The best chain should have at least this much work.
        consensus.nMinimumChainWork = uint256S("0x00");

        // By default assume that the signatures in ancestors of this block are valid.
        consensus.defaultAssumeValid = uint256S("0x00");

        consensus.genesis_subsidy = 50*COIN;
        consensus.connect_genesis_outputs = false;
        consensus.subsidy_asset = CAsset();
        anyonecanspend_aremine = false;
        enforce_pak = false;
        multi_data_permitted = false;
        consensus.has_parent_chain = false;
        g_signed_blocks = false;
        g_con_elementswitness = false;
        g_con_blockheightinheader = false;

        pchMessageStart[0] = 0xfa;
        pchMessageStart[1] = 0xbf;
        pchMessageStart[2] = 0xb5;
        pchMessageStart[3] = 0xda;
        nDefaultPort = 18444;
        nPruneAfterHeight = 1000;

        UpdateVersionBitsParametersFromArgs(args);

        genesis = CreateGenesisBlock(1296688602, 2, 0x207fffff, 1, 50 * COIN, consensus);
        consensus.hashGenesisBlock = genesis.GetHash();
        assert(consensus.hashGenesisBlock == uint256S("0x0f9188f13cb7b2c71f2a335e3a4fc328bf5beb436012afca590b1a11466e2206"));
        assert(genesis.hashMerkleRoot == uint256S("0x4a5e1e4baab89f3a32518a88c31bc87f618f76673e2cc77ab2127b7afdeda33b"));

        vFixedSeeds.clear(); //!< Regtest mode doesn't have any fixed seeds.
        vSeeds.clear();      //!< Regtest mode doesn't have any DNS seeds.

        fDefaultConsistencyChecks = true;
        fRequireStandard = false;
        fMineBlocksOnDemand = true;

        checkpointData = {
            {
                {0, uint256S("0f9188f13cb7b2c71f2a335e3a4fc328bf5beb436012afca590b1a11466e2206")},
            }
        };

        chainTxData = ChainTxData{
            0,
            0,
            0
        };

        base58Prefixes[PUBKEY_ADDRESS] = std::vector<unsigned char>(1,111);
        base58Prefixes[SCRIPT_ADDRESS] = std::vector<unsigned char>(1,196);
        base58Prefixes[SECRET_KEY] =     std::vector<unsigned char>(1,239);
        base58Prefixes[EXT_PUBLIC_KEY] = {0x04, 0x35, 0x87, 0xCF};
        base58Prefixes[EXT_SECRET_KEY] = {0x04, 0x35, 0x83, 0x94};

        bech32_hrp = "bcrt";

        /* enable fallback fee on regtest */
        m_fallback_fee_enabled = true;
    }

    /**
     * Allows modifying the Version Bits regtest parameters.
     */
    void UpdateVersionBitsParameters(Consensus::DeploymentPos d, int64_t nStartTime, int64_t nTimeout)
    {
        consensus.vDeployments[d].nStartTime = nStartTime;
        consensus.vDeployments[d].nTimeout = nTimeout;
    }
    void UpdateVersionBitsParametersFromArgs(const ArgsManager& args);
};

void CRegTestParams::UpdateVersionBitsParametersFromArgs(const ArgsManager& args)
{
    if (!args.IsArgSet("-vbparams")) return;

    for (const std::string& strDeployment : args.GetArgs("-vbparams")) {
        std::vector<std::string> vDeploymentParams;
        boost::split(vDeploymentParams, strDeployment, boost::is_any_of(":"));
        if (vDeploymentParams.size() != 3) {
            throw std::runtime_error("Version bits parameters malformed, expecting deployment:start:end");
        }
        int64_t nStartTime, nTimeout;
        if (!ParseInt64(vDeploymentParams[1], &nStartTime)) {
            throw std::runtime_error(strprintf("Invalid nStartTime (%s)", vDeploymentParams[1]));
        }
        if (!ParseInt64(vDeploymentParams[2], &nTimeout)) {
            throw std::runtime_error(strprintf("Invalid nTimeout (%s)", vDeploymentParams[2]));
        }
        bool found = false;
        for (int j=0; j < (int)Consensus::MAX_VERSION_BITS_DEPLOYMENTS; ++j) {
            if (vDeploymentParams[0] == VersionBitsDeploymentInfo[j].name) {
                UpdateVersionBitsParameters(Consensus::DeploymentPos(j), nStartTime, nTimeout);
                found = true;
                LogPrintf("Setting version bits activation parameters for %s to start=%ld, timeout=%ld\n", vDeploymentParams[0], nStartTime, nTimeout);
                break;
            }
        }
        if (!found) {
            throw std::runtime_error(strprintf("Invalid deployment (%s)", vDeploymentParams[0]));
        }
    }
}

/**
 * Custom params for testing.
 */
class CCustomParams : public CRegTestParams {
    void UpdateFromArgs(ArgsManager& args)
    {
        UpdateVersionBitsParametersFromArgs(args);

        consensus.nSubsidyHalvingInterval = args.GetArg("-con_nsubsidyhalvinginterval", consensus.nSubsidyHalvingInterval);
        consensus.BIP16Exception = uint256S(args.GetArg("-con_bip16exception", "0x0"));
        consensus.BIP34Height = args.GetArg("-con_bip34height", 0);
        consensus.BIP34Hash = uint256S(args.GetArg("-con_bip34hash", "0x0"));
        consensus.BIP65Height = args.GetArg("-con_bip65height", 0);
        consensus.BIP66Height = args.GetArg("-con_bip66height", 0);
        consensus.powLimit = uint256S(args.GetArg("-con_powlimit", "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"));
        consensus.nPowTargetTimespan = args.GetArg("-con_npowtargettimespan", consensus.nPowTargetTimespan);
        consensus.nPowTargetSpacing = args.GetArg("-con_npowtargetspacing", consensus.nPowTargetSpacing);
        consensus.fPowAllowMinDifficultyBlocks = args.GetBoolArg("-con_fpowallowmindifficultyblocks", consensus.fPowAllowMinDifficultyBlocks);
        consensus.fPowNoRetargeting = args.GetBoolArg("-con_fpownoretargeting", consensus.fPowNoRetargeting);
        consensus.nRuleChangeActivationThreshold = (uint32_t)args.GetArg("-con_nrulechangeactivationthreshold", consensus.nRuleChangeActivationThreshold);
        consensus.nMinerConfirmationWindow = (uint32_t)args.GetArg("-con_nminerconfirmationwindow", consensus.nMinerConfirmationWindow);

        consensus.nMinimumChainWork = uint256S(args.GetArg("-con_nminimumchainwork", "0x0"));
        consensus.defaultAssumeValid = uint256S(args.GetArg("-con_defaultassumevalid", "0x00"));

        nPruneAfterHeight = (uint64_t)args.GetArg("-npruneafterheight", nPruneAfterHeight);
        fDefaultConsistencyChecks = args.GetBoolArg("-fdefaultconsistencychecks", fDefaultConsistencyChecks);
        fMineBlocksOnDemand = args.GetBoolArg("-fmineblocksondemand", fMineBlocksOnDemand);
        m_fallback_fee_enabled = args.GetBoolArg("-fallback_fee_enabled", m_fallback_fee_enabled);

        bech32_hrp = args.GetArg("-bech32_hrp", bech32_hrp);
        base58Prefixes[PUBKEY_ADDRESS] = std::vector<unsigned char>(1, args.GetArg("-pubkeyprefix", 111));
        base58Prefixes[SCRIPT_ADDRESS] = std::vector<unsigned char>(1, args.GetArg("-scriptprefix", 196));
        base58Prefixes[SECRET_KEY] =     std::vector<unsigned char>(1, args.GetArg("-secretprefix", 239));

        std::string extpubprefix = args.GetArg("-extpubkeyprefix", "043587CF");
        assert(IsHex(extpubprefix) && extpubprefix.size() == 8 && "-extpubkeyprefix must be hex string of length 8");
        base58Prefixes[EXT_PUBLIC_KEY] = ParseHex(extpubprefix);

        std::string extprvprefix = args.GetArg("-extprvkeyprefix", "04358394");
        assert(IsHex(extprvprefix) && extprvprefix.size() == 8 && "-extprvkeyprefix must be hex string of length 8");
        base58Prefixes[EXT_SECRET_KEY] = ParseHex(extprvprefix);

        const std::string magic_str = args.GetArg("-pchmessagestart", "FABFB5DA");
        assert(IsHex(magic_str) && magic_str.size() == 8 && "-pchmessagestart must be hex string of length 8");
        const std::vector<unsigned char> magic_byte = ParseHex(magic_str);
        std::copy(begin(magic_byte), end(magic_byte), pchMessageStart);

        vSeeds.clear();
        if (args.IsArgSet("-seednode")) {
            const auto seednodes = args.GetArgs("-seednode");
            if (seednodes.size() != 1 || seednodes[0] != "0") {
                vSeeds = seednodes;
            }
        }

        //
        // ELEMENTS fields

        // Determines type of genesis block
        consensus.genesis_style = gArgs.GetArg("-con_genesis_style", "elements");

        // Block signing encumberance script, default of 51 aka OP_TRUE
        std::vector<unsigned char> sign_bytes = ParseHex(gArgs.GetArg("-signblockscript", "51"));
        consensus.signblockscript = CScript(sign_bytes.begin(), sign_bytes.end());
        // Default signature size is the size of dummy push, and single 72 byte DER signature
        consensus.max_block_signature_size = gArgs.GetArg("-con_max_block_sig_size", 74);
        g_signed_blocks = gArgs.GetBoolArg("-con_signed_blocks", true);

        // Note: These globals are needed to avoid circular dependencies.
        // Default to true for custom chains.
        g_con_blockheightinheader = args.GetBoolArg("-con_blockheightinheader", true);
        g_con_elementswitness = args.GetBoolArg("-con_elementswitness", true);

        // No subsidy for custom chains by default
        consensus.genesis_subsidy = args.GetArg("-con_blocksubsidy", 0);

        // All non-zero coinbase outputs must go to this scriptPubKey
        std::vector<unsigned char> man_bytes = ParseHex(args.GetArg("-con_mandatorycoinbase", ""));
        consensus.mandatory_coinbase_destination = CScript(man_bytes.begin(), man_bytes.end()); // Blank script allows any coinbase destination

        // Custom chains connect coinbase outputs to db by default
        consensus.connect_genesis_outputs = args.GetArg("-con_connect_coinbase", true);

        initialFreeCoins = gArgs.GetArg("-initialfreecoins", 0);

        anyonecanspend_aremine = args.GetBoolArg("-anyonecanspendaremine", true);

        consensus.has_parent_chain = args.GetBoolArg("-con_has_parent_chain", true);

        enforce_pak = args.GetBoolArg("-enforce_pak", false);

        // Allow multiple op_return outputs by relay policy
        multi_data_permitted = args.GetBoolArg("-multi_data_permitted", true);

        // bitcoin regtest is the parent chain by default
        parentGenesisBlockHash = uint256S(args.GetArg("-parentgenesisblockhash", "0f9188f13cb7b2c71f2a335e3a4fc328bf5beb436012afca590b1a11466e2206"));
        // Either it has a parent chain or not
        const bool parent_genesis_is_null = parentGenesisBlockHash == uint256();
        assert(consensus.has_parent_chain != parent_genesis_is_null);
        consensus.parentChainPowLimit = uint256S(args.GetArg("-con_parentpowlimit", "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"));
        consensus.parent_chain_signblockscript = StrHexToScriptWithDefault(args.GetArg("-con_parent_chain_signblockscript", ""), CScript());
        consensus.pegin_min_depth = args.GetArg("-peginconfirmationdepth", DEFAULT_PEGIN_CONFIRMATION_DEPTH);

        const CScript default_script(CScript() << OP_TRUE);
        consensus.fedpegScript = StrHexToScriptWithDefault(args.GetArg("-fedpegscript", ""), default_script);

        base58Prefixes[PARENT_PUBKEY_ADDRESS] = std::vector<unsigned char>(1, args.GetArg("-parentpubkeyprefix", 111));
        base58Prefixes[PARENT_SCRIPT_ADDRESS] = std::vector<unsigned char>(1, args.GetArg("-parentscriptprefix", 196));
        parent_bech32_hrp = args.GetArg("-parent_bech32_hrp", "bcrt");

        // Calculate pegged Bitcoin asset
        std::vector<unsigned char> commit = CommitToArguments(consensus, strNetworkID);
        uint256 entropy;
        GenerateAssetEntropy(entropy,  COutPoint(uint256(commit), 0), parentGenesisBlockHash);

        // Elements serialization uses derivation, bitcoin serialization uses 0x00
        if (g_con_elementswitness) {
            CalculateAsset(consensus.pegged_asset, entropy);
        } else {
            assert(consensus.pegged_asset == CAsset());
        }

        consensus.parent_pegged_asset.SetHex(args.GetArg("-con_parent_pegged_asset", "0x00"));
        initial_reissuance_tokens = args.GetArg("-initialreissuancetokens", 0);

        // Subsidy asset, like policyAsset, defaults to the pegged_asset
        consensus.subsidy_asset = consensus.pegged_asset;
        if (gArgs.IsArgSet("-subsidyasset")) {
            consensus.subsidy_asset = CAsset(uint256S(gArgs.GetArg("-subsidyasset", "0x00")));
        }

        // END ELEMENTS fields

        // CSV always active by default, unlike regtest
        consensus.vDeployments[Consensus::DEPLOYMENT_CSV].bit = 0;
        consensus.vDeployments[Consensus::DEPLOYMENT_CSV].nStartTime = args.GetArg("-con_csv_deploy_start", Consensus::BIP9Deployment::ALWAYS_ACTIVE);
        consensus.vDeployments[Consensus::DEPLOYMENT_CSV].nTimeout = Consensus::BIP9Deployment::NO_TIMEOUT;

    }

    void SetGenesisBlock() {
        if (consensus.genesis_style == "bitcoin") {
            // For compatibility with bitcoin (regtest)
            genesis = CreateGenesisBlock(1296688602, 2, 0x207fffff, 1, 50 * COIN, consensus);
        } else if (consensus.genesis_style == "elements") {
            // Intended compatibility with Liquid v1 and elements-0.14.1
            std::vector<unsigned char> commit = CommitToArguments(consensus, strNetworkID);
            genesis = CreateGenesisBlock(consensus, CScript(commit), CScript(OP_RETURN), 1296688602, 2, 0x207fffff, 1, 0);
            if (initialFreeCoins != 0 || initial_reissuance_tokens != 0) {
                AppendInitialIssuance(genesis, COutPoint(uint256(commit), 0), parentGenesisBlockHash, (initialFreeCoins > 0) ? 1 : 0, initialFreeCoins, (initial_reissuance_tokens > 0) ? 1 : 0, initial_reissuance_tokens, CScript() << OP_TRUE);
            }
        } else {
            throw std::runtime_error(strprintf("Invalid -genesis_style (%s)", consensus.genesis_style));
        }
    }

public:
    CCustomParams(const std::string& chain, ArgsManager& args) : CRegTestParams(args)
    {
        strNetworkID = chain;
        UpdateFromArgs(args);
        SetGenesisBlock();
        consensus.hashGenesisBlock = genesis.GetHash();
    }
};

static std::unique_ptr<const CChainParams> globalChainParams;

const CChainParams &Params() {
    assert(globalChainParams);
    return *globalChainParams;
}

std::unique_ptr<const CChainParams> CreateChainParams(const std::string& chain)
{
    // Reserved names for non-custom chains
    if (chain == CBaseChainParams::MAIN)
        return std::unique_ptr<CChainParams>(new CMainParams());
    else if (chain == CBaseChainParams::TESTNET)
        return std::unique_ptr<CChainParams>(new CTestNetParams());
    else if (chain == CBaseChainParams::REGTEST)
        return std::unique_ptr<CChainParams>(new CRegTestParams(gArgs));

    return std::unique_ptr<CChainParams>(new CCustomParams(chain, gArgs));
}

void SelectParams(const std::string& network)
{
    SelectBaseParams(network);
    globalChainParams = CreateChainParams(network);
}
