// Copyright (c) 2010 Satoshi Nakamoto
// Copyright (c) 2009-2016 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "chainparams.h"
#include "consensus/merkle.h"
#include "issuance.h"

#include "tinyformat.h"
#include "util.h"
#include "utilstrencodings.h"
#include "amount.h"
#include "crypto/sha256.h"

#include <assert.h>

#include <boost/assign/list_of.hpp>

// Safer for users if they load incorrect parameters via arguments.
static std::vector<unsigned char> CommitToArguments(const Consensus::Params& params, const std::string& networkID, const CScript& signblockscript)
{
    CSHA256 sha2;
    unsigned char commitment[32];
    sha2.Write((const unsigned char*)networkID.c_str(), networkID.length());
    sha2.Write((const unsigned char*)HexStr(params.fedpegScript).c_str(), HexStr(params.fedpegScript).length());
    sha2.Write((const unsigned char*)HexStr(signblockscript).c_str(), HexStr(signblockscript).length());
    sha2.Finalize(commitment);
    return std::vector<unsigned char>(commitment, commitment + 32);
}

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

static CBlock CreateGenesisBlock(const Consensus::Params& params, const std::string& networkID, const CScript& genesisOutputScript, uint32_t nTime, const CScript& scriptChallenge, int32_t nVersion, const CAmount& genesisReward, const uint32_t rewardShards, const CAsset& asset)
{
    // Shards must be evenly divisible
    assert(MAX_MONEY % rewardShards == 0);
    CMutableTransaction txNew;
    txNew.nVersion = 1;
    txNew.vin.resize(1);
    txNew.vout.resize(rewardShards);
    // Any consensus-related values that are command-line set can be added here for anti-footgun
    txNew.vin[0].scriptSig = CScript(CommitToArguments(params, networkID, scriptChallenge));
    for (unsigned int i = 0; i < rewardShards; i++) {
        txNew.vout[i].nValue = genesisReward/rewardShards;
        txNew.vout[i].nAsset = asset;
        txNew.vout[i].scriptPubKey = genesisOutputScript;
    }

    CBlock genesis;
    genesis.nTime    = nTime;
    genesis.proof = CProof(scriptChallenge, CScript());
    genesis.nVersion = nVersion;
    genesis.vtx.push_back(MakeTransactionRef(std::move(txNew)));
    genesis.hashPrevBlock.SetNull();
    genesis.hashMerkleRoot = BlockMerkleRoot(genesis);
    return genesis;
}

void CChainParams::UpdateBIP9Parameters(Consensus::DeploymentPos d, int64_t nStartTime, int64_t nTimeout)
{
    consensus.vDeployments[d].nStartTime = nStartTime;
    consensus.vDeployments[d].nTimeout = nTimeout;
}

/**
 * Elements Core.

 */
class CElementsParams : public CChainParams {
public:
    CElementsParams() {
        CScript defaultSignblockScript;
        // Default blocksign script for elements
        defaultSignblockScript = CScript() << OP_2 << ParseHex("03206b45265ae687dfdc602b8faa7dd749d7865b0e51f986e12c532229f0c998be") << ParseHex("02cc276552e180061f64dc16e2a02e7f9ecbcc744dea84eddbe991721824df825c") << ParseHex("0204c6be425356d9200a3303d95f2c39078cc9473ca49619da1e0ec233f27516ca") << OP_3 << OP_CHECKMULTISIG;
        CScript genesisChallengeScript = StrHexToScriptWithDefault(GetArg("-signblockscript", ""), defaultSignblockScript);
        CScript defaultFedpegScript;
        defaultFedpegScript = CScript() << OP_2 << ParseHex("02d51090b27ca8f1cc04984614bd749d8bab6f2a3681318d3fd0dd43b2a39dd774") << ParseHex("03a75bd7ac458b19f98047c76a6ffa442e592148c5d23a1ec82d379d5d558f4fd8") << ParseHex("034c55bede1bce8e486080f8ebb7a0e8f106b49efb295a8314da0e1b1723738c66") << OP_3 << OP_CHECKMULTISIG;
        consensus.fedpegScript = StrHexToScriptWithDefault(GetArg("-fedpegscript", ""), defaultFedpegScript);

        strNetworkID = CHAINPARAMS_ELEMENTS;
        consensus.nSubsidyHalvingInterval = 210000;
        consensus.BIP34Height = 227931;
        consensus.BIP34Hash = uint256S("0x000000000000024b89b42a942fe0d9fea3bb44ab7bd1b19115dd6a759c0808b8");
        consensus.BIP65Height = 388381; // 000000000000000004c2b624ed5d7756c508d90fd0da2c7c679febfa6c4735f0
        consensus.BIP66Height = 363725; // 00000000000000000379eaa19dce8c9b722d46ae6a57c2f1a988119488b50931
        consensus.powLimit = uint256S("00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffff");

        // Peg-ins Bitcoin headers must have higher difficulty target than this field
        // This value must be sufficiently small to not preclude realistic parent
        // chain difficulty during network lifespan yet sufficiently large to
        // deny peg-in DoS attacks due to our inability to ban after failed
        // IsBitcoinBlock RPC checks.
        consensus.parentChainPowLimit = uint256S("00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffff");
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
        consensus.nMinimumChainWork = uint256S("0x0000000000000000000000000000000000000000003f94d1ad391682fe038bf5");

        // By default assume that the signatures in ancestors of this block are valid.
        consensus.defaultAssumeValid = uint256S("0x00000000000000000013176bf8d7dfeab4e1db31dc93bc311b436e82ab226b90"); //453354

        /**
         * The message start string is designed to be unlikely to occur in normal data.
         * The characters are rarely used upper ASCII, not valid as UTF-8, and produce
         * a large 32-bit integer with any alignment.
         */
        pchMessageStart[0] = 0xef;
        pchMessageStart[1] = 0xb1;
        pchMessageStart[2] = 0x1f;
        pchMessageStart[3] = 0xea;
        nDefaultPort = 9042;
        nPruneAfterHeight = 100000;

        parentGenesisBlockHash = uint256S("000000000933ea01ad0ee984209779baaec3ced90fa3f408719526f8d77f4943");

        // Generate pegged Bitcoin asset
        std::vector<unsigned char> commit = CommitToArguments(consensus, strNetworkID, genesisChallengeScript);
        uint256 entropy;
        GenerateAssetEntropy(entropy, COutPoint(uint256(commit), 0), parentGenesisBlockHash);
        CalculateAsset(consensus.pegged_asset, entropy);

        CScript scriptDestination(CScript() << std::vector<unsigned char>(parentGenesisBlockHash.begin(), parentGenesisBlockHash.end()) << OP_WITHDRAWPROOFVERIFY);
        genesis = CreateGenesisBlock(consensus, strNetworkID, scriptDestination, 1231006505, genesisChallengeScript, 1, MAX_MONEY, 100, consensus.pegged_asset);
        consensus.hashGenesisBlock = genesis.GetHash();

        scriptCoinbaseDestination = CScript() << ParseHex("0229536c4c83789f59c30b93eb40d4abbd99b8dcc99ba8bd748f29e33c1d279e3c") << OP_CHECKSIG;
        vFixedSeeds.clear(); //! TODO
        vSeeds.clear(); //! TODO

        fMiningRequiresPeers = true;
        fDefaultConsistencyChecks = false;
        fRequireStandard = true;
        fMineBlocksOnDemand = false;
        anyonecanspend_aremine = false;

        checkpointData = (CCheckpointData){
            boost::assign::map_list_of
            (     0, consensus.hashGenesisBlock)
        };

        chainTxData = ChainTxData{
            0,
            0,
            0
        };
        base58Prefixes[PUBKEY_ADDRESS] = std::vector<unsigned char>(1,235);
        base58Prefixes[SCRIPT_ADDRESS] = std::vector<unsigned char>(1,75);
        base58Prefixes[BLINDED_ADDRESS]= std::vector<unsigned char>(1,4);
        base58Prefixes[SECRET_KEY] =     std::vector<unsigned char>(1,239);
        base58Prefixes[EXT_PUBLIC_KEY] = boost::assign::list_of(0x04)(0x35)(0x87)(0xCF).convert_to_container<std::vector<unsigned char> >();
        base58Prefixes[EXT_SECRET_KEY] = boost::assign::list_of(0x04)(0x35)(0x83)(0x94).convert_to_container<std::vector<unsigned char> >();

        base58Prefixes[PARENT_PUBKEY_ADDRESS] = std::vector<unsigned char>(1,111);
        base58Prefixes[PARENT_SCRIPT_ADDRESS] = std::vector<unsigned char>(1,196);
    }
};

/**
 * Use production base58 for tests
 */
class CMainParams : public CElementsParams {
public:
    CMainParams() : CElementsParams() {
        strNetworkID = CHAINPARAMS_OLD_MAIN;

        base58Prefixes[PUBKEY_ADDRESS] = std::vector<unsigned char>(1,0);
        base58Prefixes[SCRIPT_ADDRESS] = std::vector<unsigned char>(1,5);
        base58Prefixes[BLINDED_ADDRESS]= std::vector<unsigned char>(1,11);
        base58Prefixes[SECRET_KEY] =     std::vector<unsigned char>(1,128);
        base58Prefixes[EXT_PUBLIC_KEY] = boost::assign::list_of(0x04)(0x88)(0xB2)(0x1E).convert_to_container<std::vector<unsigned char> >();
        base58Prefixes[EXT_SECRET_KEY] = boost::assign::list_of(0x04)(0x88)(0xAD)(0xE4).convert_to_container<std::vector<unsigned char> >();

        base58Prefixes[PARENT_PUBKEY_ADDRESS] = std::vector<unsigned char>(1,0);
        base58Prefixes[PARENT_SCRIPT_ADDRESS] = std::vector<unsigned char>(1,5);
    }
};

/**
 * Regression test
 */
class CRegTestParams : public CChainParams {
public:
    CRegTestParams() {
        const CScript defaultRegtestScript(CScript() << OP_TRUE);
        CScript genesisChallengeScript = StrHexToScriptWithDefault(GetArg("-signblockscript", ""), defaultRegtestScript);
        consensus.fedpegScript = StrHexToScriptWithDefault(GetArg("-fedpegscript", ""), defaultRegtestScript);

        strNetworkID = CHAINPARAMS_REGTEST;
        consensus.nSubsidyHalvingInterval = 150;
        consensus.BIP34Height = 100000000; // BIP34 has not activated on regtest (far in the future so block v1 are not rejected in tests)
        consensus.BIP34Hash = uint256();
        consensus.BIP65Height = 1351; // BIP65 activated on regtest (Used in rpc activation tests)
        consensus.BIP66Height = 1251; // BIP66 activated on regtest (Used in rpc activation tests)
        consensus.powLimit = uint256S("7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff");
        consensus.parentChainPowLimit = uint256S("7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff");
        consensus.nPowTargetTimespan = 14 * 24 * 60 * 60; // two weeks
        consensus.nPowTargetSpacing = 10 * 60;
        consensus.fPowAllowMinDifficultyBlocks = true;
        consensus.fPowNoRetargeting = true;
        consensus.nRuleChangeActivationThreshold = 108; // 75% for testchains
        consensus.nMinerConfirmationWindow = 144; // Faster than normal for regtest (144 instead of 2016)
        consensus.vDeployments[Consensus::DEPLOYMENT_TESTDUMMY].bit = 28;
        consensus.vDeployments[Consensus::DEPLOYMENT_TESTDUMMY].nStartTime = 0;
        consensus.vDeployments[Consensus::DEPLOYMENT_TESTDUMMY].nTimeout = 999999999999ULL;
        consensus.vDeployments[Consensus::DEPLOYMENT_CSV].bit = 0;
        consensus.vDeployments[Consensus::DEPLOYMENT_CSV].nStartTime = 0;
        consensus.vDeployments[Consensus::DEPLOYMENT_CSV].nTimeout = 999999999999ULL;
        consensus.vDeployments[Consensus::DEPLOYMENT_SEGWIT].bit = 1;
        consensus.vDeployments[Consensus::DEPLOYMENT_SEGWIT].nStartTime = 0;
        consensus.vDeployments[Consensus::DEPLOYMENT_SEGWIT].nTimeout = 999999999999ULL;

        // The best chain should have at least this much work.
        consensus.nMinimumChainWork = uint256S("0x00");

        // By default assume that the signatures in ancestors of this block are valid.
        consensus.defaultAssumeValid = uint256S("0x00");

        pchMessageStart[0] = 0xfa;
        pchMessageStart[1] = 0xbf;
        pchMessageStart[2] = 0xb5;
        pchMessageStart[3] = 0xda;
        nDefaultPort = 7042;
        nPruneAfterHeight = 1000;

        parentGenesisBlockHash = uint256S("0f9188f13cb7b2c71f2a335e3a4fc328bf5beb436012afca590b1a11466e2206");

        // Generate pegged Bitcoin asset
        std::vector<unsigned char> commit = CommitToArguments(consensus, strNetworkID, genesisChallengeScript);
        uint256 entropy;
        GenerateAssetEntropy(entropy,  COutPoint(uint256(commit), 0), parentGenesisBlockHash);
        CalculateAsset(consensus.pegged_asset, entropy);

        genesis = CreateGenesisBlock(consensus, strNetworkID, defaultRegtestScript, 1296688602, genesisChallengeScript, 1, MAX_MONEY, 100, consensus.pegged_asset);
        consensus.hashGenesisBlock = genesis.GetHash();


        scriptCoinbaseDestination = CScript(); // Allow any coinbase destination

        vFixedSeeds.clear(); //!< Regtest mode doesn't have any fixed seeds.
        vSeeds.clear();      //!< Regtest mode doesn't have any DNS seeds.

        fMiningRequiresPeers = false;
        fDefaultConsistencyChecks = true;
        fRequireStandard = false;
        fMineBlocksOnDemand = true;
        anyonecanspend_aremine = true;

        checkpointData = (CCheckpointData){
            boost::assign::map_list_of
            (     0, consensus.hashGenesisBlock),
        };

        chainTxData = ChainTxData{
            0,
            0,
            0
        };
        base58Prefixes[PUBKEY_ADDRESS] = std::vector<unsigned char>(1,235);
        base58Prefixes[SCRIPT_ADDRESS] = std::vector<unsigned char>(1,75);
        base58Prefixes[BLINDED_ADDRESS]= std::vector<unsigned char>(1,4);
        base58Prefixes[SECRET_KEY] =     std::vector<unsigned char>(1,239);
        base58Prefixes[EXT_PUBLIC_KEY] = boost::assign::list_of(0x04)(0x35)(0x87)(0xCF).convert_to_container<std::vector<unsigned char> >();
        base58Prefixes[EXT_SECRET_KEY] = boost::assign::list_of(0x04)(0x35)(0x83)(0x94).convert_to_container<std::vector<unsigned char> >();

        base58Prefixes[PARENT_PUBKEY_ADDRESS] = std::vector<unsigned char>(1,111);
        base58Prefixes[PARENT_SCRIPT_ADDRESS] = std::vector<unsigned char>(1,196);
    }
};

/**
 * Custom params for testing.
 */
class CCustomParams : public CChainParams {

    void UpdateFromArgs()
    {
        strNetworkID = GetArg("-chainpetname", "custom");

        consensus.fPowAllowMinDifficultyBlocks = GetBoolArg("-con_fpowallowmindifficultyblocks", true);
        consensus.fPowNoRetargeting = GetBoolArg("-con_fpownoretargeting", true);
        consensus.nSubsidyHalvingInterval = GetArg("-con_nsubsidyhalvinginterval", 150);
        consensus.BIP34Height = GetArg("-con_bip34height", 100000000);
        consensus.BIP65Height = GetArg("-con_bip65height", 1351);
        consensus.BIP66Height = GetArg("-con_bip66height", 1251);
        consensus.nPowTargetTimespan = GetArg("-con_npowtargettimespan", 14 * 24 * 60 * 60); // two weeks
        consensus.nPowTargetSpacing = GetArg("-con_npowtargetspacing", 10 * 60);
        consensus.nRuleChangeActivationThreshold = GetArg("-con_nrulechangeactivationthreshold", 108); // 75% for testchains
        consensus.nMinerConfirmationWindow = GetArg("-con_nminerconfirmationwindow", 144); // Faster than normal for custom (144 instead of 2016)
        consensus.powLimit = uint256S(GetArg("-con_powlimit", "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"));
        consensus.BIP34Hash = uint256S(GetArg("-con_bip34hash", "0x0"));
        consensus.nMinimumChainWork = uint256S(GetArg("-con_nminimumchainwork", "0x0"));
        // By default assume that the signatures in ancestors of this block are valid.
        consensus.defaultAssumeValid = uint256S(GetArg("-con_defaultassumevalid", "0x00"));

        nDefaultPort = GetArg("-ndefaultport", 18444);
        nPruneAfterHeight = GetArg("-npruneafterheight", 1000);
        fDefaultConsistencyChecks = GetBoolArg("-fdefaultconsistencychecks", true);
        fRequireStandard = GetBoolArg("-frequirestandard", false);
        fMineBlocksOnDemand = GetBoolArg("-fmineblocksondemand", true);
        anyonecanspend_aremine = GetBoolArg("-anyonecanspendaremine", true);
    }

public:
    CCustomParams()
    {
        consensus.vDeployments[Consensus::DEPLOYMENT_TESTDUMMY].bit = 28;
        consensus.vDeployments[Consensus::DEPLOYMENT_TESTDUMMY].nStartTime = 0;
        consensus.vDeployments[Consensus::DEPLOYMENT_TESTDUMMY].nTimeout = 999999999999ULL;
        consensus.vDeployments[Consensus::DEPLOYMENT_CSV].bit = 0;
        consensus.vDeployments[Consensus::DEPLOYMENT_CSV].nStartTime = 0;
        consensus.vDeployments[Consensus::DEPLOYMENT_CSV].nTimeout = 999999999999ULL;
        consensus.vDeployments[Consensus::DEPLOYMENT_SEGWIT].bit = 1;
        consensus.vDeployments[Consensus::DEPLOYMENT_SEGWIT].nStartTime = 0;
        consensus.vDeployments[Consensus::DEPLOYMENT_SEGWIT].nTimeout = 999999999999ULL;

        pchMessageStart[0] = 0xfa;
        pchMessageStart[1] = 0xbf;
        pchMessageStart[2] = 0xb5;
        pchMessageStart[3] = 0xda;
        vFixedSeeds.clear(); //!< Custom mode doesn't have any fixed seeds.
        vSeeds.clear();      //!< Custom mode doesn't have any DNS seeds.
        chainTxData = ChainTxData{
            0,
            0,
            0
        };
        base58Prefixes[PUBKEY_ADDRESS] = std::vector<unsigned char>(1,111);
        base58Prefixes[SCRIPT_ADDRESS] = std::vector<unsigned char>(1,196);
        base58Prefixes[SECRET_KEY] =     std::vector<unsigned char>(1,239);
        base58Prefixes[EXT_PUBLIC_KEY] = boost::assign::list_of(0x04)(0x35)(0x87)(0xCF).convert_to_container<std::vector<unsigned char> >();
        base58Prefixes[EXT_SECRET_KEY] = boost::assign::list_of(0x04)(0x35)(0x83)(0x94).convert_to_container<std::vector<unsigned char> >();

        UpdateFromArgs();
        consensus.hashGenesisBlock = genesis.GetHash();
    }
};


const std::vector<std::string> CChainParams::supportedChains =
    boost::assign::list_of
    ( CHAINPARAMS_ELEMENTS )
    ( CHAINPARAMS_REGTEST )
    ;

static std::unique_ptr<CChainParams> globalChainParams;

const CChainParams &Params() {
    assert(globalChainParams);
    return *globalChainParams;
}

std::unique_ptr<CChainParams> CreateChainParams(const std::string& chain)
{
    if (chain == CBaseChainParams::MAIN)
        return std::unique_ptr<CChainParams>(new CMainParams());
    else if (chain == CHAINPARAMS_ELEMENTS)
        return std::unique_ptr<CChainParams>(new CElementsParams());
    else if (chain == CBaseChainParams::REGTEST)
        return std::unique_ptr<CChainParams>(new CRegTestParams());
    else if (chain == CBaseChainParams::CUSTOM) {
        return std::unique_ptr<CChainParams>(new CCustomParams());
    }
    throw std::runtime_error(strprintf("%s: Unknown chain %s.", __func__, chain));
}

void SelectParams(const std::string& network)
{
    SelectBaseParams(network);
    globalChainParams = CreateChainParams(network);
}

void UpdateBIP9Parameters(Consensus::DeploymentPos d, int64_t nStartTime, int64_t nTimeout)
{
    globalChainParams->UpdateBIP9Parameters(d, nStartTime, nTimeout);
}
 
