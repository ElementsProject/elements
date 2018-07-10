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
#include "crypto/sha256.h"

#include <assert.h>

#include <boost/assign/list_of.hpp>

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

static CBlock CreateGenesisBlock(const Consensus::Params& params, const std::string& networkID, uint32_t nTime, int32_t nVersion)
{
    CMutableTransaction txNew;
    txNew.nVersion = 1;
    txNew.vin.resize(1);
    // Any consensus-related values that are command-line set can be added here for anti-footgun
    txNew.vin[0].scriptSig = CScript(CommitToArguments(params, networkID));
    txNew.vout.clear();
    txNew.vout.push_back(CTxOut(CAsset(), 0, CScript() << OP_RETURN));

    CBlock genesis;
    genesis.nTime    = nTime;
    genesis.proof = CProof(params.signblockscript, CScript());
    genesis.nVersion = nVersion;
    genesis.vtx.push_back(MakeTransactionRef(std::move(txNew)));
    genesis.hashPrevBlock.SetNull();
    genesis.hashMerkleRoot = BlockMerkleRoot(genesis);
    return genesis;
}

/** Add an issuance transaction to the genesis block. Typically used to pre-issue
 * the policyAsset of a blockchain. The genesis block is not actually validated,
 * so this transaction simply has to match issuance structure. */
static void AppendInitialIssuance(CBlock& genesis_block, const COutPoint& prevout, const uint256& contract, const int64_t asset_outputs, const int64_t asset_values, const int64_t reissuance_outputs, const int64_t reissuance_values, const CScript& issuance_destination) {

    uint256 entropy;
    GenerateAssetEntropy(entropy, prevout, contract);

    CAsset asset;
    CalculateAsset(asset, entropy);

    // Re-issuance of policyAsset is always unblinded
    CAsset reissuance;
    CalculateReissuanceToken(reissuance, entropy, false);

    // Note: Genesis block isn't actually validated, outputs are entered into utxo db only
    CMutableTransaction txNew;
    txNew.nVersion = 1;
    txNew.vin.resize(1);
    txNew.vin[0].prevout = prevout;
    txNew.vin[0].assetIssuance.assetEntropy = contract;
    txNew.vin[0].assetIssuance.nAmount = asset_values*asset_outputs;
    txNew.vin[0].assetIssuance.nInflationKeys = reissuance_values*reissuance_outputs;

    for (unsigned int i = 0; i < asset_outputs; i++) {
        txNew.vout.push_back(CTxOut(asset, asset_values, issuance_destination));
    }
    for (unsigned int i = 0; i < reissuance_outputs; i++) {
        txNew.vout.push_back(CTxOut(reissuance, reissuance_values, issuance_destination));
    }

    genesis_block.vtx.push_back(MakeTransactionRef(std::move(txNew)));
    genesis_block.hashMerkleRoot = BlockMerkleRoot(genesis_block);
}

void CChainParams::UpdateBIP9Parameters(Consensus::DeploymentPos d, int64_t nStartTime, int64_t nTimeout)
{
    consensus.vDeployments[d].nStartTime = nStartTime;
    consensus.vDeployments[d].nTimeout = nTimeout;
}

/**
 * Custom chain params
 */
class CCustomParams : public CChainParams {

protected:
    void UpdateFromArgs()
    {
        consensus.nSubsidyHalvingInterval = GetArg("-con_nsubsidyhalvinginterval", 150);
        // BIP34 has not activated on regtest (far in the future so block v1 are not rejected in tests)
        consensus.BIP34Height = GetArg("-con_bip34height", 100000000);
        consensus.BIP34Hash = uint256S(GetArg("-con_bip34hash", "0x00"));
        consensus.BIP65Height = GetArg("-con_bip65height", 1351);
        consensus.BIP66Height = GetArg("-con_bip66height", 1251);
        consensus.powLimit = uint256S(GetArg("-con_powlimit", "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"));
        consensus.parentChainPowLimit = uint256S(GetArg("-con_parentpowlimit", "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"));
        consensus.nPowTargetTimespan = GetArg("-con_npowtargettimespan", 14 * 24 * 60 * 60); // two weeks
        consensus.nPowTargetSpacing = GetArg("-con_npowtargetspacing", 10 * 60);
        consensus.fPowAllowMinDifficultyBlocks = GetBoolArg("-con_fpowallowmindifficultyblocks", true);
        consensus.fPowNoRetargeting = GetBoolArg("-con_fpownoretargeting", true);
        consensus.nRuleChangeActivationThreshold = GetArg("-con_nrulechangeactivationthreshold", 108); // 75% for testchains
        consensus.nMinerConfirmationWindow = GetArg("-con_nminerconfirmationwindow", 144); // Faster than normal for custom (144 instead of 2016)

        // The best chain should have at least this much work.
        consensus.nMinimumChainWork = uint256S(GetArg("-con_nminimumchainwork", "0x00"));
        // By default assume that the signatures in ancestors of this block are valid.
        consensus.defaultAssumeValid = uint256S(GetArg("-con_defaultassumevalid", "0x00"));
        consensus.pegin_min_depth = GetArg("-peginconfirmationdepth", DEFAULT_PEGIN_CONFIRMATION_DEPTH);
        consensus.mandatory_coinbase_destination = StrHexToScriptWithDefault(GetArg("-con_mandatorycoinbase", ""), CScript()); // Blank script allows any coinbase destination
        consensus.parent_chain_signblockscript = StrHexToScriptWithDefault(GetArg("-con_parent_chain_signblockscript", ""), CScript());
        consensus.parent_pegged_asset.SetHex(GetArg("-con_parent_pegged_asset", "0x00"));

        // bitcoin regtest is the parent chain by default
        parentGenesisBlockHash = uint256S(GetArg("-parentgenesisblockhash", "0f9188f13cb7b2c71f2a335e3a4fc328bf5beb436012afca590b1a11466e2206"));
        initialFreeCoins = GetArg("-initialfreecoins", 0);
        initial_reissuance_tokens = GetArg("-initialreissuancetokens", 0);
        consensus.has_parent_chain = GetBoolArg("-con_has_parent_chain", true);
        // Either it has a parent chain or not
        const bool parent_genesis_is_null = parentGenesisBlockHash == uint256();
        assert(consensus.has_parent_chain != parent_genesis_is_null);

        const CScript default_script(CScript() << OP_TRUE);
        consensus.signblockscript = StrHexToScriptWithDefault(GetArg("-signblockscript", ""), default_script);
        consensus.fedpegScript = StrHexToScriptWithDefault(GetArg("-fedpegscript", ""), default_script);

        nDefaultPort = GetArg("-ndefaultport", 7042);
        nPruneAfterHeight = GetArg("-npruneafterheight", 1000);
        fMiningRequiresPeers = GetBoolArg("-fminingrequirespeers", false);
        fDefaultConsistencyChecks = GetBoolArg("-fdefaultconsistencychecks", true);
        fRequireStandard = GetBoolArg("-frequirestandard", false);
        fMineBlocksOnDemand = GetBoolArg("-fmineblocksondemand", true);
        anyonecanspend_aremine = GetBoolArg("-anyonecanspendaremine", true);

        base58Prefixes[PUBKEY_ADDRESS] = std::vector<unsigned char>(1, GetArg("-pubkeyprefix", 235));
        base58Prefixes[SCRIPT_ADDRESS] = std::vector<unsigned char>(1, GetArg("-scriptprefix", 75));
        base58Prefixes[BLINDED_ADDRESS]= std::vector<unsigned char>(1, GetArg("-blindedprefix", 4));
        base58Prefixes[SECRET_KEY] =     std::vector<unsigned char>(1, GetArg("-secretprefix", 239));

        std::string extpubprefix = GetArg("-extpubkeyprefix", "043587CF");
        if (!IsHex(extpubprefix) || extpubprefix.size() != 8) {
            assert("-extpubkeyprefix must be hex string of length 8" && false);
        }
        base58Prefixes[EXT_PUBLIC_KEY] = ParseHex(extpubprefix);

        std::string extprvprefix = GetArg("-extprvkeyprefix", "04358394");
        if (!IsHex(extprvprefix) || extprvprefix.size() != 8) {
            assert("-extprvkeyprefix must be hex string of length 8" && false);
        }
        base58Prefixes[EXT_SECRET_KEY] = ParseHex(extprvprefix);
        base58Prefixes[PARENT_PUBKEY_ADDRESS] = std::vector<unsigned char>(1, GetArg("-parentpubkeyprefix", 111));
        base58Prefixes[PARENT_SCRIPT_ADDRESS] = std::vector<unsigned char>(1, GetArg("-parentscriptprefix", 196));

    }

public:
    CCustomParams(const std::string& chain) : CChainParams(chain)
    {
        this->UpdateFromArgs();

        if (!anyonecanspend_aremine) {
            assert("Anyonecanspendismine was marked as false, but they are in the genesis block"
                    && initialFreeCoins == 0);
        }

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

        // Generate pegged Bitcoin asset
        std::vector<unsigned char> commit = CommitToArguments(consensus, strNetworkID);
        uint256 entropy;
        GenerateAssetEntropy(entropy,  COutPoint(uint256(commit), 0), parentGenesisBlockHash);
        CalculateAsset(consensus.pegged_asset, entropy);

        genesis = CreateGenesisBlock(consensus, strNetworkID, 1296688602, 1);
        if (initialFreeCoins != 0 || initial_reissuance_tokens != 0) {
            AppendInitialIssuance(genesis, COutPoint(uint256(commit), 0), parentGenesisBlockHash, (initialFreeCoins > 0) ? 1 : 0, initialFreeCoins, (initial_reissuance_tokens > 0) ? 1 : 0, initial_reissuance_tokens, CScript() << OP_TRUE);
        }
        consensus.hashGenesisBlock = genesis.GetHash();



        vFixedSeeds.clear(); //!< Regtest mode doesn't have any fixed seeds.
        vSeeds.clear();      //!< Regtest mode doesn't have any DNS seeds.

        checkpointData = (CCheckpointData){
            boost::assign::map_list_of
            (     0, consensus.hashGenesisBlock),
        };

        chainTxData = ChainTxData{
            0,
            0,
            0
        };
    }
};

/**
 * Use base58 and other old configurations for outdated unittests
 */
class CMainParams : public CCustomParams {
public:
    CMainParams(const std::string& chain) : CCustomParams(chain)
    {
        consensus.nRuleChangeActivationThreshold = 1916; // 95% of 2016
        consensus.nMinerConfirmationWindow = 2016; // nPowTargetTimespan / nPowTargetSpacing
        consensus.vDeployments[Consensus::DEPLOYMENT_TESTDUMMY].bit = 28;
        consensus.vDeployments[Consensus::DEPLOYMENT_TESTDUMMY].nStartTime = 1199145601; // January 1, 2008
        consensus.vDeployments[Consensus::DEPLOYMENT_TESTDUMMY].nTimeout = 1230767999; // December 31, 2008

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


const std::vector<std::string> CChainParams::supportedChains =
    boost::assign::list_of
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
        return std::unique_ptr<CChainParams>(new CMainParams(chain));
    return std::unique_ptr<CChainParams>(new CCustomParams(chain));
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
