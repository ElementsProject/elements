// Copyright (c) 2010 Satoshi Nakamoto
// Copyright (c) 2009-2016 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "chainparams.h"
#include "consensus/merkle.h"
#include "issuance.h"
#include "ethaddress.h"

#include "tinyformat.h"
#include "util.h"
#include "utilstrencodings.h"
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
    sha2.Write((const unsigned char*)HexStr(params.parentContract).c_str(), HexStr(params.parentContract).length());
    sha2.Write((const unsigned char*)HexStr(params.fedpegAddress).c_str(), HexStr(params.fedpegAddress).length());
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

static CBlock CreateGenesisBlock(const Consensus::Params& params, const std::string& networkID, uint32_t nTime, const CScript& scriptChallenge, int32_t nVersion)
{
    CMutableTransaction txNew;
    txNew.nVersion = 1;
    txNew.vin.resize(1);
    // Any consensus-related values that are command-line set can be added here for anti-footgun
    txNew.vin[0].scriptSig = CScript(CommitToArguments(params, networkID, scriptChallenge));
    txNew.vout.clear();
    txNew.vout.push_back(CTxOut(CAsset(), 0, CScript() << OP_RETURN));

    // If issuance controller script exists add to genesis coinbase transaction in an op_return script
    std::string issuecontrolscript = GetArg("-issuecontrolscript", "");
    if (issuecontrolscript != "")
    {
        txNew.vout.push_back(CTxOut(CAsset(), 0, CScript() << OP_RETURN << ParseHex(issuecontrolscript)));
    }

    CBlock genesis;
    genesis.nTime    = nTime;
    genesis.proof = CProof(scriptChallenge, CScript());
    genesis.nVersion = nVersion;
    genesis.vtx.push_back(MakeTransactionRef(std::move(txNew)));
    genesis.hashPrevBlock.SetNull();
    genesis.hashMerkleRoot = BlockMerkleRoot(genesis);
    if (GetBoolArg("-embedcontract", DEFAULT_EMBED_CONTRACT)) {
        genesis.hashContract = GetContractHash(networkID);
    }
    if (GetBoolArg("-embedmapping", DEFAULT_EMBED_MAPPING)) {
        // no mapping exists at/prior to the genesis
        genesis.hashMapping = uint256S("");
    }
    genesis.hashAttestation = uint256S(GetArg("-attestationhash", ""));
    return genesis;
}

/** Add an issuance transaction to the genesis block. Typically used to pre-issue
 * the policyAsset of a blockchain. The genesis block is not actually validated,
 * so this transaction simply has to match issuance structure. */
static void AppendInitialIssuance(CBlock& genesis_block, const COutPoint& prevout, const uint256& contract, const int64_t asset_outputs,
    const int64_t asset_values, const int64_t reissuance_outputs, const int64_t reissuance_values, const CScript& issuance_destination) {

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
        // eth mainnet is the parent genesis blockhash by default
        parentGenesisBlockHash = uint256S(GetArg("-parentgenesisblockhash", "d4e56740f876aef8c010b86a40d5f56745a118d0906a34e69aec8c0db1cb8fa3"));
        initialFreeCoins = GetArg("-initialfreecoins", 0);
        policyCoins = GetArg("-policycoins", 0);
        genesisTimeStamp = GetArg("-genesistimestamp", 1514764800);
        initialFreeCoinsDestination = StrHexToScriptWithDefault(GetArg("-initialfreecoinsdestination", ""), CScript() << OP_TRUE);
        freezeListCoinsDestination = StrHexToScriptWithDefault(GetArg("-freezelistcoinsdestination", ""), CScript() << OP_RETURN);
        burnListCoinsDestination = StrHexToScriptWithDefault(GetArg("-burnlistcoinsdestination", ""), CScript() << OP_RETURN);
        whiteListCoinsDestination = StrHexToScriptWithDefault(GetArg("-whitelistcoinsdestination", ""), CScript() << OP_RETURN);
        challengeCoinsDestination = StrHexToScriptWithDefault(GetArg("-challengecoinsdestination", ""), CScript() << OP_RETURN);
        permissionCoinsDestination = StrHexToScriptWithDefault(GetArg("-permissioncoinsdestination", ""), CScript() << OP_RETURN);
        issuanceCoinsDestination = StrHexToScriptWithDefault(GetArg("-issuancecoinsdestination", ""), CScript() << OP_RETURN);
        attestationHash = uint256S(GetArg("-attestationhash", ""));

        nDefaultPort = GetArg("-ndefaultport", 7042);
        nPruneAfterHeight = GetArg("-npruneafterheight", 1000);
        fMiningRequiresPeers = GetBoolArg("-fminingrequirespeers", false);
        fDefaultConsistencyChecks = GetBoolArg("-fdefaultconsistencychecks", true);
        fRequireStandard = GetBoolArg("-frequirestandard", false);
        fEmbedContract = GetBoolArg("-embedcontract", DEFAULT_EMBED_CONTRACT);
        fContractInTx = GetBoolArg("-contractintx", DEFAULT_CONTRACT_IN_TX);
        fContractInKYCFile = GetBoolArg("-contractinkycfile", DEFAULT_CONTRACT_IN_KYCFILE);
        fEmbedMapping = GetBoolArg("-embedmapping", DEFAULT_EMBED_MAPPING);
        fMineBlocksOnDemand = GetBoolArg("-fmineblocksondemand", true);
        anyonecanspend_aremine = GetBoolArg("-anyonecanspendaremine", true);
    }

public:
    CCustomParams(const std::string& chain) : CChainParams(chain)
    {
        this->UpdateFromArgs();

        const CScript defaultRegtestScript(CScript() << OP_TRUE);
        CScript genesisChallengeScript = StrHexToScriptWithDefault(GetArg("-signblockscript", ""), defaultRegtestScript);
        consensus.fedpegScript = StrHexToScriptWithDefault(GetArg("-fedpegscript", ""), defaultRegtestScript);
        consensus.parentContract.SetHex(GetArg("-parentcontract", "076C97e1c869072eE22f8c91978C99B4bcB02591"));
        consensus.fedpegAddress = CEthAddress(ParseHex(GetArg("-fedpegaddress", "")));

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
        std::vector<unsigned char> commit = CommitToArguments(consensus, strNetworkID, genesisChallengeScript);
        uint256 entropy;
        GenerateAssetEntropy(entropy,  COutPoint(uint256(commit), 0), parentGenesisBlockHash);
        CalculateAsset(consensus.pegged_asset, entropy);

        genesis = CreateGenesisBlock(consensus, strNetworkID, genesisTimeStamp, genesisChallengeScript, 1);
        int nOut = 0;
        if (initialFreeCoins != 0) {
            AppendInitialIssuance(genesis, COutPoint(uint256(commit), nOut), parentGenesisBlockHash, 100, initialFreeCoins/100, 0, 0, initialFreeCoinsDestination);
            ++nOut;
        }

        if (policyCoins != 0) {
            if(!freezeListCoinsDestination.IsUnspendable()) {
                uint256 contract = uint256S("0000000000000000000000000000000000000000000000000000000000000010");
                const COutPoint prevout = COutPoint(uint256(commit), nOut);
                ++nOut;

                GenerateAssetEntropy(entropy,  prevout, contract);
                CalculateAsset(consensus.freezelist_asset, entropy);

                AppendInitialIssuance(genesis, prevout, contract, 100, policyCoins/100, 0, 0, freezeListCoinsDestination);
            }

            if(!burnListCoinsDestination.IsUnspendable()) {
                uint256 contract = uint256S("0000000000000000000000000000000000000000000000000000000000000020");
                const COutPoint prevout = COutPoint(uint256(commit), nOut);
                ++nOut;

                GenerateAssetEntropy(entropy,  prevout, contract);
                CalculateAsset(consensus.burnlist_asset, entropy);

                AppendInitialIssuance(genesis, prevout, contract, 100, policyCoins/100, 0, 0, burnListCoinsDestination);
            }

            if(!whiteListCoinsDestination.IsUnspendable()) {
                uint256 contract = uint256S("0000000000000000000000000000000000000000000000000000000000000030");
                const COutPoint prevout = COutPoint(uint256(commit), nOut);
                ++nOut;

                GenerateAssetEntropy(entropy,  prevout, contract);
                CalculateAsset(consensus.whitelist_asset, entropy);

                AppendInitialIssuance(genesis, prevout, contract, 100, policyCoins/100, 0, 0, whiteListCoinsDestination);
            }

            if(!challengeCoinsDestination.IsUnspendable()) {
                uint256 contract = uint256S("0000000000000000000000000000000000000000000000000000000000000040");
                const COutPoint prevout = COutPoint(uint256(commit), nOut);
                ++nOut;

                GenerateAssetEntropy(entropy,  prevout, contract);
                CalculateAsset(consensus.challenge_asset, entropy);

                AppendInitialIssuance(genesis, prevout, contract, 100, policyCoins/100, 0, 0, challengeCoinsDestination);
            }

            if (!permissionCoinsDestination.IsUnspendable()) {
                uint256 contract = uint256S("0000000000000000000000000000000000000000000000000000000000000050");
                const COutPoint prevout = COutPoint(uint256(commit), nOut);
                ++nOut;

                GenerateAssetEntropy(entropy, prevout, contract);
                CalculateAsset(consensus.permission_asset, entropy);

                AppendInitialIssuance(genesis, prevout, contract, 100, policyCoins / 100, 0, 0, permissionCoinsDestination);
            }

            if (!issuanceCoinsDestination.IsUnspendable()) {
                uint256 contract = uint256S("0000000000000000000000000000000000000000000000000000000000000060");
                const COutPoint prevout = COutPoint(uint256(commit), nOut);
                ++nOut;

                GenerateAssetEntropy(entropy, prevout, contract);
                CalculateAsset(consensus.issuance_asset, entropy);

                AppendInitialIssuance(genesis, prevout, contract, 100, policyCoins / 100, 0, 0, issuanceCoinsDestination);
            }
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
        base58Prefixes[PUBKEY_ADDRESS] = std::vector<unsigned char>(1,235);
        base58Prefixes[SCRIPT_ADDRESS] = std::vector<unsigned char>(1,75);
        base58Prefixes[BLINDED_ADDRESS]= std::vector<unsigned char>(1,4);
        base58Prefixes[EXTENDED_ADDRESS]= std::vector<unsigned char>(1,5);
        base58Prefixes[SECRET_KEY] =     std::vector<unsigned char>(1,239);
        base58Prefixes[EXT_PUBLIC_KEY] = boost::assign::list_of(0x04)(0x35)(0x87)(0xCF).convert_to_container<std::vector<unsigned char> >();
        base58Prefixes[EXT_SECRET_KEY] = boost::assign::list_of(0x04)(0x35)(0x83)(0x94).convert_to_container<std::vector<unsigned char> >();

        base58Prefixes[PARENT_PUBKEY_ADDRESS] = std::vector<unsigned char>(1,111);
        base58Prefixes[PARENT_SCRIPT_ADDRESS] = std::vector<unsigned char>(1,196);
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
        base58Prefixes[EXTENDED_ADDRESS]= std::vector<unsigned char>(1,12);
        base58Prefixes[SECRET_KEY] =     std::vector<unsigned char>(1,128);
        base58Prefixes[EXT_PUBLIC_KEY] = boost::assign::list_of(0x04)(0x88)(0xB2)(0x1E).convert_to_container<std::vector<unsigned char> >();
        base58Prefixes[EXT_SECRET_KEY] = boost::assign::list_of(0x04)(0x88)(0xAD)(0xE4).convert_to_container<std::vector<unsigned char> >();
        base58Prefixes[PARENT_PUBKEY_ADDRESS] = std::vector<unsigned char>(1,0);
        base58Prefixes[PARENT_SCRIPT_ADDRESS] = std::vector<unsigned char>(1,5);
    }
};

/**
 * Gold Params - overriding only key/address prefixes
 */
class CGoldParams : public CCustomParams {
public:
    CGoldParams(const std::string& chain) : CCustomParams(chain)
    {
        base58Prefixes[PUBKEY_ADDRESS] = std::vector<unsigned char>(1,38); // G
        base58Prefixes[SCRIPT_ADDRESS] = std::vector<unsigned char>(1,97); // g
        base58Prefixes[BLINDED_ADDRESS]= std::vector<unsigned char>(1,13);
        base58Prefixes[EXTENDED_ADDRESS]= std::vector<unsigned char>(1,14);
        base58Prefixes[SECRET_KEY] =     std::vector<unsigned char>(1,180);
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
    if (chain == CBaseChainParams::GOLD)
        return std::unique_ptr<CChainParams>(new CGoldParams(chain));
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

