// Copyright (c) 2010 Satoshi Nakamoto
// Copyright (c) 2009-2020 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <chainparams.h>

#include <chainparamsseeds.h>
#include <consensus/merkle.h>
#include <deploymentinfo.h>
#include <hash.h> // for signet block challenge hash
#include <issuance.h>
#include <primitives/transaction.h>
#include <util/system.h>
#include <crypto/sha256.h>

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
    txNew.vin[0].scriptSig = genesisScriptSig;
    txNew.vout.push_back(CTxOut(CAsset(), genesisReward, genesisOutputScript));

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
 * Main network on which people trade goods and services.
 */
class CMainParams : public CChainParams {
public:
    CMainParams() {
        strNetworkID = CBaseChainParams::MAIN;
        consensus.signet_blocks = false;
        consensus.signet_challenge.clear();
        consensus.nSubsidyHalvingInterval = 210000;
        consensus.BIP16Exception = uint256S("0x00000000000002dc756eebf4f49723ed8d30cc28a5f108eb94b1ba88ac4f9c22");
        consensus.BIP34Height = 227931;
        consensus.BIP34Hash = uint256S("0x000000000000024b89b42a942fe0d9fea3bb44ab7bd1b19115dd6a759c0808b8");
        consensus.BIP65Height = 388381; // 000000000000000004c2b624ed5d7756c508d90fd0da2c7c679febfa6c4735f0
        consensus.BIP66Height = 363725; // 00000000000000000379eaa19dce8c9b722d46ae6a57c2f1a988119488b50931
        consensus.CSVHeight = 419328; // 000000000000000004a1b34462cb8aeebd5799177f7a29cf28f2d1961716b5b5
        consensus.SegwitHeight = 481824; // 0000000000000000001c8018d9cb3b742ef25114f27563e3fc4a1902167f9893
        consensus.MinBIP9WarningHeight = 483840; // segwit activation height + miner confirmation window
        consensus.powLimit = uint256S("00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffff");
        consensus.nPowTargetTimespan = 14 * 24 * 60 * 60; // two weeks
        consensus.nPowTargetSpacing = 10 * 60;
        consensus.fPowAllowMinDifficultyBlocks = false;
        consensus.fPowNoRetargeting = false;
        consensus.nRuleChangeActivationThreshold = 1815; // 90% of 2016
        consensus.nMinerConfirmationWindow = 2016; // nPowTargetTimespan / nPowTargetSpacing
        consensus.vDeployments[Consensus::DEPLOYMENT_TESTDUMMY].bit = 28;
        consensus.vDeployments[Consensus::DEPLOYMENT_TESTDUMMY].nStartTime = Consensus::BIP9Deployment::NEVER_ACTIVE;
        consensus.vDeployments[Consensus::DEPLOYMENT_TESTDUMMY].nTimeout = Consensus::BIP9Deployment::NO_TIMEOUT;
        consensus.vDeployments[Consensus::DEPLOYMENT_TESTDUMMY].min_activation_height = 0; // No activation delay
        // DynaFed: never activate (but set to avoid use of unitialized memory in tests)
        consensus.vDeployments[Consensus::DEPLOYMENT_DYNA_FED].bit = 25;
        consensus.vDeployments[Consensus::DEPLOYMENT_DYNA_FED].nStartTime = Consensus::BIP9Deployment::NEVER_ACTIVE;
        consensus.vDeployments[Consensus::DEPLOYMENT_DYNA_FED].nTimeout = Consensus::BIP9Deployment::NO_TIMEOUT;
        consensus.vDeployments[Consensus::DEPLOYMENT_DYNA_FED].min_activation_height = 0; // No activation delay

        // Deployment of Taproot (BIPs 340-342)
        consensus.vDeployments[Consensus::DEPLOYMENT_TAPROOT].bit = 2;
        consensus.vDeployments[Consensus::DEPLOYMENT_TAPROOT].nStartTime = 1619222400; // April 24th, 2021
        consensus.vDeployments[Consensus::DEPLOYMENT_TAPROOT].nTimeout = 1628640000; // August 11th, 2021
        consensus.vDeployments[Consensus::DEPLOYMENT_TAPROOT].min_activation_height = 709632; // Approximately November 12th, 2021

        consensus.nMinimumChainWork = uint256S("0x00000000000000000000000000000000000000001fa4663bbbe19f82de910280");
        consensus.defaultAssumeValid = uint256S("0x00000000000000000008a89e854d57e5667df88f1cdef6fde2fbca1de5b639ad"); // 691719

        consensus.genesis_subsidy = 50*COIN;
        consensus.connect_genesis_outputs = false;
        consensus.subsidy_asset = CAsset();
        anyonecanspend_aremine = false;
        enforce_pak = false;
        multi_data_permitted = false;
        consensus.has_parent_chain = false;
        g_signed_blocks = false;
        g_con_elementsmode = false;
        g_con_blockheightinheader = false;
        consensus.total_valid_epochs = 0;
        consensus.elements_mode = g_con_elementsmode;

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
        m_assumed_blockchain_size = 420;
        m_assumed_chain_state_size = 6;

        genesis = CreateGenesisBlock(1231006505, 2083236893, 0x1d00ffff, 1, 50 * COIN, consensus);
        consensus.hashGenesisBlock = genesis.GetHash();
        assert(consensus.hashGenesisBlock == uint256S("0x000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f"));
        assert(genesis.hashMerkleRoot == uint256S("0x4a5e1e4baab89f3a32518a88c31bc87f618f76673e2cc77ab2127b7afdeda33b"));

        // Note that of those which support the service bits prefix, most only support a subset of
        // possible options.
        // This is fine at runtime as we'll fall back to using them as an addrfetch if they don't support the
        // service bits we want, but we should get them updated to support all service bits wanted by any
        // release ASAP to avoid it where possible.
        vSeeds.emplace_back("seed.bitcoin.sipa.be"); // Pieter Wuille, only supports x1, x5, x9, and xd
        vSeeds.emplace_back("dnsseed.bluematt.me"); // Matt Corallo, only supports x9
        vSeeds.emplace_back("dnsseed.bitcoin.dashjr.org"); // Luke Dashjr
        vSeeds.emplace_back("seed.bitcoinstats.com"); // Christian Decker, supports x1 - xf
        vSeeds.emplace_back("seed.bitcoin.jonasschnelli.ch"); // Jonas Schnelli, only supports x1, x5, x9, and xd
        vSeeds.emplace_back("seed.btc.petertodd.org"); // Peter Todd, only supports x1, x5, x9, and xd
        vSeeds.emplace_back("seed.bitcoin.sprovoost.nl"); // Sjors Provoost
        vSeeds.emplace_back("dnsseed.emzy.de"); // Stephan Oeste
        vSeeds.emplace_back("seed.bitcoin.wiz.biz"); // Jason Maurice

        base58Prefixes[PUBKEY_ADDRESS] = std::vector<unsigned char>(1,0);
        base58Prefixes[SCRIPT_ADDRESS] = std::vector<unsigned char>(1,5);
        base58Prefixes[SECRET_KEY] =     std::vector<unsigned char>(1,128);
        base58Prefixes[EXT_PUBLIC_KEY] = {0x04, 0x88, 0xB2, 0x1E};
        base58Prefixes[EXT_SECRET_KEY] = {0x04, 0x88, 0xAD, 0xE4};

        bech32_hrp = "bc";
        blech32_hrp = bech32_hrp;

        vFixedSeeds = std::vector<uint8_t>(std::begin(chainparams_seed_main), std::end(chainparams_seed_main));

        fDefaultConsistencyChecks = false;
        fRequireStandard = true;
        m_is_test_chain = false;
        m_is_mockable_chain = false;

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

        m_assumeutxo_data = MapAssumeutxo{
         // TODO to be specified in a future patch.
        };

        chainTxData = ChainTxData{
            // Data from RPC: getchaintxstats 4096 00000000000000000008a89e854d57e5667df88f1cdef6fde2fbca1de5b639ad
            /* nTime    */ 1626697539,
            /* nTxCount */ 656509474,
            /* dTxRate  */ 2.424920418708139,
        };
    }
};

/**
 * Testnet (v3): public test network which is reset from time to time.
 */
class CTestNetParams : public CChainParams {
public:
    CTestNetParams() {
        strNetworkID = CBaseChainParams::TESTNET;
        consensus.signet_blocks = false;
        consensus.signet_challenge.clear();
        consensus.nSubsidyHalvingInterval = 210000;
        consensus.BIP16Exception = uint256S("0x00000000dd30457c001f4095d208cc1296b0eed002427aa599874af7a432b105");
        consensus.BIP34Height = 21111;
        consensus.BIP34Hash = uint256S("0x0000000023b3a96d3484e5abb3755c413e7d41500f8e2a5c3f0dd01299cd8ef8");
        consensus.BIP65Height = 581885; // 00000000007f6655f22f98e72ed80d8b06dc761d5da09df0fa1dc4be4f861eb6
        consensus.BIP66Height = 330776; // 000000002104c8c45e99a8853285a3b592602a3ccde2b832481da85e9e4ba182
        consensus.CSVHeight = 770112; // 00000000025e930139bac5c6c31a403776da130831ab85be56578f3fa75369bb
        consensus.SegwitHeight = 834624; // 00000000002b980fcd729daaa248fd9316a5200e9b367f4ff2c42453e84201ca
        consensus.MinBIP9WarningHeight = 836640; // segwit activation height + miner confirmation window
        consensus.powLimit = uint256S("00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffff");
        consensus.nPowTargetTimespan = 14 * 24 * 60 * 60; // two weeks
        consensus.nPowTargetSpacing = 10 * 60;
        consensus.fPowAllowMinDifficultyBlocks = true;
        consensus.fPowNoRetargeting = false;
        consensus.nRuleChangeActivationThreshold = 1512; // 75% for testchains
        consensus.nMinerConfirmationWindow = 2016; // nPowTargetTimespan / nPowTargetSpacing
        consensus.vDeployments[Consensus::DEPLOYMENT_TESTDUMMY].bit = 28;
        consensus.vDeployments[Consensus::DEPLOYMENT_TESTDUMMY].nStartTime = Consensus::BIP9Deployment::NEVER_ACTIVE;
        consensus.vDeployments[Consensus::DEPLOYMENT_TESTDUMMY].nTimeout = Consensus::BIP9Deployment::NO_TIMEOUT;
        consensus.vDeployments[Consensus::DEPLOYMENT_TESTDUMMY].min_activation_height = 0; // No activation delay

        // Deployment of Taproot (BIPs 340-342)
        consensus.vDeployments[Consensus::DEPLOYMENT_TAPROOT].bit = 2;
        consensus.vDeployments[Consensus::DEPLOYMENT_TAPROOT].nStartTime = 1619222400; // April 24th, 2021
        consensus.vDeployments[Consensus::DEPLOYMENT_TAPROOT].nTimeout = 1628640000; // August 11th, 2021
        consensus.vDeployments[Consensus::DEPLOYMENT_TAPROOT].min_activation_height = 0; // No activation delay

        consensus.nMinimumChainWork = uint256S("0x0000000000000000000000000000000000000000000005180c3bd8290da33a1a");
        consensus.defaultAssumeValid = uint256S("0x0000000000004ae2f3896ca8ecd41c460a35bf6184e145d91558cece1c688a76"); // 2010000

        consensus.genesis_subsidy = 50*COIN;
        consensus.connect_genesis_outputs = false;
        consensus.subsidy_asset = CAsset();
        anyonecanspend_aremine = false;
        enforce_pak = false;
        multi_data_permitted = false;
        consensus.has_parent_chain = false;
        g_signed_blocks = false;
        g_con_elementsmode = false;
        g_con_blockheightinheader = false;
        consensus.total_valid_epochs = 0;
        consensus.elements_mode = g_con_elementsmode;

        pchMessageStart[0] = 0x0b;
        pchMessageStart[1] = 0x11;
        pchMessageStart[2] = 0x09;
        pchMessageStart[3] = 0x07;
        nDefaultPort = 18333;
        nPruneAfterHeight = 1000;
        m_assumed_blockchain_size = 40;
        m_assumed_chain_state_size = 2;

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
        blech32_hrp = bech32_hrp;

        vFixedSeeds = std::vector<uint8_t>(std::begin(chainparams_seed_test), std::end(chainparams_seed_test));

        fDefaultConsistencyChecks = false;
        fRequireStandard = false;
        m_is_test_chain = true;
        m_is_mockable_chain = false;

        checkpointData = {
            {
                {546, uint256S("000000002a936ca763904c3c35fce2f3556c559c0214345d31b1bcebf76acb70")},
            }
        };

        m_assumeutxo_data = MapAssumeutxo{
            // TODO to be specified in a future patch.
        };

        chainTxData = ChainTxData{
            // Data from RPC: getchaintxstats 4096 0000000000004ae2f3896ca8ecd41c460a35bf6184e145d91558cece1c688a76
            /* nTime    */ 1625727096,
            /* nTxCount */ 60408943,
            /* dTxRate  */ 0.08379062270367649,
        };
    }
};

/**
 * Signet: test network with an additional consensus parameter (see BIP325).
 */
class SigNetParams : public CChainParams {
public:
    explicit SigNetParams(const ArgsManager& args) {
        std::vector<uint8_t> bin;
        vSeeds.clear();

        if (!args.IsArgSet("-signetchallenge")) {
            bin = ParseHex("512103ad5e0edad18cb1f0fc0d28a3d4f1f3e445640337489abb10404f2d1e086be430210359ef5021964fe22d6f8e05b2463c9540ce96883fe3b278760f048f5189f2e6c452ae");
            vSeeds.emplace_back("178.128.221.177");
            vSeeds.emplace_back("2a01:7c8:d005:390::5");
            vSeeds.emplace_back("v7ajjeirttkbnt32wpy3c6w3emwnfr3fkla7hpxcfokr3ysd3kqtzmqd.onion:38333");

            consensus.nMinimumChainWork = uint256S("0x0000000000000000000000000000000000000000000000000000008546553c03");
            consensus.defaultAssumeValid = uint256S("0x000000187d4440e5bff91488b700a140441e089a8aaea707414982460edbfe54"); // 47200
            m_assumed_blockchain_size = 1;
            m_assumed_chain_state_size = 0;
            chainTxData = ChainTxData{
                // Data from RPC: getchaintxstats 4096 000000187d4440e5bff91488b700a140441e089a8aaea707414982460edbfe54
                /* nTime    */ 1626696658,
                /* nTxCount */ 387761,
                /* dTxRate  */ 0.04035946932424404,
            };
        } else {
            const auto signet_challenge = args.GetArgs("-signetchallenge");
            if (signet_challenge.size() != 1) {
                throw std::runtime_error(strprintf("%s: -signetchallenge cannot be multiple values.", __func__));
            }
            bin = ParseHex(signet_challenge[0]);

            consensus.nMinimumChainWork = uint256{};
            consensus.defaultAssumeValid = uint256{};
            m_assumed_blockchain_size = 0;
            m_assumed_chain_state_size = 0;
            chainTxData = ChainTxData{
                0,
                0,
                0,
            };
            LogPrintf("Signet with challenge %s\n", signet_challenge[0]);
        }

        if (args.IsArgSet("-signetseednode")) {
            vSeeds = args.GetArgs("-signetseednode");
        }

        strNetworkID = CBaseChainParams::SIGNET;
        consensus.signet_blocks = true;
        consensus.signet_challenge.assign(bin.begin(), bin.end());
        consensus.nSubsidyHalvingInterval = 210000;
        consensus.BIP16Exception = uint256{};
        consensus.BIP34Height = 1;
        consensus.BIP34Hash = uint256{};
        consensus.BIP65Height = 1;
        consensus.BIP66Height = 1;
        consensus.CSVHeight = 1;
        consensus.SegwitHeight = 1;
        consensus.nPowTargetTimespan = 14 * 24 * 60 * 60; // two weeks
        consensus.nPowTargetSpacing = 10 * 60;
        consensus.fPowAllowMinDifficultyBlocks = false;
        consensus.fPowNoRetargeting = false;
        consensus.nRuleChangeActivationThreshold = 1815; // 90% of 2016
        consensus.nMinerConfirmationWindow = 2016; // nPowTargetTimespan / nPowTargetSpacing
        consensus.MinBIP9WarningHeight = 0;
        consensus.powLimit = uint256S("00000377ae000000000000000000000000000000000000000000000000000000");
        consensus.vDeployments[Consensus::DEPLOYMENT_TESTDUMMY].bit = 28;
        consensus.vDeployments[Consensus::DEPLOYMENT_TESTDUMMY].nStartTime = Consensus::BIP9Deployment::NEVER_ACTIVE;
        consensus.vDeployments[Consensus::DEPLOYMENT_TESTDUMMY].nTimeout = Consensus::BIP9Deployment::NO_TIMEOUT;
        consensus.vDeployments[Consensus::DEPLOYMENT_TESTDUMMY].min_activation_height = 0; // No activation delay
        // DynaFed: never activate (but set to avoid use of unitialized memory in tests)
        consensus.vDeployments[Consensus::DEPLOYMENT_DYNA_FED].bit = 25;
        consensus.vDeployments[Consensus::DEPLOYMENT_DYNA_FED].nStartTime = Consensus::BIP9Deployment::NEVER_ACTIVE;
        consensus.vDeployments[Consensus::DEPLOYMENT_DYNA_FED].nTimeout = Consensus::BIP9Deployment::NO_TIMEOUT;
        consensus.vDeployments[Consensus::DEPLOYMENT_DYNA_FED].min_activation_height = 0; // No activation delay

        // Activation of Taproot (BIPs 340-342)
        consensus.vDeployments[Consensus::DEPLOYMENT_TAPROOT].bit = 2;
        consensus.vDeployments[Consensus::DEPLOYMENT_TAPROOT].nStartTime = Consensus::BIP9Deployment::ALWAYS_ACTIVE;
        consensus.vDeployments[Consensus::DEPLOYMENT_TAPROOT].nTimeout = Consensus::BIP9Deployment::NO_TIMEOUT;
        consensus.vDeployments[Consensus::DEPLOYMENT_TAPROOT].min_activation_height = 0; // No activation delay

        // ELEMENTS: copied from Main
        consensus.genesis_subsidy = 50*COIN;
        consensus.connect_genesis_outputs = false;
        consensus.subsidy_asset = CAsset();
        anyonecanspend_aremine = false;
        enforce_pak = false;
        multi_data_permitted = false;
        consensus.has_parent_chain = false;
        g_signed_blocks = false; // lol
        g_con_elementsmode = false;
        g_con_blockheightinheader = false;
        consensus.total_valid_epochs = 0;
        consensus.elements_mode = g_con_elementsmode;

        // message start is defined as the first 4 bytes of the sha256d of the block script
        CHashWriter h(SER_DISK, 0);
        h << consensus.signet_challenge;
        uint256 hash = h.GetHash();
        memcpy(pchMessageStart, hash.begin(), 4);

        nDefaultPort = 38333;
        nPruneAfterHeight = 1000;

        genesis = CreateGenesisBlock(1598918400, 52613770, 0x1e0377ae, 1, 50 * COIN, consensus);
        consensus.hashGenesisBlock = genesis.GetHash();
        assert(consensus.hashGenesisBlock == uint256S("0x00000008819873e925422c1ff0f99f7cc9bbb232af63a077a480a3633bee1ef6"));
        assert(genesis.hashMerkleRoot == uint256S("0x4a5e1e4baab89f3a32518a88c31bc87f618f76673e2cc77ab2127b7afdeda33b"));

        vFixedSeeds.clear();

        base58Prefixes[PUBKEY_ADDRESS] = std::vector<unsigned char>(1,111);
        base58Prefixes[SCRIPT_ADDRESS] = std::vector<unsigned char>(1,196);
        base58Prefixes[SECRET_KEY] =     std::vector<unsigned char>(1,239);
        base58Prefixes[EXT_PUBLIC_KEY] = {0x04, 0x35, 0x87, 0xCF};
        base58Prefixes[EXT_SECRET_KEY] = {0x04, 0x35, 0x83, 0x94};

        bech32_hrp = "tb";
        blech32_hrp = bech32_hrp;

        fDefaultConsistencyChecks = false;
        fRequireStandard = true;
        m_is_test_chain = true;
        m_is_mockable_chain = false;
    }
};

/**
 * Regression test: intended for private networks only. Has minimal difficulty to ensure that
 * blocks can be found instantly.
 */
class CRegTestParams : public CChainParams {
public:
    explicit CRegTestParams(const ArgsManager& args) {
        strNetworkID =  CBaseChainParams::REGTEST;
        consensus.signet_blocks = false;
        consensus.signet_challenge.clear();
        consensus.nSubsidyHalvingInterval = 150;
        consensus.BIP16Exception = uint256();
        consensus.BIP34Height = 500; // BIP34 activated on regtest (Used in functional tests)
        consensus.BIP34Hash = uint256();
        consensus.BIP65Height = 1351; // BIP65 activated on regtest (Used in functional tests)
        consensus.BIP66Height = 1251; // BIP66 activated on regtest (Used in functional tests)
        consensus.CSVHeight = 432; // CSV activated on regtest (Used in rpc activation tests)
        consensus.SegwitHeight = 0; // SEGWIT is always activated on regtest unless overridden
        consensus.MinBIP9WarningHeight = 0;
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
        consensus.vDeployments[Consensus::DEPLOYMENT_TESTDUMMY].min_activation_height = 0; // No activation delay

        // DynaFed: never activate (but set to avoid use of unitialized memory in tests)
        consensus.vDeployments[Consensus::DEPLOYMENT_DYNA_FED].bit = 25;
        consensus.vDeployments[Consensus::DEPLOYMENT_DYNA_FED].nStartTime = Consensus::BIP9Deployment::NEVER_ACTIVE;
        consensus.vDeployments[Consensus::DEPLOYMENT_DYNA_FED].nTimeout = Consensus::BIP9Deployment::NO_TIMEOUT;
        consensus.vDeployments[Consensus::DEPLOYMENT_DYNA_FED].min_activation_height = 0; // No activation delay

        consensus.vDeployments[Consensus::DEPLOYMENT_TAPROOT].bit = 2;
        consensus.vDeployments[Consensus::DEPLOYMENT_TAPROOT].nStartTime = gArgs.GetArg("-con_taproot_signal_start", Consensus::BIP9Deployment::ALWAYS_ACTIVE);
        consensus.vDeployments[Consensus::DEPLOYMENT_TAPROOT].nTimeout = Consensus::BIP9Deployment::NO_TIMEOUT;
        consensus.vDeployments[Consensus::DEPLOYMENT_TAPROOT].min_activation_height = 0; // No activation delay
        consensus.vDeployments[Consensus::DEPLOYMENT_TAPROOT].nPeriod = 128; // test ability to change from default
        consensus.vDeployments[Consensus::DEPLOYMENT_TAPROOT].nThreshold = 128;

        consensus.nMinimumChainWork = uint256{};
        consensus.defaultAssumeValid = uint256{};

        consensus.genesis_subsidy = 50*COIN;
        consensus.connect_genesis_outputs = false;
        consensus.subsidy_asset = CAsset();
        anyonecanspend_aremine = false;
        enforce_pak = false;
        multi_data_permitted = false;
        consensus.has_parent_chain = false;
        g_signed_blocks = false;
        g_con_elementsmode = false;
        consensus.elements_mode = g_con_elementsmode;
        g_con_blockheightinheader = false;
        consensus.total_valid_epochs = 0;

        pchMessageStart[0] = 0xfa;
        pchMessageStart[1] = 0xbf;
        pchMessageStart[2] = 0xb5;
        pchMessageStart[3] = 0xda;
        nDefaultPort = 18444;
        nPruneAfterHeight = args.GetBoolArg("-fastprune", false) ? 100 : 1000;
        m_assumed_blockchain_size = 0;
        m_assumed_chain_state_size = 0;

        UpdateActivationParametersFromArgs(args);

        genesis = CreateGenesisBlock(1296688602, 2, 0x207fffff, 1, 50 * COIN, consensus);
        consensus.hashGenesisBlock = genesis.GetHash();
        assert(consensus.hashGenesisBlock == uint256S("0x0f9188f13cb7b2c71f2a335e3a4fc328bf5beb436012afca590b1a11466e2206"));
        assert(genesis.hashMerkleRoot == uint256S("0x4a5e1e4baab89f3a32518a88c31bc87f618f76673e2cc77ab2127b7afdeda33b"));

        vFixedSeeds.clear(); //!< Regtest mode doesn't have any fixed seeds.
        vSeeds.clear();      //!< Regtest mode doesn't have any DNS seeds.

        fDefaultConsistencyChecks = true;
        fRequireStandard = true;
        m_is_test_chain = true;
        m_is_mockable_chain = true;

        checkpointData = {
            {
                {0, uint256S("0f9188f13cb7b2c71f2a335e3a4fc328bf5beb436012afca590b1a11466e2206")},
            }
        };

        m_assumeutxo_data = MapAssumeutxo{
            {
                110,
                {AssumeutxoHash{uint256S("0x09a3e443dbf48f3b95207c9ce529062d9764395232c482aa7d3a0bf274d282d9")}, 110},
            },
            {
                200,
                {AssumeutxoHash{uint256S("0x51c8d11d8b5c1de51543c579736e786aa2736206d1e11e627568029ce092cf62")}, 200},
            },
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
        blech32_hrp = bech32_hrp;
    }

    /**
     * Allows modifying the Version Bits regtest parameters.
     */
    void UpdateVersionBitsParameters(Consensus::DeploymentPos d, int64_t nStartTime, int64_t nTimeout, int min_activation_height)
    {
        consensus.vDeployments[d].nStartTime = nStartTime;
        consensus.vDeployments[d].nTimeout = nTimeout;
        consensus.vDeployments[d].min_activation_height = min_activation_height;
    }
    void UpdateActivationParametersFromArgs(const ArgsManager& args);
};

void CRegTestParams::UpdateActivationParametersFromArgs(const ArgsManager& args)
{
    if (args.IsArgSet("-segwitheight")) {
        int64_t height = args.GetArg("-segwitheight", consensus.SegwitHeight);
        if (height < -1 || height >= std::numeric_limits<int>::max()) {
            throw std::runtime_error(strprintf("Activation height %ld for segwit is out of valid range. Use -1 to disable segwit.", height));
        } else if (height == -1) {
            LogPrintf("Segwit disabled for testing\n");
            height = std::numeric_limits<int>::max();
        }
        consensus.SegwitHeight = static_cast<int>(height);
    }

    if (!args.IsArgSet("-vbparams")) return;

    for (const std::string& strDeployment : args.GetArgs("-vbparams")) {
        std::vector<std::string> vDeploymentParams;
        boost::split(vDeploymentParams, strDeployment, boost::is_any_of(":"));
        if (vDeploymentParams.size() < 3 || 4 < vDeploymentParams.size()) {
            throw std::runtime_error("Version bits parameters malformed, expecting deployment:start:end[:min_activation_height]");
        }
        int64_t nStartTime, nTimeout;
        int min_activation_height = 0;
        if (!ParseInt64(vDeploymentParams[1], &nStartTime)) {
            throw std::runtime_error(strprintf("Invalid nStartTime (%s)", vDeploymentParams[1]));
        }
        if (!ParseInt64(vDeploymentParams[2], &nTimeout)) {
            throw std::runtime_error(strprintf("Invalid nTimeout (%s)", vDeploymentParams[2]));
        }
        if (vDeploymentParams.size() >= 4 && !ParseInt32(vDeploymentParams[3], &min_activation_height)) {
            throw std::runtime_error(strprintf("Invalid min_activation_height (%s)", vDeploymentParams[3]));
        }
        bool found = false;
        for (int j=0; j < (int)Consensus::MAX_VERSION_BITS_DEPLOYMENTS; ++j) {
            if (vDeploymentParams[0] == VersionBitsDeploymentInfo[j].name) {
                UpdateVersionBitsParameters(Consensus::DeploymentPos(j), nStartTime, nTimeout, min_activation_height);
                found = true;
                LogPrintf("Setting version bits activation parameters for %s to start=%ld, timeout=%ld, min_activation_height=%d\n", vDeploymentParams[0], nStartTime, nTimeout, min_activation_height);
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
    void UpdateFromArgs(const ArgsManager& args)
    {
        UpdateActivationParametersFromArgs(args);

        consensus.nSubsidyHalvingInterval = args.GetArg("-con_nsubsidyhalvinginterval", consensus.nSubsidyHalvingInterval);
        consensus.BIP16Exception = uint256S(args.GetArg("-con_bip16exception", "0x0"));
        consensus.BIP34Height = args.GetArg("-con_bip34height", 0);
        consensus.BIP34Hash = uint256S(args.GetArg("-con_bip34hash", "0x0"));
        consensus.BIP65Height = args.GetArg("-con_bip65height", 0);
        consensus.BIP66Height = args.GetArg("-con_bip66height", 0);
        consensus.CSVHeight = args.GetArg("-con_csv_deploy_start", 432);
        consensus.powLimit = uint256S(args.GetArg("-con_powlimit", "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"));
        consensus.nPowTargetTimespan = args.GetArg("-con_npowtargettimespan", consensus.nPowTargetTimespan);
        consensus.nPowTargetSpacing = args.GetArg("-con_npowtargetspacing", consensus.nPowTargetSpacing);
        consensus.fPowAllowMinDifficultyBlocks = args.GetBoolArg("-con_fpowallowmindifficultyblocks", consensus.fPowAllowMinDifficultyBlocks);
        consensus.fPowNoRetargeting = args.GetBoolArg("-con_fpownoretargeting", consensus.fPowNoRetargeting);
        consensus.nRuleChangeActivationThreshold = (uint32_t)args.GetArg("-con_nrulechangeactivationthreshold", consensus.nRuleChangeActivationThreshold);
        consensus.nMinerConfirmationWindow = (uint32_t)args.GetArg("-con_nminerconfirmationwindow", consensus.nMinerConfirmationWindow);

        consensus.nMinimumChainWork = uint256S(args.GetArg("-con_nminimumchainwork", "0x0"));
        consensus.defaultAssumeValid = uint256S(args.GetArg("-con_defaultassumevalid", "0x00"));
        // TODO: Embed in genesis block in nTime field with new genesis block type
        consensus.dynamic_epoch_length = args.GetArg("-dynamic_epoch_length", 10);
        // Default junk keys for testing
        consensus.first_extension_space = {ParseHex("02fcba7ecf41bc7e1be4ee122d9d22e3333671eb0a3a87b5cdf099d59874e1940f02fcba7ecf41bc7e1be4ee122d9d22e3333671eb0a3a87b5cdf099d59874e1940f")};
        std::vector<std::string> pak_list_str = args.GetArgs("-pak");
        if (!pak_list_str.empty()) {
            consensus.first_extension_space.clear();
            for (const auto& entry : pak_list_str) {
                consensus.first_extension_space.push_back(ParseHex(entry));
            }
        }

        nPruneAfterHeight = (uint64_t)args.GetArg("-npruneafterheight", nPruneAfterHeight);
        fDefaultConsistencyChecks = args.GetBoolArg("-fdefaultconsistencychecks", fDefaultConsistencyChecks);
        m_is_test_chain = args.GetBoolArg("-fmineblocksondemand", m_is_test_chain);

        bech32_hrp = args.GetArg("-bech32_hrp", "ert");
        blech32_hrp = args.GetArg("-blech32_hrp", "el");
        base58Prefixes[PUBKEY_ADDRESS] = std::vector<unsigned char>(1, args.GetArg("-pubkeyprefix", 235));
        base58Prefixes[SCRIPT_ADDRESS] = std::vector<unsigned char>(1, args.GetArg("-scriptprefix", 75));
        base58Prefixes[BLINDED_ADDRESS] = std::vector<unsigned char>(1, args.GetArg("-blindedprefix", 4));
        base58Prefixes[SECRET_KEY] =     std::vector<unsigned char>(1, args.GetArg("-secretprefix", 239));
        base58Prefixes[PARENT_PUBKEY_ADDRESS] = std::vector<unsigned char>(1, args.GetArg("-parentpubkeyprefix", 111));
        base58Prefixes[PARENT_SCRIPT_ADDRESS] = std::vector<unsigned char>(1, args.GetArg("-parentscriptprefix", 196));
        parent_bech32_hrp = args.GetArg("-parent_bech32_hrp", "bcrt");
        parent_blech32_hrp = args.GetArg("-parent_blech32_hrp", "bcrt");


        std::string extpubprefix = args.GetArg("-extpubkeyprefix", "043587CF");
        assert(IsHex(extpubprefix) && extpubprefix.size() == 8 && "-extpubkeyprefix must be hex string of length 8");
        base58Prefixes[EXT_PUBLIC_KEY] = ParseHex(extpubprefix);

        std::string extprvprefix = args.GetArg("-extprvkeyprefix", "04358394");
        assert(IsHex(extprvprefix) && extprvprefix.size() == 8 && "-extprvkeyprefix must be hex string of length 8");
        base58Prefixes[EXT_SECRET_KEY] = ParseHex(extprvprefix);

        const std::string magic_str = args.GetArg("-pchmessagestart", "5319F20E");
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
        consensus.genesis_style = args.GetArg("-con_genesis_style", "elements");

        // Block signing encumberance script, default of 51 aka OP_TRUE
        std::vector<unsigned char> sign_bytes = ParseHex(args.GetArg("-signblockscript", "51"));
        consensus.signblockscript = CScript(sign_bytes.begin(), sign_bytes.end());
        // Default signature size is the size of dummy push, and single 72 byte DER signature
        consensus.max_block_signature_size = args.GetArg("-con_max_block_sig_size", 74);
        g_signed_blocks = args.GetBoolArg("-con_signed_blocks", true);

        // Note: These globals are needed to avoid circular dependencies.
        // Default to true for custom chains.
        g_con_blockheightinheader = args.GetBoolArg("-con_blockheightinheader", true);
        g_con_elementsmode = args.GetBoolArg("-con_elementsmode", true);
        consensus.elements_mode = g_con_elementsmode;

        // No subsidy for custom chains by default
        consensus.genesis_subsidy = args.GetArg("-con_blocksubsidy", 0);

        // All non-zero coinbase outputs must go to this scriptPubKey
        std::vector<unsigned char> man_bytes = ParseHex(args.GetArg("-con_mandatorycoinbase", ""));
        consensus.mandatory_coinbase_destination = CScript(man_bytes.begin(), man_bytes.end()); // Blank script allows any coinbase destination

        // Custom chains connect coinbase outputs to db by default
        consensus.connect_genesis_outputs = args.GetArg("-con_connect_genesis_outputs", true);

        initialFreeCoins = args.GetArg("-initialfreecoins", 0);

        anyonecanspend_aremine = args.GetBoolArg("-anyonecanspendaremine", true);

        consensus.has_parent_chain = args.GetBoolArg("-con_has_parent_chain", true);

        enforce_pak = args.GetBoolArg("-enforce_pak", false);

        // Allow multiple op_return outputs by relay policy
        multi_data_permitted = args.GetBoolArg("-multi_data_permitted", enforce_pak);

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

        // Calculate pegged Bitcoin asset
        std::vector<unsigned char> commit = CommitToArguments(consensus, strNetworkID);
        uint256 entropy;
        GenerateAssetEntropy(entropy,  COutPoint(uint256(commit), 0), parentGenesisBlockHash);

        consensus.total_valid_epochs = args.GetArg("-total_valid_epochs", 2);

        // Elements serialization uses derivation, bitcoin serialization uses 0x00
        if (g_con_elementsmode) {
            CalculateAsset(consensus.pegged_asset, entropy);
        } else {
            assert(consensus.pegged_asset == CAsset());
        }

        consensus.parent_pegged_asset.SetHex(args.GetArg("-con_parent_pegged_asset", "0x00"));
        initial_reissuance_tokens = args.GetArg("-initialreissuancetokens", 0);

        // Subsidy asset, like policyAsset, defaults to the pegged_asset
        consensus.subsidy_asset = consensus.pegged_asset;
        if (args.IsArgSet("-subsidyasset")) {
            consensus.subsidy_asset = CAsset(uint256S(args.GetArg("-subsidyasset", "0x00")));
        }

        consensus.vDeployments[Consensus::DEPLOYMENT_DYNA_FED].bit = 25;
        consensus.vDeployments[Consensus::DEPLOYMENT_DYNA_FED].nStartTime = args.GetArg("-con_dyna_deploy_start", Consensus::BIP9Deployment::ALWAYS_ACTIVE);
        consensus.vDeployments[Consensus::DEPLOYMENT_DYNA_FED].nTimeout = Consensus::BIP9Deployment::NO_TIMEOUT;
        consensus.vDeployments[Consensus::DEPLOYMENT_DYNA_FED].min_activation_height = 0; // No activation delay
        // END ELEMENTS fields
    }

    void SetGenesisBlock() {
        if (consensus.genesis_style == "bitcoin") {
            // For compatibility with bitcoin (regtest)
            genesis = CreateGenesisBlock(1296688602, 2, 0x207fffff, 1, 50 * COIN, consensus);
        } else if (consensus.genesis_style == "elements") {
            // Intended compatibility with Liquid v1 and elements-0.14.1
            std::vector<unsigned char> commit = CommitToArguments(consensus, strNetworkID);
            genesis = CreateGenesisBlock(consensus, CScript() << commit, CScript(OP_RETURN), 1296688602, 2, 0x207fffff, 1, 0);
            if (initialFreeCoins != 0 || initial_reissuance_tokens != 0) {
                AppendInitialIssuance(genesis, COutPoint(uint256(commit), 0), parentGenesisBlockHash, (initialFreeCoins > 0) ? 1 : 0, initialFreeCoins, (initial_reissuance_tokens > 0) ? 1 : 0, initial_reissuance_tokens, CScript() << OP_TRUE);
            }
        } else if (consensus.genesis_style == "dynamic") {
            // Liquid v2 HF, from genesis. Upgrading networks still use "elements".
            // TODO fill out genesis block with special commitments including epoch
            // length in nTime
            throw std::runtime_error(strprintf("Invalid -genesis_style (%s)", consensus.genesis_style));
        } else {
            throw std::runtime_error(strprintf("Invalid -genesis_style (%s)", consensus.genesis_style));
        }
    }

public:
    CCustomParams(const std::string& chain, const ArgsManager& args) : CRegTestParams(args)
    {
        strNetworkID = chain;
        UpdateFromArgs(args);
        SetGenesisBlock();
        consensus.hashGenesisBlock = genesis.GetHash();
    }
};

/**
 * Liquid v1
 */
class CLiquidV1Params : public CChainParams {
public:
    CLiquidV1Params()
    {

        strNetworkID = "liquidv1";
        consensus.nSubsidyHalvingInterval = 150;
        consensus.BIP16Exception = uint256();
        consensus.BIP34Height = 0;
        consensus.BIP34Hash = uint256();
        consensus.BIP65Height = 0;
        consensus.BIP66Height = 0;
        consensus.CSVHeight = 0;
        consensus.SegwitHeight = 0;
        consensus.powLimit = uint256S("7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff");
        consensus.nPowTargetTimespan = 14 * 24 * 60 * 60; // two weeks;
        consensus.nPowTargetSpacing = 60; // Minute block assumption
        consensus.fPowAllowMinDifficultyBlocks = true;
        consensus.fPowNoRetargeting = true;
        consensus.nRuleChangeActivationThreshold = 108;
        consensus.nMinerConfirmationWindow = 144;

        consensus.nMinimumChainWork = uint256();
        consensus.defaultAssumeValid = uint256();

        nPruneAfterHeight = 1000;
        fDefaultConsistencyChecks = false;
        fRequireStandard = true;
        m_is_test_chain = false;

        m_assumed_blockchain_size = 3;
        m_assumed_chain_state_size = 1;

        bech32_hrp = "ex"; // ex(plicit)
        blech32_hrp = "lq"; // l(i)q(uid)
        parent_bech32_hrp = "bc";
        parent_blech32_hrp = "bc"; // Doesn't exist but...

        base58Prefixes[PUBKEY_ADDRESS] = std::vector<unsigned char>(1, 57);
        base58Prefixes[SCRIPT_ADDRESS] = std::vector<unsigned char>(1, 39);
        base58Prefixes[SECRET_KEY] =     std::vector<unsigned char>(1, 128);
        base58Prefixes[BLINDED_ADDRESS]= std::vector<unsigned char>(1,12);

        base58Prefixes[EXT_PUBLIC_KEY] = {0x04, 0x88, 0xB2, 0x1E};
        base58Prefixes[EXT_SECRET_KEY] = {0x04, 0x88, 0xAD, 0xE4};

        base58Prefixes[PARENT_PUBKEY_ADDRESS] = std::vector<unsigned char>(1,0);
        base58Prefixes[PARENT_SCRIPT_ADDRESS] = std::vector<unsigned char>(1,5);

        pchMessageStart[0] = 0xfa;
        pchMessageStart[1] = 0xbf;
        pchMessageStart[2] = 0xb5;
        pchMessageStart[3] = 0xda;

        nDefaultPort = 7042;

        vSeeds.clear();
        vSeeds.emplace_back("seed.liquidnetwork.io");
        vFixedSeeds = std::vector<uint8_t>(std::begin(pnSeed6_liquidv1), std::end(pnSeed6_liquidv1));

        //
        // ELEMENTS fields

        consensus.genesis_style = "elements"; // unused here but let's set it anyways

        // Block signing encumberance script, default of 51 aka OP_TRUE
        std::vector<unsigned char> sign_bytes = ParseHex("5b21026a2a106ec32c8a1e8052e5d02a7b0a150423dbd9b116fc48d46630ff6e6a05b92102791646a8b49c2740352b4495c118d876347bf47d0551c01c4332fdc2df526f1a2102888bda53a424466b0451627df22090143bbf7c060e9eacb1e38426f6b07f2ae12102aee8967150dee220f613de3b239320355a498808084a93eaf39a34dcd62024852102d46e9259d0a0bb2bcbc461a3e68f34adca27b8d08fbe985853992b4b104e27412102e9944e35e5750ab621e098145b8e6cf373c273b7c04747d1aa020be0af40ccd62102f9a9d4b10a6d6c56d8c955c547330c589bb45e774551d46d415e51cd9ad5116321033b421566c124dfde4db9defe4084b7aa4e7f36744758d92806b8f72c2e943309210353dcc6b4cf6ad28aceb7f7b2db92a4bf07ac42d357adf756f3eca790664314b621037f55980af0455e4fb55aad9b85a55068bb6dc4740ea87276dc693f4598db45fa210384001daa88dabd23db878dbb1ce5b4c2a5fa72c3113e3514bf602325d0c37b8e21039056d089f2fe72dbc0a14780b4635b0dc8a1b40b7a59106325dd1bc45cc70493210397ab8ea7b0bf85bc7fc56bb27bf85e75502e94e76a6781c409f3f2ec3d1122192103b00e3b5b77884bf3cae204c4b4eac003601da75f96982ffcb3dcb29c5ee419b92103c1f3c0874cfe34b8131af34699589aacec4093399739ae352e8a46f80a6f68375fae");
        consensus.signblockscript = CScript(sign_bytes.begin(), sign_bytes.end());
        // 11 signatures, 15 pubkeys, plus wiggle room
        consensus.max_block_signature_size = 12*74+16*33;
        g_signed_blocks = true;

        g_con_blockheightinheader = true;
        g_con_elementsmode = true;
        consensus.elements_mode = g_con_elementsmode;
        consensus.total_valid_epochs = 2;
        consensus.dynamic_epoch_length = 20160;


        consensus.genesis_subsidy = 0;

        // All non-zero coinbase outputs must go to this scriptPubKey
        std::vector<unsigned char> man_bytes = ParseHex("76a914fc26751a5025129a2fd006c6fbfa598ddd67f7e188ac");
        consensus.mandatory_coinbase_destination = CScript(man_bytes.begin(), man_bytes.end()); // Blank script allows any coinbase destination

        // Custom chains connect coinbase outputs to db by default
        consensus.connect_genesis_outputs = true;

        initialFreeCoins = 0;

        anyonecanspend_aremine = false;

        consensus.has_parent_chain = true;

        enforce_pak = true;

        multi_data_permitted = true;

        parentGenesisBlockHash = uint256S("000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f");
        const bool parent_genesis_is_null = parentGenesisBlockHash == uint256();
        assert(consensus.has_parent_chain != parent_genesis_is_null);
        consensus.parentChainPowLimit = uint256S("0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff");
        consensus.parent_chain_signblockscript = CScript(); // It has PoW
        consensus.pegin_min_depth = 100;

        const CScript default_script(CScript() << OP_TRUE);
        consensus.fedpegScript = StrHexToScriptWithDefault("745c87635b21020e0338c96a8870479f2396c373cc7696ba124e8635d41b0ea581112b678172612102675333a4e4b8fb51d9d4e22fa5a8eaced3fdac8a8cbf9be8c030f75712e6af992102896807d54bc55c24981f24a453c60ad3e8993d693732288068a23df3d9f50d4821029e51a5ef5db3137051de8323b001749932f2ff0d34c82e96a2c2461de96ae56c2102a4e1a9638d46923272c266631d94d36bdb03a64ee0e14c7518e49d2f29bc40102102f8a00b269f8c5e59c67d36db3cdc11b11b21f64b4bffb2815e9100d9aa8daf072103079e252e85abffd3c401a69b087e590a9b86f33f574f08129ccbd3521ecf516b2103111cf405b627e22135b3b3733a4a34aa5723fb0f58379a16d32861bf576b0ec2210318f331b3e5d38156da6633b31929c5b220349859cc9ca3d33fb4e68aa08401742103230dae6b4ac93480aeab26d000841298e3b8f6157028e47b0897c1e025165de121035abff4281ff00660f99ab27bb53e6b33689c2cd8dcd364bc3c90ca5aea0d71a62103bd45cddfacf2083b14310ae4a84e25de61e451637346325222747b157446614c2103cc297026b06c71cbfa52089149157b5ff23de027ac5ab781800a578192d175462103d3bde5d63bdb3a6379b461be64dad45eabff42f758543a9645afd42f6d4248282103ed1e8d5109c9ed66f7941bc53cc71137baa76d50d274bda8d5e8ffbd6e61fe9a5f6702c00fb275522103aab896d53a8e7d6433137bbba940f9c521e085dd07e60994579b64a6d992cf79210291b7d0b1b692f8f524516ed950872e5da10fb1b808b5a526dedc6fed1cf29807210386aa9372fbab374593466bc5451dc59954e90787f08060964d95c87ef34ca5bb5368ae", default_script);


        // Calculate pegged Bitcoin asset
        std::vector<unsigned char> commit = CommitToArguments(consensus, strNetworkID);
        uint256 entropy;
        GenerateAssetEntropy(entropy,  COutPoint(uint256(commit), 0), parentGenesisBlockHash);

        // Elements serialization uses derivation, bitcoin serialization uses 0x00
        if (g_con_elementsmode) {
            CalculateAsset(consensus.pegged_asset, entropy);
        } else {
            assert(consensus.pegged_asset == CAsset());
        }

        consensus.parent_pegged_asset.SetHex("0x00"); // No parent pegged asset
        initial_reissuance_tokens = 0;

        consensus.subsidy_asset = consensus.pegged_asset;

        // Legacy PAK list
        consensus.first_extension_space = {
            ParseHex("0362f0cf4898e44a20472664daed460156976bab5cc8bb8431b206bbafddd230c9"
                    "0399dadeeedc2cefe9042ffa596c553cad1967cda04de6aa0f9fbd96b6044292e7"),
            ParseHex("033fad80bd2b818d1ca8a8d4a25dafcf5e740be07db6788be1f2f15266e3c6805d"
                    "0253ff3f140ef8f594d54996eab810a82550c79204279920d95681afe699d00da5"),
            ParseHex("03f2d35e88741f930a3938bfa7075377ec2da4f1d7699a779e2cbf7a389195dc67"
                    "026132199a025299b5e0f4ab3f44294c81c5302f6d45ddda6316c18ae515793cf6"),
            ParseHex("036286d30d20ddcd3e867851936802dd8a2d84846c7e52aece0fc303c6deec9e04"
                    "02c7581da9d9ac0001e1c560c348b5df07d42de166d74eccd4c3bda467fe84f898"),
            ParseHex("0327b1884b3d743f4859db7c2df07e6e346d61d77fbc46c1da6db113fbbd43d7c5"
                    "0383c832ec502cf0990b199a4e46a45a63bfa6c6eb3f4b231472f144e684d6e9f8"),
            ParseHex("03075f118532928c7ef27a77644a12a87fbada3cd94cf67b2d2ae5cb169ddaefa4"
                    "02882c4fed938b20f3472af337cd7674a99f0aab0ae1803e27e978c52c417ce5e1"),
            ParseHex("02b988448e337c15cd6ac82b4737e3e2b5e92947da2f7fa96a81db7f9be3fabeb2"
                    "02f660c7675a1ed4893df838a5c4c07a287997cbd7dc5d884044b338ed606231bc"),
            ParseHex("0245b763999e3152418b9cd08b5f54c410a072d5e486826823791848e1bb879061"
                    "0259740ea12e953db0c5fd135c1a9564ce81a318729668811cf54f884c2f980eb8"),
            ParseHex("032f8814144351d5d05ca40c87cbbda67bb5f8b1920a38cf3bd008c1d266bb4682"
                    "039eb3a0b89656b338c3f4a9fc7bba582dd21935f59471c18e6b43c57e063053d9"),
            ParseHex("03d8b2ed1813370955cfb8dec24b7c5cb34b13fa4545d9e6d47d8c05af56a2c7d2"
                    "026392f13fefce606c60adadfe9e729e0af84f5f8cb6a35b76be244351635b38f7"),
            ParseHex("03e2a56e47f41eb83af34fb65c4dfb77ac442b01b5134fd92219bd3f4a999c7de5"
                    "034e93391cea816e5141dace7e5477bbed90c9daa0670b68b7acc8a44af556bbc1"),
            ParseHex("03156b39a4bce80e68c1582aa78f81f0252ccbb039766b5395ee9a0224f41c236d"
                    "0399a5d1d42f5b6cb587560394e1581eb0c76916db317c0d644a1b9f509a06c4e6"),
            ParseHex("029ce033e1dc81164deb04b4c55966b823a025ef47bb1f767017696b68ab9ae201"
                    "03e612d646e71b07e5ce0eaa3a0178e4606dd9a6e8f0d5ace9171fb1e808a3865b"),
            ParseHex("02a8300f0cff92b23e402459e83c52ec5824de82ee4004cf9d254e788304027ef6"
                    "0389cbda672fa9efea51706863f1d7ae5e5015b2e519003ef0178c99f71be6e8be"),
            ParseHex("03fcba7ecf41bc7e1be4ee122d9d22e3333671eb0a3a87b5cdf099d59874e1940f"
                    "02b0fb4fe4670c68329441e47acaaa954ff00e3fd547b9ff4e0fe547df2e775ec5"),
            ParseHex("0335f807a1bdc0906adda1a4166f9cdc2aa974a78b15fc29d79a8d7ca529a96008"
                    "02228dfd7ff95506dd67b1118803eb8ab49352b2e24cd5f38da043847e722009ba"),
            ParseHex("03fcc2963daaf8249bfd220e52c693626254b9295ac4f947ae2e0cddb3046724c1"
                    "02dac03530ac9712a71eafb87766644b61cf4be85d0fdc6a859875b41e7a1dc8e6"),
            ParseHex("039bfd22bf5c41ce14d3fbd50ef226d2066e826b2efba455150d23d958d52bfddf"
                    "03211678d22c45402c993d96ea4a6d861d3e1da33798aebd5424fe5725a7ce8f4b"),
            ParseHex("02d67fcb027c5d8fe354fb36235192cb4fffabffdcc6ce74be255fe869f62d8675"
                    "03d61d857b2a8cb060fd4b9a98a862f250df5825068665a3c8d93f2ac8a7085888"),
            ParseHex("02cfe983eb588975958e9ce832937ba7f24592882cf5c0fc0f07896097fd66a8e7"
                    "0344744d01c091eacea5730ed1205b0a83378418644ea7938ed664649e88dcbb29"),
            ParseHex("029ec6dd0c310513b3720800025a7ad9013d60a7fb041f6e9b9d3963485ba28657"
                    "0277247f28eb9481dd21d664093a2bc19a496c7ffebeca0026a1726a5041e671ba"),
            ParseHex("03f9dea372c4a667dcfe234ff8e0410c22341149ff7d8780c46954ff74998fbe44"
                    "0340c4e534906c06b73874cef00a880ab602641c7883de94296f0f601e6517ae7e"),
            ParseHex("03cf8520f2db93e1ba75fa9043ac7e3476719b2a33a12d7e725688a2de68852c88"
                    "0343b7551ba662fa7071ac93e7e25517967bb8a9420af64d35d41c6d88056ad4ba"),
            ParseHex("03f79461a5559f360c407069b92a8075958bf1f70918872d9dd702db145bccbd42"
                    "0395058fc702f126176ae13e0ebed05107288900a5a35b121f62923e58798b7b2f"),
            ParseHex("02d7f049d9e87c861fc9decfbe167cb13ccc87cce99113f69e3a5dca8bb71b6aed"
                    "03e82197b2e9cc0ee11a59808cfdb52e824445f8fa99e44dc9c30d1e49950ff9d6"),
            ParseHex("0281bfeffcc6841d1355dce039f5d64f72714a4c3adc4d351eaf3c28acbcee15f0"
                    "0270a16ee1cdfc78755a783efbdb66fe822605cc5f53af707e5038615e22b288e2"),
            ParseHex("025651f14b6347a000e15473eaf631fd78c9307e07db85e177e31fcde0b3f2a574"
                    "03d5303909fe1c6665cbc96a538b17274068c8e79757705f68db3df2b561a4c110"),
            ParseHex("03627a4855be1edc657927f30a4a869ad830041c1f0e74ab4670588af9532b8de8"
                    "03444cb85aef9fbba10b3e2662d533858db771010b57b7aedb1ecaa1c5a34918f1"),
            ParseHex("0286951fdc1e81652cdd10a10971966792e5c2a2bbe524f32a561f585b2b3d2057"
                    "034294862542484e49c6fb835919212352527298c689ff7be57e445bf0fe3536de"),
        };

        consensus.vDeployments[Consensus::DEPLOYMENT_TESTDUMMY].bit = 28;
        consensus.vDeployments[Consensus::DEPLOYMENT_TESTDUMMY].nStartTime = 0;
        consensus.vDeployments[Consensus::DEPLOYMENT_TESTDUMMY].nTimeout = Consensus::BIP9Deployment::NO_TIMEOUT;

        consensus.vDeployments[Consensus::DEPLOYMENT_TAPROOT].bit = 2;
        consensus.vDeployments[Consensus::DEPLOYMENT_TAPROOT].nStartTime = 1554500; // November 1, 2021
        consensus.vDeployments[Consensus::DEPLOYMENT_TAPROOT].nTimeout = Consensus::BIP9Deployment::NO_TIMEOUT;
        consensus.vDeployments[Consensus::DEPLOYMENT_TAPROOT].nPeriod = 10080; // one week...
        consensus.vDeployments[Consensus::DEPLOYMENT_TAPROOT].nThreshold = 10080; // ...of 100% signalling

        // Activated from block 1,000,000.
        consensus.vDeployments[Consensus::DEPLOYMENT_DYNA_FED].bit = 25;
        // Allow blocksigners to delay activation.
        consensus.vDeployments[Consensus::DEPLOYMENT_DYNA_FED].nStartTime = gArgs.GetArg("-con_dyna_deploy_start", 1000000);
        consensus.vDeployments[Consensus::DEPLOYMENT_DYNA_FED].nTimeout = Consensus::BIP9Deployment::NO_TIMEOUT;
        consensus.vDeployments[Consensus::DEPLOYMENT_DYNA_FED].min_activation_height = 0; // No activation delay


        // Finally, create genesis block
        genesis = CreateGenesisBlock(consensus, CScript() << commit, CScript(OP_RETURN), 1296688602, 2, 0x207fffff, 1, 0);
        consensus.hashGenesisBlock = genesis.GetHash();
        assert(consensus.hashGenesisBlock.GetHex() == "1466275836220db2944ca059a3a10ef6fd2ea684b0688d2c379296888a206003");
    }
};

/**
 * New: Liquid v1 testing, as close to prod as possible while still being customizable.
 */
class CLiquidV1TestParams : public CLiquidV1Params {
public:
    explicit CLiquidV1TestParams(const ArgsManager& args)
    {
        // Our goal here is to override ONLY the things from liquidv1 that make no sense for a test chain / which are pointless and burdensome to require people to override manually.

        strNetworkID = "liquidv1test";

        m_is_test_chain = true;
        m_is_mockable_chain = false;

        vSeeds.clear();  // No network seeds
        vFixedSeeds.clear();  // No network seeds

        // 51 means OP_TRUE, this can be overridden on the commandline
        std::vector<unsigned char> sign_bytes = ParseHex("51");
        consensus.signblockscript = CScript(sign_bytes.begin(), sign_bytes.end());

        // Do not mandate a specific destination for fees in testing
        consensus.mandatory_coinbase_destination = CScript(); // Blank script allows any coinbase destination

        // The bitcoin regtest genesis blockhash is the default, not the mainchain
        parentGenesisBlockHash = uint256S("0f9188f13cb7b2c71f2a335e3a4fc328bf5beb436012afca590b1a11466e2206");
        const bool parent_genesis_is_null = parentGenesisBlockHash == uint256();
        assert(consensus.has_parent_chain != parent_genesis_is_null);

        // This is the regtest limit, not the mainchain limit.
        consensus.parentChainPowLimit = uint256S("7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff");
        consensus.parent_chain_signblockscript = CScript(); // It has PoW

        // Default to 8, not 100, for expedited testing.
        consensus.pegin_min_depth = DEFAULT_PEGIN_CONFIRMATION_DEPTH;

        // Default fedpegscrit is OP_TRUE (tests should override it)
        consensus.fedpegScript = CScript() << OP_TRUE;

        // For testing purposes, default to the same junk keys that CustomParams uses (this can be overridden.)
        consensus.first_extension_space = {ParseHex("02fcba7ecf41bc7e1be4ee122d9d22e3333671eb0a3a87b5cdf099d59874e1940f02fcba7ecf41bc7e1be4ee122d9d22e3333671eb0a3a87b5cdf099d59874e1940f")};

        // Use all regtest rather than mainchain magic numbers:
        bech32_hrp = args.GetArg("-bech32_hrp", "ert");
        blech32_hrp = args.GetArg("-blech32_hrp", "el");
        base58Prefixes[PUBKEY_ADDRESS] = std::vector<unsigned char>(1, args.GetArg("-pubkeyprefix", 235));
        base58Prefixes[SCRIPT_ADDRESS] = std::vector<unsigned char>(1, args.GetArg("-scriptprefix", 75));
        base58Prefixes[BLINDED_ADDRESS] = std::vector<unsigned char>(1, args.GetArg("-blindedprefix", 4));
        base58Prefixes[SECRET_KEY] =     std::vector<unsigned char>(1, args.GetArg("-secretprefix", 239));
        base58Prefixes[PARENT_PUBKEY_ADDRESS] = std::vector<unsigned char>(1, args.GetArg("-parentpubkeyprefix", 111));
        base58Prefixes[PARENT_SCRIPT_ADDRESS] = std::vector<unsigned char>(1, args.GetArg("-parentscriptprefix", 196));
        parent_bech32_hrp = args.GetArg("-parent_bech32_hrp", "bcrt");
        parent_blech32_hrp = args.GetArg("-parent_blech32_hrp", "bcrt");

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
        // END magic numbers

        UpdateFromArgs(args);
        SetGenesisBlock();
        consensus.hashGenesisBlock = genesis.GetHash();
    }

    // As much as possible here, our goal is to:
    // - Allow overriding anything that can be overridden in CCustomParams;
    // - Leave everything alone unless an argument / config parameter was given.
    // This is unlike the CCustomParams UpdateFromArgs method, which has lots of defaults in it.
    void UpdateFromArgs(const ArgsManager& args)
    {
        // NOTE: We don't handle version bits, because I'm not sure we actually use them, and it would be messy to do so.
        // UpdateVersionBitsParametersFromArgs(args);

        consensus.nSubsidyHalvingInterval = args.GetArg("-con_nsubsidyhalvinginterval", consensus.nSubsidyHalvingInterval);
        if (args.IsArgSet("-con_bip16exception")) {
            consensus.BIP16Exception = uint256S(args.GetArg("-con_bip16exception", ""));
        }
        consensus.BIP34Height = args.GetArg("-con_bip34height", consensus.BIP34Height);
        if (args.IsArgSet("-con_bip34hash")) {
            consensus.BIP34Hash = uint256S(args.GetArg("-con_bip34hash", ""));
        }
        consensus.BIP65Height = args.GetArg("-con_bip65height", consensus.BIP65Height);
        consensus.BIP66Height = args.GetArg("-con_bip66height", consensus.BIP66Height);
        if (args.IsArgSet("-con_powlimit")) {
            consensus.powLimit = uint256S(args.GetArg("-con_powlimit", ""));
        }
        consensus.nPowTargetTimespan = args.GetArg("-con_npowtargettimespan", consensus.nPowTargetTimespan);
        consensus.nPowTargetSpacing = args.GetArg("-con_npowtargetspacing", consensus.nPowTargetSpacing);
        consensus.fPowAllowMinDifficultyBlocks = args.GetBoolArg("-con_fpowallowmindifficultyblocks", consensus.fPowAllowMinDifficultyBlocks);
        consensus.fPowNoRetargeting = args.GetBoolArg("-con_fpownoretargeting", consensus.fPowNoRetargeting);
        consensus.nRuleChangeActivationThreshold = (uint32_t)args.GetArg("-con_nrulechangeactivationthreshold", consensus.nRuleChangeActivationThreshold);
        consensus.nMinerConfirmationWindow = (uint32_t)args.GetArg("-con_nminerconfirmationwindow", consensus.nMinerConfirmationWindow);

        if (args.IsArgSet("-con_nminimumchainwork")) {
            consensus.nMinimumChainWork = uint256S(args.GetArg("-con_nminimumchainwork", ""));
        }
        if (args.IsArgSet("-con_defaultassumevalid")) {
            consensus.defaultAssumeValid = uint256S(args.GetArg("-con_defaultassumevalid", ""));
        }
        // TODO: Embed in genesis block in nTime field with new genesis block type
        consensus.dynamic_epoch_length = args.GetArg("-dynamic_epoch_length", consensus.dynamic_epoch_length);

        std::vector<std::string> pak_list_str = args.GetArgs("-pak");
        if (!pak_list_str.empty()) {
            consensus.first_extension_space.clear();
            for (const auto& entry : pak_list_str) {
                consensus.first_extension_space.push_back(ParseHex(entry));
            }
        }

        nPruneAfterHeight = (uint64_t)args.GetArg("-npruneafterheight", nPruneAfterHeight);
        fDefaultConsistencyChecks = args.GetBoolArg("-fdefaultconsistencychecks", fDefaultConsistencyChecks);
        m_is_test_chain = args.GetBoolArg("-fmineblocksondemand", m_is_test_chain);

        bech32_hrp = args.GetArg("-bech32_hrp", bech32_hrp);
        blech32_hrp = args.GetArg("-blech32_hrp", blech32_hrp);

        if (args.IsArgSet("-pubkeyprefix")) {
            base58Prefixes[PUBKEY_ADDRESS] = std::vector<unsigned char>(1, args.GetArg("-pubkeyprefix", 0));
        }
        if (args.IsArgSet("-scriptprefix")) {
            base58Prefixes[SCRIPT_ADDRESS] = std::vector<unsigned char>(1, args.GetArg("-scriptprefix", 0));
        }
        if (args.IsArgSet("-blindedprefix")) {
            base58Prefixes[BLINDED_ADDRESS] = std::vector<unsigned char>(1, args.GetArg("-blindedprefix", 0));
        }
        if (args.IsArgSet("-secretprefix")) {
            base58Prefixes[SECRET_KEY] = std::vector<unsigned char>(1, args.GetArg("-secretprefix", 0));
        }
        if (args.IsArgSet("-parentpubkeyprefix")) {
            base58Prefixes[PARENT_PUBKEY_ADDRESS] = std::vector<unsigned char>(1, args.GetArg("-parentpubkeyprefix", 0));
        }
        if (args.IsArgSet("-parentscriptprefix")) {
            base58Prefixes[PARENT_SCRIPT_ADDRESS] = std::vector<unsigned char>(1, args.GetArg("-parentscriptprefix", 0));
        }
        parent_bech32_hrp = args.GetArg("-parent_bech32_hrp", parent_bech32_hrp);
        parent_blech32_hrp = args.GetArg("-parent_blech32_hrp", parent_blech32_hrp);

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
        consensus.genesis_style = args.GetArg("-con_genesis_style", consensus.genesis_style);

        // Block signing encumberance script
        if (args.IsArgSet("-signblockscript")) {
            std::vector<unsigned char> sign_bytes = ParseHex(args.GetArg("-signblockscript", ""));
            consensus.signblockscript = CScript(sign_bytes.begin(), sign_bytes.end());
        }

        consensus.max_block_signature_size = args.GetArg("-con_max_block_sig_size", consensus.max_block_signature_size);
        g_signed_blocks = args.GetBoolArg("-con_signed_blocks", g_signed_blocks);

        // Note: These globals are needed to avoid circular dependencies.
        g_con_blockheightinheader = args.GetBoolArg("-con_blockheightinheader", g_con_blockheightinheader);

        // Doesn't make any sense to use this chain in !elementsmode. Don't do it.
        assert(args.GetBoolArg("-con_elementsmode", true));
        g_con_elementsmode = true;
        consensus.elements_mode = true;

        consensus.genesis_subsidy = args.GetArg("-con_blocksubsidy", consensus.genesis_subsidy);

        // All non-zero coinbase outputs must go to this scriptPubKey
        if (args.IsArgSet("-con_mandatorycoinbase")) {
            std::vector<unsigned char> man_bytes = ParseHex(args.GetArg("-con_mandatorycoinbase", ""));
            consensus.mandatory_coinbase_destination = CScript(man_bytes.begin(), man_bytes.end()); // Blank script allows any coinbase destination
        }

        consensus.connect_genesis_outputs = args.GetArg("-con_connect_genesis_outputs", consensus.connect_genesis_outputs);

        initialFreeCoins = args.GetArg("-initialfreecoins", initialFreeCoins);

        anyonecanspend_aremine = args.GetBoolArg("-anyonecanspendaremine", anyonecanspend_aremine);

        consensus.has_parent_chain = args.GetBoolArg("-con_has_parent_chain", consensus.has_parent_chain);

        enforce_pak = args.GetBoolArg("-enforce_pak", enforce_pak);

        multi_data_permitted = args.GetBoolArg("-multi_data_permitted", multi_data_permitted);

        if (args.IsArgSet("-parentgenesisblockhash")) {
            parentGenesisBlockHash = uint256S(args.GetArg("-parentgenesisblockhash", ""));
        }
        // Either it has a parent chain or not
        const bool parent_genesis_is_null = parentGenesisBlockHash == uint256();
        assert(consensus.has_parent_chain != parent_genesis_is_null);
        if (args.IsArgSet("-con_parentpowlimit")) {
            consensus.parentChainPowLimit = uint256S(args.GetArg("-con_parentpowlimit", ""));
        }

        if (args.IsArgSet("-con_parent_chain_signblockscript")) {
            consensus.parent_chain_signblockscript = StrHexToScriptWithDefault(args.GetArg("-con_parent_chain_signblockscript", ""), CScript());
        }
        consensus.pegin_min_depth = args.GetArg("-peginconfirmationdepth", consensus.pegin_min_depth);

        if (args.IsArgSet("-fedpegscript")) {
            consensus.fedpegScript = StrHexToScriptWithDefault(args.GetArg("-fedpegscript", ""), CScript());
        }

        consensus.total_valid_epochs = args.GetArg("-total_valid_epochs", consensus.total_valid_epochs);

        // Calculate pegged Bitcoin asset
        std::vector<unsigned char> commit = CommitToArguments(consensus, strNetworkID);
        uint256 entropy;
        GenerateAssetEntropy(entropy,  COutPoint(uint256(commit), 0), parentGenesisBlockHash);
        CalculateAsset(consensus.pegged_asset, entropy);

        if (args.IsArgSet("-con_parent_pegged_asset")) {
            consensus.parent_pegged_asset.SetHex(args.GetArg("-con_parent_pegged_asset", ""));
        }
        initial_reissuance_tokens = args.GetArg("-initialreissuancetokens", initial_reissuance_tokens);

        if (args.IsArgSet("-subsidyasset")) {
            consensus.subsidy_asset = CAsset(uint256S(args.GetArg("-subsidyasset", "")));
        }

        if (args.IsArgSet("-con_dyna_deploy_start")) {
            consensus.vDeployments[Consensus::DEPLOYMENT_DYNA_FED].bit = 25;
            consensus.vDeployments[Consensus::DEPLOYMENT_DYNA_FED].nStartTime = args.GetArg("-con_dyna_deploy_start", Consensus::BIP9Deployment::ALWAYS_ACTIVE);
            consensus.vDeployments[Consensus::DEPLOYMENT_DYNA_FED].nTimeout = Consensus::BIP9Deployment::NO_TIMEOUT;
            consensus.vDeployments[Consensus::DEPLOYMENT_DYNA_FED].min_activation_height = 0; // No activation delay
        }

        if (args.IsArgSet("-con_taproot_signal_start")) {
            consensus.vDeployments[Consensus::DEPLOYMENT_TAPROOT].nStartTime = gArgs.GetArg("-con_taproot_signal_start", 0);
        }

        // END ELEMENTS fields
    }

    // XXX: This is copy-and-pasted from CCustomParams; sharing it would be better, but is annoying.
    void SetGenesisBlock() {
        if (consensus.genesis_style == "bitcoin") {
            // For compatibility with bitcoin (regtest)
            genesis = CreateGenesisBlock(1296688602, 2, 0x207fffff, 1, 50 * COIN, consensus);
        } else if (consensus.genesis_style == "elements") {
            // Intended compatibility with Liquid v1 and elements-0.14.1
            std::vector<unsigned char> commit = CommitToArguments(consensus, strNetworkID);
            genesis = CreateGenesisBlock(consensus, CScript() << commit, CScript(OP_RETURN), 1296688602, 2, 0x207fffff, 1, 0);
            if (initialFreeCoins != 0 || initial_reissuance_tokens != 0) {
                AppendInitialIssuance(genesis, COutPoint(uint256(commit), 0), parentGenesisBlockHash, (initialFreeCoins > 0) ? 1 : 0, initialFreeCoins, (initial_reissuance_tokens > 0) ? 1 : 0, initial_reissuance_tokens, CScript() << OP_TRUE);
            }
        } else if (consensus.genesis_style == "dynamic") {
            // Liquid v2 HF, from genesis. Upgrading networks still use "elements".
            // TODO fill out genesis block with special commitments including epoch
            // length in nTime
            throw std::runtime_error(strprintf("Invalid -genesis_style (%s)", consensus.genesis_style));
        } else {
            throw std::runtime_error(strprintf("Invalid -genesis_style (%s)", consensus.genesis_style));
        }
    }
};


static std::unique_ptr<const CChainParams> globalChainParams;

const CChainParams &Params() {
    assert(globalChainParams);
    return *globalChainParams;
}

std::unique_ptr<const CChainParams> CreateChainParams(const ArgsManager& args, const std::string& chain)
{
    // Reserved names for non-custom chains
    if (chain == CBaseChainParams::MAIN) {
        return std::unique_ptr<CChainParams>(new CMainParams());
    } else if (chain == CBaseChainParams::TESTNET) {
        return std::unique_ptr<CChainParams>(new CTestNetParams());
    } else if (chain == CBaseChainParams::SIGNET) {
        return std::unique_ptr<CChainParams>(new SigNetParams(args));
    } else if (chain == CBaseChainParams::REGTEST) {
        return std::unique_ptr<CChainParams>(new CRegTestParams(args));
    } else if (chain == CBaseChainParams::LIQUID1) {
        return std::unique_ptr<CChainParams>(new CLiquidV1Params());
    } else if (chain == CBaseChainParams::LIQUID1TEST) {
        return std::unique_ptr<CChainParams>(new CLiquidV1TestParams(args));
    }

    return std::unique_ptr<CChainParams>(new CCustomParams(chain, args));
}

void SelectParams(const std::string& network)
{
    SelectBaseParams(network);
    globalChainParams = CreateChainParams(gArgs, network);
}
