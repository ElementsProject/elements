// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2021 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_CHAINPARAMS_H
#define BITCOIN_CHAINPARAMS_H

#include <chainparamsbase.h>
#include <consensus/params.h>
#include <netaddress.h>
#include <primitives/block.h>
#include <protocol.h>
#include <util/hash_type.h>

#include <memory>
#include <string>
#include <vector>

typedef std::map<int, uint256> MapCheckpoints;

struct CCheckpointData {
    MapCheckpoints mapCheckpoints;

    int GetHeight() const {
        const auto& final_checkpoint = mapCheckpoints.rbegin();
        return final_checkpoint == mapCheckpoints.rend() ? 0 : final_checkpoint->first /* height */;
    }
};

struct AssumeutxoHash : public BaseHash<uint256> {
    explicit AssumeutxoHash(const uint256& hash) : BaseHash(hash) {}
};

/**
 * Holds configuration for use during UTXO snapshot load and validation. The contents
 * here are security critical, since they dictate which UTXO snapshots are recognized
 * as valid.
 */
struct AssumeutxoData {
    //! The expected hash of the deserialized UTXO set.
    const AssumeutxoHash hash_serialized;

    //! Used to populate the nChainTx value, which is used during BlockManager::LoadBlockIndex().
    //!
    //! We need to hardcode the value here because this is computed cumulatively using block data,
    //! which we do not necessarily have at the time of snapshot load.
    const unsigned int nChainTx;
};

using MapAssumeutxo = std::map<int, const AssumeutxoData>;

/**
 * Holds various statistics on transactions within a chain. Used to estimate
 * verification progress during chain sync.
 *
 * See also: CChainParams::TxData, GuessVerificationProgress.
 */
struct ChainTxData {
    int64_t nTime;    //!< UNIX timestamp of last known number of transactions
    int64_t nTxCount; //!< total number of transactions between genesis and that timestamp
    double dTxRate;   //!< estimated number of transactions per second after that timestamp
};

/**
 * CChainParams defines various tweakable parameters of a given instance of the
 * Bitcoin system.
 */
class CChainParams
{
public:
    enum Base58Type {
        PUBKEY_ADDRESS,
        SCRIPT_ADDRESS,
        SECRET_KEY,
        EXT_PUBLIC_KEY,
        EXT_SECRET_KEY,
        // ELEMENTS
        BLINDED_ADDRESS,
        PARENT_PUBKEY_ADDRESS,
        PARENT_SCRIPT_ADDRESS,

        MAX_BASE58_TYPES
    };

    const Consensus::Params& GetConsensus() const { return consensus; }
    const CMessageHeader::MessageStartChars& MessageStart() const { return pchMessageStart; }
    uint16_t GetDefaultPort() const { return nDefaultPort; }
    uint16_t GetDefaultPort(Network net) const
    {
        return net == NET_I2P ? I2P_SAM31_PORT : GetDefaultPort();
    }
    uint16_t GetDefaultPort(const std::string& addr) const
    {
        CNetAddr a;
        return a.SetSpecial(addr) ? GetDefaultPort(a.GetNetwork()) : GetDefaultPort();
    }

    const CBlock& GenesisBlock() const { return genesis; }
    /** Default value for -checkmempool and -checkblockindex argument */
    bool DefaultConsistencyChecks() const { return fDefaultConsistencyChecks; }
    /** Policy: Filter transactions that do not match well-defined patterns */
    bool RequireStandard() const { return fRequireStandard; }
    /** If this chain is exclusively used for testing */
    bool IsTestChain() const { return m_is_test_chain; }
    /** If this chain allows time to be mocked */
    bool IsMockableChain() const { return m_is_mockable_chain; }
    uint64_t PruneAfterHeight() const { return nPruneAfterHeight; }
    /** Minimum free space (in GB) needed for data directory */
    uint64_t AssumedBlockchainSize() const { return m_assumed_blockchain_size; }
    /** Minimum free space (in GB) needed for data directory when pruned; Does not include prune target*/
    uint64_t AssumedChainStateSize() const { return m_assumed_chain_state_size; }
    /** Whether it is possible to mine blocks on demand (no retargeting) */
    bool MineBlocksOnDemand() const { return consensus.fPowNoRetargeting; }
    /** Return the network string */
    std::string NetworkIDString() const { return strNetworkID; }
    /** Return the list of hostnames to look up for DNS seeds */
    const std::vector<std::string>& DNSSeeds() const { return vSeeds; }
    const std::vector<unsigned char>& Base58Prefix(Base58Type type) const { return base58Prefixes[type]; }
    const std::string& Bech32HRP() const { return bech32_hrp; }
    const std::string& Blech32HRP() const { return blech32_hrp; }
    const std::vector<uint8_t>& FixedSeeds() const { return vFixedSeeds; }
    const CCheckpointData& Checkpoints() const { return checkpointData; }

    //! Get allowed assumeutxo configuration.
    //! @see ChainstateManager
    const MapAssumeutxo& Assumeutxo() const { return m_assumeutxo_data; }

    const ChainTxData& TxData() const { return chainTxData; }
    // ELEMENTS extra fields:
    const uint256& ParentGenesisBlockHash() const { return parentGenesisBlockHash; }
    const uint256& HashGenesisBlock() const { return consensus.hashGenesisBlock; }
    bool anyonecanspend_aremine;
    const std::string& ParentBech32HRP() const { return parent_bech32_hrp; }
    const std::string& ParentBlech32HRP() const { return parent_blech32_hrp; }
    bool GetEnforcePak() const { return enforce_pak; }
    bool GetMultiDataPermitted() const { return multi_data_permitted; }
    bool GetAcceptDiscountCT() const { return accept_discount_ct; }
    bool GetCreateDiscountCT() const { return create_discount_ct; }

protected:
    CChainParams() {}

    Consensus::Params consensus;
    CMessageHeader::MessageStartChars pchMessageStart;
    uint16_t nDefaultPort;
    uint64_t nPruneAfterHeight;
    uint64_t m_assumed_blockchain_size;
    uint64_t m_assumed_chain_state_size;
    std::vector<std::string> vSeeds;
    std::vector<unsigned char> base58Prefixes[MAX_BASE58_TYPES];
    std::string bech32_hrp;
    std::string blech32_hrp;
    std::string strNetworkID;
    CBlock genesis;
    CAmount initialFreeCoins;
    CAmount initial_reissuance_tokens;
    std::vector<uint8_t> vFixedSeeds;
    bool fDefaultConsistencyChecks;
    bool fRequireStandard;
    bool m_is_test_chain;
    bool m_is_mockable_chain;
    CCheckpointData checkpointData;
    MapAssumeutxo m_assumeutxo_data;
    ChainTxData chainTxData;
    // ELEMENTS extra fields:
    uint256 parentGenesisBlockHash;
    std::string parent_bech32_hrp;
    std::string parent_blech32_hrp;
    bool enforce_pak;
    bool multi_data_permitted;
    bool accept_discount_ct;
    bool create_discount_ct;
};

/**
 * Creates and returns a std::unique_ptr<CChainParams> of the chosen chain.
 * @returns a CChainParams* of the chosen chain.
 * @throws a std::runtime_error if the chain is not supported.
 */
std::unique_ptr<const CChainParams> CreateChainParams(const ArgsManager& args, const std::string& chain);

/**
 * Return the currently selected parameters. This won't change after app
 * startup, except for unit tests.
 */
const CChainParams &Params();

/**
 * Sets the params returned by Params() to those for the given chain name.
 * @throws std::runtime_error when the chain is not supported.
 */
void SelectParams(const std::string& chain);

#endif // BITCOIN_CHAINPARAMS_H
