// Copyright (c) 2015-2018 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_CORE_MEMUSAGE_H
#define BITCOIN_CORE_MEMUSAGE_H

#include <primitives/transaction.h>
#include <primitives/block.h>
#include <memusage.h>

static inline size_t RecursiveDynamicUsage(const CScript& script) {
    return memusage::DynamicUsage(script);
}

static inline size_t RecursiveDynamicUsage(const COutPoint& out) {
    return 0;
}

static inline size_t RecursiveDynamicUsage(const CTxIn& in) {
    size_t mem = RecursiveDynamicUsage(in.scriptSig) + RecursiveDynamicUsage(in.prevout);
    return mem;
}

static inline size_t RecursiveDynamicUsage(const CScriptWitness& scriptWit) {
    size_t mem = memusage::DynamicUsage(scriptWit.stack);
    for (std::vector<std::vector<unsigned char> >::const_iterator it = scriptWit.stack.begin(); it != scriptWit.stack.end(); it++) {
        mem += memusage::DynamicUsage(*it);
    }
    return mem;
}

static inline size_t RecursiveDynamicUsage(const CTxInWitness& txInWit) {
    size_t mem = RecursiveDynamicUsage(txInWit.scriptWitness);
    mem += RecursiveDynamicUsage(txInWit.m_pegin_witness);
    return mem;
}

static inline size_t RecursiveDynamicUsage(const CTxOutWitness& txOutWit) {
    size_t mem = memusage::DynamicUsage(txOutWit.vchRangeproof);
    mem += memusage::DynamicUsage(txOutWit.vchSurjectionproof);
    return mem;
}

static inline size_t RecursiveDynamicUsage(const CTxWitness& wit) {
    size_t mem = memusage::DynamicUsage(wit.vtxinwit) + memusage::DynamicUsage(wit.vtxoutwit);
    for (const auto& txInWit: wit.vtxinwit) {
        mem += RecursiveDynamicUsage(txInWit);
    }
    for (const auto& txOutWit: wit.vtxoutwit) {
        mem += RecursiveDynamicUsage(txOutWit);
    }
    return mem;
}

static inline size_t RecursiveDynamicUsage(const CTxOut& out) {
    return RecursiveDynamicUsage(out.scriptPubKey);
}

static inline size_t RecursiveDynamicUsage(const CTransaction& tx) {
    size_t mem = memusage::DynamicUsage(tx.vin) + memusage::DynamicUsage(tx.vout);
    for (std::vector<CTxIn>::const_iterator it = tx.vin.begin(); it != tx.vin.end(); it++) {
        mem += RecursiveDynamicUsage(*it);
    }
    for (std::vector<CTxOut>::const_iterator it = tx.vout.begin(); it != tx.vout.end(); it++) {
        mem += RecursiveDynamicUsage(*it);
    }
    return mem;
}

static inline size_t RecursiveDynamicUsage(const CMutableTransaction& tx) {
    size_t mem = memusage::DynamicUsage(tx.vin) + memusage::DynamicUsage(tx.vout);
    for (std::vector<CTxIn>::const_iterator it = tx.vin.begin(); it != tx.vin.end(); it++) {
        mem += RecursiveDynamicUsage(*it);
    }
    for (std::vector<CTxOut>::const_iterator it = tx.vout.begin(); it != tx.vout.end(); it++) {
        mem += RecursiveDynamicUsage(*it);
    }
    return mem;
}

static inline size_t RecursiveDynamicUsage(const CBlock& block) {
    size_t mem = memusage::DynamicUsage(block.vtx);
    for (const auto& tx : block.vtx) {
        mem += memusage::DynamicUsage(tx) + RecursiveDynamicUsage(*tx);
    }
    return mem;
}

static inline size_t RecursiveDynamicUsage(const CBlockLocator& locator) {
    return memusage::DynamicUsage(locator.vHave);
}

template<typename X>
static inline size_t RecursiveDynamicUsage(const std::shared_ptr<X>& p) {
    return p ? memusage::DynamicUsage(p) + RecursiveDynamicUsage(*p) : 0;
}

#endif // BITCOIN_CORE_MEMUSAGE_H
