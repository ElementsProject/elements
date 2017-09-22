// Copyright (c) 2015-2016 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_CORE_MEMUSAGE_H
#define BITCOIN_CORE_MEMUSAGE_H

#include "primitives/transaction.h"
#include "primitives/block.h"
#include "memusage.h"

static inline size_t RecursiveDynamicUsage(const CScript& script) {
    return memusage::DynamicUsage(*static_cast<const CScriptBase*>(&script));
}

static inline size_t RecursiveDynamicUsage(const COutPoint& out) {
    return 0;
}

static inline size_t RecursiveDynamicUsage(const CTxIn& in) {
    size_t mem = RecursiveDynamicUsage(in.scriptSig) + RecursiveDynamicUsage(in.prevout);
    return mem;
}

static inline size_t RecursiveDynamicUsage(const CTxOut& out) {
    return RecursiveDynamicUsage(out.scriptPubKey);
}

static inline size_t RecursiveDynamicUsage(const ::CTxInWitness& wit) {
    return memusage::DynamicUsage(wit.vchIssuanceAmountRangeproof)
        + memusage::DynamicUsage(wit.vchInflationKeysRangeproof);
}

static inline size_t RecursiveDynamicUsage(const ::CTxOutWitness& wit) {
    return memusage::DynamicUsage(wit.vchSurjectionproof)
        + memusage::DynamicUsage(wit.vchRangeproof);
}

static inline size_t RecursiveDynamicUsage(const ::CTxWitness& wit) {
    size_t mem = memusage::DynamicUsage(wit.vtxinwit)
        + memusage::DynamicUsage(wit.vtxoutwit);
    for (const CTxInWitness& w : wit.vtxinwit) {
        mem += RecursiveDynamicUsage(w);
    }
    for (const CTxOutWitness& w : wit.vtxoutwit) {
        mem += RecursiveDynamicUsage(w);
    }
    return mem;
}

static inline size_t RecursiveDynamicUsage(const CTransaction& tx) {
    size_t mem = memusage::DynamicUsage(tx.vin) + memusage::DynamicUsage(tx.vout);
    for (const CTxIn& txi : tx.vin) {
        mem += RecursiveDynamicUsage(txi);
    }
    for (const CTxOut& txo : tx.vout) {
        mem += RecursiveDynamicUsage(txo);
    }
    mem += RecursiveDynamicUsage(tx.wit);
    return mem;
}

static inline size_t RecursiveDynamicUsage(const CMutableTransaction& tx) {
    size_t mem = memusage::DynamicUsage(tx.vin) + memusage::DynamicUsage(tx.vout);
    for (const CTxIn& txi : tx.vin) {
        mem += RecursiveDynamicUsage(txi);
    }
    for (const CTxOut& txo : tx.vout) {
        mem += RecursiveDynamicUsage(txo);
    }
    mem += RecursiveDynamicUsage(tx.wit);
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

#endif // BITCOIN_CORE_MEMUSAGE_H
