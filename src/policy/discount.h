// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2021 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_POLICY_DISCOUNT_H
#define BITCOIN_POLICY_DISCOUNT_H

#include <consensus/consensus.h>
#include <cstdint>
#include <primitives/transaction.h>
#include <version.h>

/**
 * Calculate a smaller virtual size for discounted Confidential Transactions.
 */
static inline int64_t GetDiscountVirtualTransactionSize(const CTransaction& tx, int64_t nSigOpCost = 0, unsigned int bytes_per_sig_op = 0)
{
    int64_t size_bytes = ::GetSerializeSize(tx, PROTOCOL_VERSION | SERIALIZE_TRANSACTION_NO_WITNESS) * (WITNESS_SCALE_FACTOR - 1) + ::GetSerializeSize(tx, PROTOCOL_VERSION);
    int64_t sigop_bytes = nSigOpCost * bytes_per_sig_op;

    int64_t weight = std::max(size_bytes, sigop_bytes);

    // for each confidential output
    for (size_t i = 0; i < tx.vout.size(); ++i) {
        const CTxOut& output = tx.vout[i];
        if (i < tx.witness.vtxoutwit.size()) {
            // subtract the weight of the output witness, except the 2 bytes used to serialize the empty proofs
            size_t witness_size = ::GetSerializeSize(tx.witness.vtxoutwit[i], PROTOCOL_VERSION);
            assert(witness_size >= 2);
            weight -= (witness_size - 2);
        }
        if (output.nValue.IsCommitment()) {
            // subtract the weight difference of amount commitment (33) vs explicit amount (9)
            weight -= (33 - 9);
        }
        if (output.nNonce.IsCommitment()) {
            // subtract the weight difference of nonce commitment (33) vs no nonce (1)
            weight -= 32;
        }
    }
    assert(weight > 0);

    size_t discountvsize = (weight + WITNESS_SCALE_FACTOR - 1) / WITNESS_SCALE_FACTOR;

    assert(discountvsize > 0);
    return discountvsize;
}

#endif // BITCOIN_POLICY_DISCOUNT_H
