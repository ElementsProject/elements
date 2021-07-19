// Copyright (c) 2021 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_WALLET_SPEND_H
#define BITCOIN_WALLET_SPEND_H

#include <wallet/coinselection.h>
#include <wallet/transaction.h>
#include <wallet/wallet.h>

class COutput
{
public:
    const CWalletTx *tx;

    /** Index in tx->vout. */
    int i;

    /**
     * Depth in block chain.
     * If > 0: the tx is on chain and has this many confirmations.
     * If = 0: the tx is waiting confirmation.
     * If < 0: a conflicting tx is on chain and has this many confirmations. */
    int nDepth;

    /** Pre-computed estimated size of this output as a fully-signed input in a transaction. Can be -1 if it could not be calculated */
    int nInputBytes;

    /** Whether we have the private keys to spend this output */
    bool fSpendable;

    /** Whether we know how to spend this output, ignoring the lack of keys */
    bool fSolvable;

    /** Whether to use the maximum sized, 72 byte signature when calculating the size of the input spend. This should only be set when watch-only outputs are allowed */
    bool use_max_sig;

    /**
     * Whether this output is considered safe to spend. Unconfirmed transactions
     * from outside keys and unconfirmed replacement transactions are considered
     * unsafe and will not be used to fund new spending transactions.
     */
    bool fSafe;

    COutput(const CWalletTx *txIn, int iIn, int nDepthIn, bool fSpendableIn, bool fSolvableIn, bool fSafeIn, bool use_max_sig_in = false)
    {
        tx = txIn; i = iIn; nDepth = nDepthIn; fSpendable = fSpendableIn; fSolvable = fSolvableIn; fSafe = fSafeIn; nInputBytes = -1; use_max_sig = use_max_sig_in;
        // If known and signable by the given wallet, compute nInputBytes
        // Failure will keep this value -1
        if (fSpendable && tx) {
            nInputBytes = tx->GetSpendSize(i, use_max_sig);
        }
    }

    std::string ToString() const;

    inline CInputCoin GetInputCoin() const
    {
        return CInputCoin(tx, i, nInputBytes);
    }
};

// ELEMENTS
struct IssuanceDetails {
    bool issuing = false;

    bool blind_issuance = true;
    CAsset reissuance_asset;
    CAsset reissuance_token;
    uint256 entropy;
};

struct BlindDetails {
    bool ignore_blind_failure = true; // Certain corner-cases are hard to avoid

    // Temporary tx-specific details.
    std::vector<uint256> i_amount_blinds;
    std::vector<uint256> i_asset_blinds;
    std::vector<CAsset>  i_assets;
    std::vector<CAmount> i_amounts;
    std::vector<CAmount> o_amounts;
    std::vector<CPubKey> o_pubkeys;
    std::vector<uint256> o_amount_blinds;
    std::vector<CAsset>  o_assets;
    std::vector<uint256> o_asset_blinds;

    int num_to_blind;
    int change_to_blind;
    // Only used to strip blinding if its the only blind output in certain situations
    int only_recipient_blind_index;
    // Needed in case of one blinded output that is change and no blind inputs
    int only_change_pos;
};

// end ELEMENTS

class WalletRescanReserver; //forward declarations for ScanForWalletTransactions/RescanFromTime
/**
 * A CWallet maintains a set of transactions and balances, and provides the ability to create new transactions.
 */

#endif // BITCOIN_WALLET_SPEND_H
