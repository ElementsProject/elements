// Copyright (c) 2011-2019 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_QT_WALLETMODELTRANSACTION_H
#define BITCOIN_QT_WALLETMODELTRANSACTION_H

#include <primitives/transaction.h>
#include <qt/sendcoinsrecipient.h>

#include <amount.h>

#include <QObject>

class SendAssetsRecipient;

namespace interfaces {
class Node;
}

/** Data model for a walletmodel transaction. */
class WalletModelTransaction
{
public:
    explicit WalletModelTransaction(const QList<SendAssetsRecipient> &recipients);

    QList<SendAssetsRecipient> getRecipients() const;

    CTransactionRef& getWtx();
    void setWtx(const CTransactionRef&);

    unsigned int getTransactionSize();

    void setTransactionFee(const CAmount& newFee);
    CAmount getTransactionFee() const;

    CAmountMap getTotalTransactionAmount() const;

    void reassignAmounts(const std::vector<CAmount>& out_amounts, int nChangePosRet); // needed for the subtract-fee-from-amount feature

private:
    QList<SendAssetsRecipient> recipients;
    CTransactionRef wtx;
    CAmount fee;
};

#endif // BITCOIN_QT_WALLETMODELTRANSACTION_H
