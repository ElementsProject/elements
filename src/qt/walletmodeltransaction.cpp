// Copyright (c) 2011-2019 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifdef HAVE_CONFIG_H
#include <config/bitcoin-config.h>
#endif

#include <qt/walletmodeltransaction.h>

#include <policy/policy.h>

#define SendCoinsRecipient SendAssetsRecipient

WalletModelTransaction::WalletModelTransaction(const QList<SendCoinsRecipient> &_recipients) :
    recipients(_recipients),
    fee(0)
{
}

QList<SendCoinsRecipient> WalletModelTransaction::getRecipients() const
{
    return recipients;
}

CTransactionRef& WalletModelTransaction::getWtx()
{
    return wtx;
}

void WalletModelTransaction::setWtx(const CTransactionRef& newTx)
{
    wtx = newTx;
}

unsigned int WalletModelTransaction::getTransactionSize()
{
    return wtx ? GetVirtualTransactionSize(*wtx) : 0;
}

CAmount WalletModelTransaction::getTransactionFee() const
{
    return fee;
}

void WalletModelTransaction::setTransactionFee(const CAmount& newFee)
{
    fee = newFee;
}

void WalletModelTransaction::reassignAmounts(const std::vector<CAmount>& outAmounts, int nChangePosRet)
{
    const CTransaction* walletTransaction = wtx.get();
    int i = 0;
    for (auto it = recipients.begin(); it != recipients.end(); ++it)
    {
        auto& rcp = (*it);

        {
            if (i == nChangePosRet)
                i++;
            rcp.asset_amount = g_con_elementsmode ? outAmounts[i] : walletTransaction->vout[i].nValue.GetAmount();
            i++;
        }
    }
}

CAmountMap WalletModelTransaction::getTotalTransactionAmount() const
{
    CAmountMap totalTransactionAmount;
    for (const auto &rcp : recipients)
    {
        totalTransactionAmount[rcp.asset] += rcp.asset_amount;
    }
    return totalTransactionAmount;
}
