// Copyright (c) 2011-2018 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <qt/walletmodeltransaction.h>

#include <interfaces/node.h>
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

std::unique_ptr<interfaces::PendingWalletTx>& WalletModelTransaction::getWtx()
{
    return wtx;
}

unsigned int WalletModelTransaction::getTransactionSize()
{
    return wtx ? wtx->getVirtualSize() : 0;
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
    int i = 0;
    for (auto it = recipients.begin(); it != recipients.end(); ++it)
    {
        auto& rcp = (*it);

        if (rcp.paymentRequest.IsInitialized())
        {
            CAmount subtotal = 0;
            const payments::PaymentDetails& details = rcp.paymentRequest.getDetails();
            for (int j = 0; j < details.outputs_size(); j++)
            {
                const payments::Output& out = details.outputs(j);
                if (out.amount() <= 0) continue;
                if (i == nChangePosRet)
                    i++;
                subtotal += outAmounts[i];
                i++;
            }
            rcp.asset_amount = subtotal;
        }
        else // normal recipient (no payment request)
        {
            if (i == nChangePosRet)
                i++;
            rcp.asset_amount = outAmounts[i];
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
