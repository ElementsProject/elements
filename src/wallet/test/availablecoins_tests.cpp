// Copyright (c) 2022 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or https://www.opensource.org/licenses/mit-license.php.

#include <validation.h>
#include <wallet/coincontrol.h>
#include <wallet/spend.h>
#include <wallet/test/util.h>
#include <wallet/test/wallet_test_fixture.h>

#include <boost/test/unit_test.hpp>

namespace wallet {
BOOST_FIXTURE_TEST_SUITE(availablecoins_tests, WalletTestingSetup)
class AvailableCoinsTestingSetup : public TestChain100Setup
{
public:
    AvailableCoinsTestingSetup()
    {
        CreateAndProcessBlock({}, {});
        wallet = CreateSyncedWallet(*m_node.chain, m_node.chainman->ActiveChain(), m_args, coinbaseKey);
    }

    ~AvailableCoinsTestingSetup()
    {
        wallet.reset();
    }
    CWalletTx& AddTx(CRecipient recipient)
    {
        CTransactionRef tx;
        CCoinControl dummy;
        {
            constexpr int RANDOM_CHANGE_POSITION = -1;
            auto res = CreateTransaction(*wallet, {recipient}, RANDOM_CHANGE_POSITION, dummy);
            BOOST_CHECK(res);
            tx = res.GetObj().tx;
        }
        wallet->CommitTransaction(tx, {}, {});
        CMutableTransaction blocktx;
        {
            LOCK(wallet->cs_wallet);
            blocktx = CMutableTransaction(*wallet->mapWallet.at(tx->GetHash()).tx);
        }
        CreateAndProcessBlock({CMutableTransaction(blocktx)}, GetScriptForRawPubKey(coinbaseKey.GetPubKey()));

        LOCK(wallet->cs_wallet);
        wallet->SetLastBlockProcessed(wallet->GetLastBlockHeight() + 1, m_node.chainman->ActiveChain().Tip()->GetBlockHash());
        auto it = wallet->mapWallet.find(tx->GetHash());
        BOOST_CHECK(it != wallet->mapWallet.end());
        it->second.m_state = TxStateConfirmed{m_node.chainman->ActiveChain().Tip()->GetBlockHash(), m_node.chainman->ActiveChain().Height(), /*index=*/1};
        return it->second;
    }

    std::unique_ptr<CWallet> wallet;
};

    // ELEMENTS FIXME: swapping these around so that bech32 is run first before bech32m
    // fixes an intermittent issue with the transaction failing to validate its own signature,
    // showing an "invalid schnorr signature" error.  this requires further investigation.
    // see https://github.com/ElementsProject/elements/issues/1370

BOOST_FIXTURE_TEST_CASE(BasicOutputTypesTestBech32m, AvailableCoinsTestingSetup)
{
    CoinsResult available_coins;
    BResult<CTxDestination> dest;
    LOCK(wallet->cs_wallet);

    // Verify our wallet has one usable coinbase UTXO before starting
    // This UTXO is a P2PK, so it should show up in the Other bucket
    available_coins = AvailableCoins(*wallet);
    BOOST_CHECK_EQUAL(available_coins.size(), 1U);
    BOOST_CHECK_EQUAL(available_coins.other.size(), 1U);

    // We will create a self transfer for each of the OutputTypes and
    // verify it is put in the correct bucket after running GetAvailablecoins
    //
    // For each OutputType, We expect 2 UTXOs in our wallet following the self transfer:
    //   1. One UTXO as the recipient
    //   2. One UTXO from the change, due to payment address matching logic


    // Bech32m
    dest = wallet->GetNewDestination(OutputType::BECH32M, "");
    BOOST_ASSERT(dest.HasRes());
    AddTx(CRecipient{{GetScriptForDestination(dest.GetObj())}, 1 * COIN, CAsset(), CPubKey(), /*fSubtractFeeFromAmount=*/true});
    available_coins = AvailableCoins(*wallet);
    BOOST_CHECK_EQUAL(available_coins.bech32m.size(), 2U);
}

BOOST_FIXTURE_TEST_CASE(BasicOutputTypesTestBech32, AvailableCoinsTestingSetup)
{
    CoinsResult available_coins;
    BResult<CTxDestination> dest;
    LOCK(wallet->cs_wallet);

    available_coins = AvailableCoins(*wallet);
    BOOST_CHECK_EQUAL(available_coins.size(), 1U);
    BOOST_CHECK_EQUAL(available_coins.other.size(), 1U);

    // Bech32
    dest = wallet->GetNewDestination(OutputType::BECH32, "");
    BOOST_ASSERT(dest.HasRes());
    AddTx(CRecipient{{GetScriptForDestination(dest.GetObj())}, 2 * COIN, CAsset(), CPubKey(), /*fSubtractFeeFromAmount=*/true});
    available_coins = AvailableCoins(*wallet);
    BOOST_CHECK_EQUAL(available_coins.bech32.size(), 2U);
}

BOOST_FIXTURE_TEST_CASE(BasicOutputTypesTestP2SHSegWit, AvailableCoinsTestingSetup)
{
    CoinsResult available_coins;
    BResult<CTxDestination> dest;
    LOCK(wallet->cs_wallet);

    available_coins = AvailableCoins(*wallet);
    BOOST_CHECK_EQUAL(available_coins.size(), 1U);
    BOOST_CHECK_EQUAL(available_coins.other.size(), 1U);

    // P2SH-SEGWIT
    dest = wallet->GetNewDestination(OutputType::P2SH_SEGWIT, "");
    AddTx(CRecipient{{GetScriptForDestination(dest.GetObj())}, 3 * COIN, CAsset(), CPubKey(), /*fSubtractFeeFromAmount=*/true});
    available_coins = AvailableCoins(*wallet);
    BOOST_CHECK_EQUAL(available_coins.P2SH_segwit.size(), 2U);
}


BOOST_FIXTURE_TEST_CASE(BasicOutputTypesTestLegacy, AvailableCoinsTestingSetup)
{
    CoinsResult available_coins;
    BResult<CTxDestination> dest;
    LOCK(wallet->cs_wallet);

    available_coins = AvailableCoins(*wallet);
    BOOST_CHECK_EQUAL(available_coins.size(), 1U);
    BOOST_CHECK_EQUAL(available_coins.other.size(), 1U);

    // Legacy (P2PKH)
    dest = wallet->GetNewDestination(OutputType::LEGACY, "");
    BOOST_ASSERT(dest.HasRes());
    AddTx(CRecipient{{GetScriptForDestination(dest.GetObj())}, 4 * COIN, CAsset(), CPubKey(), /*fSubtractFeeFromAmount=*/true});
    available_coins = AvailableCoins(*wallet);
    BOOST_CHECK_EQUAL(available_coins.legacy.size(), 2U);
}

BOOST_AUTO_TEST_SUITE_END()
} // namespace wallet
