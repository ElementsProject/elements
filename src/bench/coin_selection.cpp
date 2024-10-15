// Copyright (c) 2012-2021 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <bench/bench.h>
#include <interfaces/chain.h>
#include <node/context.h>
#include <wallet/coinselection.h>
#include <asset.h>
#include <policy/policy.h>
#include <wallet/spend.h>
#include <wallet/wallet.h>

#include <set>

using node::NodeContext;
using wallet::AttemptSelection;
using wallet::CHANGE_LOWER;
using wallet::COutput;
using wallet::CWallet;
using wallet::CWalletTx;
using wallet::CoinEligibilityFilter;
using wallet::CoinSelectionParams;
using wallet::CreateDummyWalletDatabase;
using wallet::OutputGroup;
using wallet::SelectCoinsBnB;
using wallet::TxStateInactive;

static void addCoin(const CAmount& nValue, const CWallet& wallet, std::vector<std::unique_ptr<CWalletTx>>& wtxs)
{
    static int nextLockTime = 0;
    CMutableTransaction tx;
    tx.nLockTime = nextLockTime++; // so all transactions get different hashes
    tx.vout.resize(1);
    tx.vout[0].nValue = nValue;
    wtxs.push_back(std::make_unique<CWalletTx>(MakeTransactionRef(std::move(tx)), TxStateInactive{}));
}

// Simple benchmark for wallet coin selection. Note that it maybe be necessary
// to build up more complicated scenarios in order to get meaningful
// measurements of performance. From laanwj, "Wallet coin selection is probably
// the hardest, as you need a wider selection of scenarios, just testing the
// same one over and over isn't too useful. Generating random isn't useful
// either for measurements."
// (https://github.com/bitcoin/bitcoin/issues/7883#issuecomment-224807484)
static void CoinSelection(benchmark::Bench& bench)
{
    NodeContext node;
    auto chain = interfaces::MakeChain(node);
    CWallet wallet(chain.get(), "", gArgs, CreateDummyWalletDatabase());
    std::vector<std::unique_ptr<CWalletTx>> wtxs;
    LOCK(wallet.cs_wallet);

    // Add coins.
    for (int i = 0; i < 1000; ++i) {
        addCoin(1000 * COIN, wallet, wtxs);
    }
    addCoin(3 * COIN, wallet, wtxs);

    // Create coins
    std::vector<COutput> coins;
    for (const auto& wtx : wtxs) {
        const auto txout = wtx->tx->vout.at(0);
        coins.emplace_back(COutPoint(wtx->GetHash(), 0), txout, /*depth=*/6 * 24, CalculateMaximumSignedInputSize(txout, &wallet, /*coin_control=*/nullptr), /*spendable=*/true, /*solvable=*/true, /*safe=*/true, wtx->GetTxTime(), /*from_me=*/true, /*fees=*/ 0);
    }

    const CoinEligibilityFilter filter_standard(1, 6, 0);
    FastRandomContext rand{};
    const CoinSelectionParams coin_selection_params{
        rand,
        /*change_output_size=*/ 34,
        /*change_spend_size=*/ 148,
        /*min_change_target=*/ CHANGE_LOWER,
        /*effective_feerate=*/ CFeeRate(0),
        /*long_term_feerate=*/ CFeeRate(0),
        /*discard_feerate=*/ CFeeRate(0),
        /*tx_noinputs_size=*/ 0,
        /*avoid_partial=*/ false,
    };
    bench.run([&] {
        CAmountMap mapValue;
        mapValue[::policyAsset] = 1003 * COIN;
        auto result = AttemptSelection(wallet, mapValue, filter_standard, coins, coin_selection_params);
        assert(result);
        assert(result->GetSelectedValue() == mapValue);
        assert(result->GetInputSet().size() == 2);

/*        std::set<std::pair<const CWalletTx*, unsigned int> > setCoinsRet;
        CAmountMap nValueRet;
        CAmountMap mapValue;
        mapValue[CAsset()] = 1003 * COIN;
        bool success = wallet.SelectCoinsMinConf(mapValue, 1, 6, 0, vCoins, setCoinsRet, nValueRet);
        assert(success);
        assert(nValueRet[CAsset()] == 1003 * COIN);
        assert(setCoinsRet.size() == 2);*/
    });
}

static NodeContext testNode;
static auto testChain = interfaces::MakeChain(testNode);
static CWallet testWallet(testChain.get(), "", gArgs, CreateDummyWalletDatabase());

// Copied from src/wallet/test/coinselector_tests.cpp
static void add_coin(const CAmount& nValue, int nInput, std::vector<OutputGroup>& set)
{
    CMutableTransaction tx;
    tx.vout.resize(nInput + 1);
    tx.vout[nInput].nValue = nValue;
    CWalletTx wtx(MakeTransactionRef(tx), TxStateInactive{});
    COutput output(COutPoint(wtx.GetHash(), nInput), wtx.tx->vout.at(nInput), /*depth=*/ 0, /*input_bytes=*/ -1, /*spendable=*/ true, /*solvable=*/ true, /*safe=*/ true, /*time=*/ 0, /*from_me=*/ true, /*fees=*/ 0);
    set.emplace_back();
    set.back().Insert(output, /*ancestors=*/ 0, /*descendants=*/ 0, /*positive_only=*/ false);
}
// Copied from src/wallet/test/coinselector_tests.cpp
static CAmount make_hard_case(int utxos, std::vector<OutputGroup>& utxo_pool)
{
    utxo_pool.clear();
    CAmount target = 0;
    for (int i = 0; i < utxos; ++i) {
        target += (CAmount)1 << (utxos+i);
        add_coin((CAmount)1 << (utxos+i), 2*i, utxo_pool);
        add_coin(((CAmount)1 << (utxos+i)) + ((CAmount)1 << (utxos-1-i)), 2*i + 1, utxo_pool);
    }
    return target;
}

static void BnBExhaustion(benchmark::Bench& bench)
{
    // Setup
    std::vector<OutputGroup> utxo_pool;

    bench.run([&] {
        // Benchmark
        CAmount target = make_hard_case(17, utxo_pool);
        SelectCoinsBnB(utxo_pool, target, 0); // Should exhaust

        // Cleanup
        utxo_pool.clear();
    });
}

BENCHMARK(CoinSelection);
BENCHMARK(BnBExhaustion);
