// Copyright (c) 2021 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <wallet/test/util.h>

#include <chain.h>
#include <key.h>
#include <key_io.h>
#include <test/util/setup_common.h>
#include <wallet/wallet.h>
#include <wallet/walletdb.h>

#include <boost/test/unit_test.hpp>

#include <memory>

namespace wallet {
std::unique_ptr<CWallet> CreateSyncedWallet(interfaces::Chain& chain, CChain& cchain, ArgsManager& args, const CKey& key)
{
    auto wallet = std::make_unique<CWallet>(&chain, "", args, CreateMockWalletDatabase());
    {
        LOCK2(wallet->cs_wallet, ::cs_main);
        wallet->SetLastBlockProcessed(cchain.Height(), cchain.Tip()->GetBlockHash());
    }
    wallet->LoadWallet();
    {
        LOCK(wallet->cs_wallet);
        wallet->SetWalletFlag(WALLET_FLAG_DESCRIPTORS);
        wallet->SetupDescriptorScriptPubKeyMans();

        FlatSigningProvider provider;
        std::string error;
        std::unique_ptr<Descriptor> desc = Parse("combo(" + EncodeSecret(key) + ")", provider, error, /* require_checksum=*/ false);
        assert(desc);
        WalletDescriptor w_desc(std::move(desc), 0, 0, 1, 1);
        if (!wallet->AddWalletDescriptor(w_desc, provider, "", false)) assert(false);
    }
    WalletRescanReserver reserver(*wallet);
    reserver.reserve();
    CWallet::ScanResult result = wallet->ScanForWalletTransactions(cchain.Genesis()->GetBlockHash(), /*start_height=*/0, /*max_height=*/{}, reserver, /*fUpdate=*/false, /*save_progress=*/false);
    BOOST_CHECK_EQUAL(result.status, CWallet::ScanResult::SUCCESS);
    BOOST_CHECK_EQUAL(result.last_scanned_block, cchain.Tip()->GetBlockHash());
    BOOST_CHECK_EQUAL(*result.last_scanned_height, cchain.Height());
    BOOST_CHECK(result.last_failed_block.IsNull());
    return wallet;
}
} // namespace wallet
