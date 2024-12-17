// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2021 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <wallet/wallet.h>

#include <blindpsbt.h>
#include <chain.h>
#include <consensus/amount.h>
#include <consensus/consensus.h>
#include <consensus/validation.h>
#include <external_signer.h>
#include <fs.h>
#include <interfaces/chain.h>
#include <interfaces/wallet.h>
#include <key.h>
#include <key_io.h>
#include <outputtype.h>
#include <pegins.h>
#include <policy/fees.h>
#include <policy/policy.h>
#include <primitives/block.h>
#include <primitives/transaction.h>
#include <psbt.h>
#include <script/descriptor.h>
#include <script/pegins.h>
#include <script/script.h>
#include <script/signingprovider.h>
#include <txmempool.h>
#include <util/bip32.h>
#include <util/check.h>
#include <util/error.h>
#include <util/fees.h>
#include <util/moneystr.h>
#include <util/rbf.h>
#include <util/string.h>
#include <util/translation.h>
#include <validation.h>
#include <wallet/coincontrol.h>
#include <wallet/context.h>
#include <wallet/fees.h>
#include <wallet/external_signer_scriptpubkeyman.h>

#include <univalue.h>

#include <algorithm>
#include <assert.h>
#include <optional>

#include <boost/algorithm/string/replace.hpp>

#include <blind.h>
#include <issuance.h>
#include <crypto/hmac_sha256.h>
#include <random.h>

using interfaces::FoundBlock;

namespace wallet {
isminetype InputIsMine(const CWallet& wallet, const COutPoint& txin); // ELEMENTS: forward declaration to remove circular dep on receive.h
const std::map<uint64_t,std::string> WALLET_FLAG_CAVEATS{
    {WALLET_FLAG_AVOID_REUSE,
        "You need to rescan the blockchain in order to correctly mark used "
        "destinations in the past. Until this is done, some destinations may "
        "be considered unused, even if the opposite is the case."
    },
};

bool AddWalletSetting(interfaces::Chain& chain, const std::string& wallet_name)
{
    util::SettingsValue setting_value = chain.getRwSetting("wallet");
    if (!setting_value.isArray()) setting_value.setArray();
    for (const util::SettingsValue& value : setting_value.getValues()) {
        if (value.isStr() && value.get_str() == wallet_name) return true;
    }
    setting_value.push_back(wallet_name);
    return chain.updateRwSetting("wallet", setting_value);
}

bool RemoveWalletSetting(interfaces::Chain& chain, const std::string& wallet_name)
{
    util::SettingsValue setting_value = chain.getRwSetting("wallet");
    if (!setting_value.isArray()) return true;
    util::SettingsValue new_value(util::SettingsValue::VARR);
    for (const util::SettingsValue& value : setting_value.getValues()) {
        if (!value.isStr() || value.get_str() != wallet_name) new_value.push_back(value);
    }
    if (new_value.size() == setting_value.size()) return true;
    return chain.updateRwSetting("wallet", new_value);
}

static void UpdateWalletSetting(interfaces::Chain& chain,
                                const std::string& wallet_name,
                                std::optional<bool> load_on_startup,
                                std::vector<bilingual_str>& warnings)
{
    if (!load_on_startup) return;
    if (load_on_startup.value() && !AddWalletSetting(chain, wallet_name)) {
        warnings.emplace_back(Untranslated("Wallet load on startup setting could not be updated, so wallet may not be loaded next node startup."));
    } else if (!load_on_startup.value() && !RemoveWalletSetting(chain, wallet_name)) {
        warnings.emplace_back(Untranslated("Wallet load on startup setting could not be updated, so wallet may still be loaded next node startup."));
    }
}

/**
 * Refresh mempool status so the wallet is in an internally consistent state and
 * immediately knows the transaction's status: Whether it can be considered
 * trusted and is eligible to be abandoned ...
 */
static void RefreshMempoolStatus(CWalletTx& tx, interfaces::Chain& chain)
{
    if (chain.isInMempool(tx.GetHash())) {
        tx.m_state = TxStateInMempool();
    } else if (tx.state<TxStateInMempool>()) {
        tx.m_state = TxStateInactive();
    }
}

bool AddWallet(WalletContext& context, const std::shared_ptr<CWallet>& wallet)
{
    LOCK(context.wallets_mutex);
    assert(wallet);
    std::vector<std::shared_ptr<CWallet>>::const_iterator i = std::find(context.wallets.begin(), context.wallets.end(), wallet);
    if (i != context.wallets.end()) return false;
    context.wallets.push_back(wallet);
    wallet->ConnectScriptPubKeyManNotifiers();
    wallet->NotifyCanGetAddressesChanged();
    return true;
}

bool RemoveWallet(WalletContext& context, const std::shared_ptr<CWallet>& wallet, std::optional<bool> load_on_start, std::vector<bilingual_str>& warnings)
{
    assert(wallet);

    interfaces::Chain& chain = wallet->chain();
    std::string name = wallet->GetName();

    // Unregister with the validation interface which also drops shared ponters.
    wallet->m_chain_notifications_handler.reset();
    LOCK(context.wallets_mutex);
    std::vector<std::shared_ptr<CWallet>>::iterator i = std::find(context.wallets.begin(), context.wallets.end(), wallet);
    if (i == context.wallets.end()) return false;
    context.wallets.erase(i);

    // Write the wallet setting
    UpdateWalletSetting(chain, name, load_on_start, warnings);

    return true;
}

bool RemoveWallet(WalletContext& context, const std::shared_ptr<CWallet>& wallet, std::optional<bool> load_on_start)
{
    std::vector<bilingual_str> warnings;
    return RemoveWallet(context, wallet, load_on_start, warnings);
}

std::vector<std::shared_ptr<CWallet>> GetWallets(WalletContext& context)
{
    LOCK(context.wallets_mutex);
    return context.wallets;
}

std::shared_ptr<CWallet> GetWallet(WalletContext& context, const std::string& name)
{
    LOCK(context.wallets_mutex);
    for (const std::shared_ptr<CWallet>& wallet : context.wallets) {
        if (wallet->GetName() == name) return wallet;
    }
    return nullptr;
}

std::unique_ptr<interfaces::Handler> HandleLoadWallet(WalletContext& context, LoadWalletFn load_wallet)
{
    LOCK(context.wallets_mutex);
    auto it = context.wallet_load_fns.emplace(context.wallet_load_fns.end(), std::move(load_wallet));
    return interfaces::MakeHandler([&context, it] { LOCK(context.wallets_mutex); context.wallet_load_fns.erase(it); });
}

void NotifyWalletLoaded(WalletContext& context, const std::shared_ptr<CWallet>& wallet)
{
    LOCK(context.wallets_mutex);
    for (auto& load_wallet : context.wallet_load_fns) {
        load_wallet(interfaces::MakeWallet(context, wallet));
    }
}

static Mutex g_loading_wallet_mutex;
static Mutex g_wallet_release_mutex;
static std::condition_variable g_wallet_release_cv;
static std::set<std::string> g_loading_wallet_set GUARDED_BY(g_loading_wallet_mutex);
static std::set<std::string> g_unloading_wallet_set GUARDED_BY(g_wallet_release_mutex);

// Custom deleter for shared_ptr<CWallet>.
static void ReleaseWallet(CWallet* wallet)
{
    const std::string name = wallet->GetName();
    wallet->WalletLogPrintf("Releasing wallet\n");
    wallet->Flush();
    delete wallet;
    // Wallet is now released, notify UnloadWallet, if any.
    {
        LOCK(g_wallet_release_mutex);
        if (g_unloading_wallet_set.erase(name) == 0) {
            // UnloadWallet was not called for this wallet, all done.
            return;
        }
    }
    g_wallet_release_cv.notify_all();
}

void UnloadWallet(std::shared_ptr<CWallet>&& wallet)
{
    // Mark wallet for unloading.
    const std::string name = wallet->GetName();
    {
        LOCK(g_wallet_release_mutex);
        auto it = g_unloading_wallet_set.insert(name);
        assert(it.second);
    }
    // The wallet can be in use so it's not possible to explicitly unload here.
    // Notify the unload intent so that all remaining shared pointers are
    // released.
    wallet->NotifyUnload();

    // Time to ditch our shared_ptr and wait for ReleaseWallet call.
    wallet.reset();
    {
        WAIT_LOCK(g_wallet_release_mutex, lock);
        while (g_unloading_wallet_set.count(name) == 1) {
            g_wallet_release_cv.wait(lock);
        }
    }
}

namespace {
std::shared_ptr<CWallet> LoadWalletInternal(WalletContext& context, const std::string& name, std::optional<bool> load_on_start, const DatabaseOptions& options, DatabaseStatus& status, bilingual_str& error, std::vector<bilingual_str>& warnings)
{
    try {
        std::unique_ptr<WalletDatabase> database = MakeWalletDatabase(name, options, status, error);
        if (!database) {
            error = Untranslated("Wallet file verification failed.") + Untranslated(" ") + error;
            return nullptr;
        }

        context.chain->initMessage(_("Loading wallet…").translated);
        const std::shared_ptr<CWallet> wallet = CWallet::Create(context, name, std::move(database), options.create_flags, error, warnings);
        if (!wallet) {
            error = Untranslated("Wallet loading failed.") + Untranslated(" ") + error;
            status = DatabaseStatus::FAILED_LOAD;
            return nullptr;
        }

        NotifyWalletLoaded(context, wallet);
        AddWallet(context, wallet);
        wallet->postInitProcess();

        // Write the wallet setting
        UpdateWalletSetting(*context.chain, name, load_on_start, warnings);

        return wallet;
    } catch (const std::runtime_error& e) {
        error = Untranslated(e.what());
        status = DatabaseStatus::FAILED_LOAD;
        return nullptr;
    }
}
} // namespace

std::shared_ptr<CWallet> LoadWallet(WalletContext& context, const std::string& name, std::optional<bool> load_on_start, const DatabaseOptions& options, DatabaseStatus& status, bilingual_str& error, std::vector<bilingual_str>& warnings)
{
    auto result = WITH_LOCK(g_loading_wallet_mutex, return g_loading_wallet_set.insert(name));
    if (!result.second) {
        error = Untranslated("Wallet already loading.");
        status = DatabaseStatus::FAILED_LOAD;
        return nullptr;
    }
    auto wallet = LoadWalletInternal(context, name, load_on_start, options, status, error, warnings);
    WITH_LOCK(g_loading_wallet_mutex, g_loading_wallet_set.erase(result.first));
    return wallet;
}

std::shared_ptr<CWallet> CreateWallet(WalletContext& context, const std::string& name, std::optional<bool> load_on_start, DatabaseOptions& options, DatabaseStatus& status, bilingual_str& error, std::vector<bilingual_str>& warnings)
{
    uint64_t wallet_creation_flags = options.create_flags;
    const SecureString& passphrase = options.create_passphrase;

    if (wallet_creation_flags & WALLET_FLAG_DESCRIPTORS) options.require_format = DatabaseFormat::SQLITE;

    // Indicate that the wallet is actually supposed to be blank and not just blank to make it encrypted
    bool create_blank = (wallet_creation_flags & WALLET_FLAG_BLANK_WALLET);

    // Born encrypted wallets need to be created blank first.
    if (!passphrase.empty()) {
        wallet_creation_flags |= WALLET_FLAG_BLANK_WALLET;
    }

    // Private keys must be disabled for an external signer wallet
    if ((wallet_creation_flags & WALLET_FLAG_EXTERNAL_SIGNER) && !(wallet_creation_flags & WALLET_FLAG_DISABLE_PRIVATE_KEYS)) {
        error = Untranslated("Private keys must be disabled when using an external signer");
        status = DatabaseStatus::FAILED_CREATE;
        return nullptr;
    }

    // Descriptor support must be enabled for an external signer wallet
    if ((wallet_creation_flags & WALLET_FLAG_EXTERNAL_SIGNER) && !(wallet_creation_flags & WALLET_FLAG_DESCRIPTORS)) {
        error = Untranslated("Descriptor support must be enabled when using an external signer");
        status = DatabaseStatus::FAILED_CREATE;
        return nullptr;
    }

    // Wallet::Verify will check if we're trying to create a wallet with a duplicate name.
    std::unique_ptr<WalletDatabase> database = MakeWalletDatabase(name, options, status, error);
    if (!database) {
        error = Untranslated("Wallet file verification failed.") + Untranslated(" ") + error;
        status = DatabaseStatus::FAILED_VERIFY;
        return nullptr;
    }

    // Do not allow a passphrase when private keys are disabled
    if (!passphrase.empty() && (wallet_creation_flags & WALLET_FLAG_DISABLE_PRIVATE_KEYS)) {
        error = Untranslated("Passphrase provided but private keys are disabled. A passphrase is only used to encrypt private keys, so cannot be used for wallets with private keys disabled.");
        status = DatabaseStatus::FAILED_CREATE;
        return nullptr;
    }

    // Make the wallet
    context.chain->initMessage(_("Loading wallet…").translated);
    const std::shared_ptr<CWallet> wallet = CWallet::Create(context, name, std::move(database), wallet_creation_flags, error, warnings);
    if (!wallet) {
        error = Untranslated("Wallet creation failed.") + Untranslated(" ") + error;
        status = DatabaseStatus::FAILED_CREATE;
        return nullptr;
    }

    // Encrypt the wallet
    if (!passphrase.empty() && !(wallet_creation_flags & WALLET_FLAG_DISABLE_PRIVATE_KEYS)) {
        if (!wallet->EncryptWallet(passphrase)) {
            error = Untranslated("Error: Wallet created but failed to encrypt.");
            status = DatabaseStatus::FAILED_ENCRYPT;
            return nullptr;
        }
        if (!create_blank) {
            // Unlock the wallet
            if (!wallet->Unlock(passphrase)) {
                error = Untranslated("Error: Wallet was encrypted but could not be unlocked");
                status = DatabaseStatus::FAILED_ENCRYPT;
                return nullptr;
            }

            // Set a seed for the wallet
            {
                LOCK(wallet->cs_wallet);
                if (wallet->IsWalletFlagSet(WALLET_FLAG_DESCRIPTORS)) {
                    wallet->SetupDescriptorScriptPubKeyMans();
                } else {
                    for (auto spk_man : wallet->GetActiveScriptPubKeyMans()) {
                        if (!spk_man->SetupGeneration()) {
                            error = Untranslated("Unable to generate initial keys");
                            status = DatabaseStatus::FAILED_CREATE;
                            return nullptr;
                        }
                    }
                }
            }

            // Relock the wallet
            wallet->Lock();
        }
    }

    NotifyWalletLoaded(context, wallet);
    AddWallet(context, wallet);
    wallet->postInitProcess();

    // Write the wallet settings
    UpdateWalletSetting(*context.chain, name, load_on_start, warnings);

    status = DatabaseStatus::SUCCESS;
    return wallet;
}

std::shared_ptr<CWallet> RestoreWallet(WalletContext& context, const fs::path& backup_file, const std::string& wallet_name, std::optional<bool> load_on_start, DatabaseStatus& status, bilingual_str& error, std::vector<bilingual_str>& warnings)
{
    DatabaseOptions options;
    options.require_existing = true;

    if (!fs::exists(backup_file)) {
        error = Untranslated("Backup file does not exist");
        status = DatabaseStatus::FAILED_INVALID_BACKUP_FILE;
        return nullptr;
    }

    const fs::path wallet_path = fsbridge::AbsPathJoin(GetWalletDir(), fs::u8path(wallet_name));

    if (fs::exists(wallet_path) || !TryCreateDirectories(wallet_path)) {
        error = Untranslated(strprintf("Failed to create database path '%s'. Database already exists.", fs::PathToString(wallet_path)));
        status = DatabaseStatus::FAILED_ALREADY_EXISTS;
        return nullptr;
    }

    auto wallet_file = wallet_path / "wallet.dat";
    fs::copy_file(backup_file, wallet_file, fs::copy_options::none);

    auto wallet = LoadWallet(context, wallet_name, load_on_start, options, status, error, warnings);

    if (!wallet) {
        fs::remove(wallet_file);
        fs::remove(wallet_path);
    }

    return wallet;
}

/** @defgroup mapWallet
 *
 * @{
 */

const CWalletTx* CWallet::GetWalletTx(const uint256& hash) const
{
    AssertLockHeld(cs_wallet);
    std::map<uint256, CWalletTx>::const_iterator it = mapWallet.find(hash);
    if (it == mapWallet.end())
        return nullptr;
    return &(it->second);
}

void CWallet::UpgradeKeyMetadata()
{
    if (IsLocked() || IsWalletFlagSet(WALLET_FLAG_KEY_ORIGIN_METADATA)) {
        return;
    }

    auto spk_man = GetLegacyScriptPubKeyMan();
    if (!spk_man) {
        return;
    }

    spk_man->UpgradeKeyMetadata();
    SetWalletFlag(WALLET_FLAG_KEY_ORIGIN_METADATA);
}

void CWallet::UpgradeDescriptorCache()
{
    if (!IsWalletFlagSet(WALLET_FLAG_DESCRIPTORS) || IsLocked() || IsWalletFlagSet(WALLET_FLAG_LAST_HARDENED_XPUB_CACHED)) {
        return;
    }

    for (ScriptPubKeyMan* spkm : GetAllScriptPubKeyMans()) {
        DescriptorScriptPubKeyMan* desc_spkm = dynamic_cast<DescriptorScriptPubKeyMan*>(spkm);
        desc_spkm->UpgradeDescriptorCache();
    }
    SetWalletFlag(WALLET_FLAG_LAST_HARDENED_XPUB_CACHED);
}

bool CWallet::Unlock(const SecureString& strWalletPassphrase, bool accept_no_keys)
{
    CCrypter crypter;
    CKeyingMaterial _vMasterKey;

    {
        LOCK(cs_wallet);
        for (const MasterKeyMap::value_type& pMasterKey : mapMasterKeys)
        {
            if(!crypter.SetKeyFromPassphrase(strWalletPassphrase, pMasterKey.second.vchSalt, pMasterKey.second.nDeriveIterations, pMasterKey.second.nDerivationMethod))
                return false;
            if (!crypter.Decrypt(pMasterKey.second.vchCryptedKey, _vMasterKey))
                continue; // try another master key
            if (Unlock(_vMasterKey, accept_no_keys)) {
                // Now that we've unlocked, upgrade the key metadata
                UpgradeKeyMetadata();
                // Now that we've unlocked, upgrade the descriptor cache
                UpgradeDescriptorCache();
                return true;
            }
        }
    }
    return false;
}

bool CWallet::ChangeWalletPassphrase(const SecureString& strOldWalletPassphrase, const SecureString& strNewWalletPassphrase)
{
    bool fWasLocked = IsLocked();

    {
        LOCK(cs_wallet);
        Lock();

        CCrypter crypter;
        CKeyingMaterial _vMasterKey;
        for (MasterKeyMap::value_type& pMasterKey : mapMasterKeys)
        {
            if(!crypter.SetKeyFromPassphrase(strOldWalletPassphrase, pMasterKey.second.vchSalt, pMasterKey.second.nDeriveIterations, pMasterKey.second.nDerivationMethod))
                return false;
            if (!crypter.Decrypt(pMasterKey.second.vchCryptedKey, _vMasterKey))
                return false;
            if (Unlock(_vMasterKey))
            {
                int64_t nStartTime = GetTimeMillis();
                crypter.SetKeyFromPassphrase(strNewWalletPassphrase, pMasterKey.second.vchSalt, pMasterKey.second.nDeriveIterations, pMasterKey.second.nDerivationMethod);
                pMasterKey.second.nDeriveIterations = static_cast<unsigned int>(pMasterKey.second.nDeriveIterations * (100 / ((double)(GetTimeMillis() - nStartTime))));

                nStartTime = GetTimeMillis();
                crypter.SetKeyFromPassphrase(strNewWalletPassphrase, pMasterKey.second.vchSalt, pMasterKey.second.nDeriveIterations, pMasterKey.second.nDerivationMethod);
                pMasterKey.second.nDeriveIterations = (pMasterKey.second.nDeriveIterations + static_cast<unsigned int>(pMasterKey.second.nDeriveIterations * 100 / ((double)(GetTimeMillis() - nStartTime)))) / 2;

                if (pMasterKey.second.nDeriveIterations < 25000)
                    pMasterKey.second.nDeriveIterations = 25000;

                WalletLogPrintf("Wallet passphrase changed to an nDeriveIterations of %i\n", pMasterKey.second.nDeriveIterations);

                if (!crypter.SetKeyFromPassphrase(strNewWalletPassphrase, pMasterKey.second.vchSalt, pMasterKey.second.nDeriveIterations, pMasterKey.second.nDerivationMethod))
                    return false;
                if (!crypter.Encrypt(_vMasterKey, pMasterKey.second.vchCryptedKey))
                    return false;
                WalletBatch(GetDatabase()).WriteMasterKey(pMasterKey.first, pMasterKey.second);
                if (fWasLocked)
                    Lock();
                return true;
            }
        }
    }

    return false;
}

void CWallet::chainStateFlushed(const CBlockLocator& loc)
{
    WalletBatch batch(GetDatabase());
    batch.WriteBestBlock(loc);
}

void CWallet::SetMinVersion(enum WalletFeature nVersion, WalletBatch* batch_in)
{
    LOCK(cs_wallet);
    if (nWalletVersion >= nVersion)
        return;
    nWalletVersion = nVersion;

    {
        WalletBatch* batch = batch_in ? batch_in : new WalletBatch(GetDatabase());
        if (nWalletVersion > 40000)
            batch->WriteMinVersion(nWalletVersion);
        if (!batch_in)
            delete batch;
    }
}

std::set<uint256> CWallet::GetConflicts(const uint256& txid) const
{
    std::set<uint256> result;
    AssertLockHeld(cs_wallet);

    std::map<uint256, CWalletTx>::const_iterator it = mapWallet.find(txid);
    if (it == mapWallet.end())
        return result;
    const CWalletTx& wtx = it->second;

    std::pair<TxSpends::const_iterator, TxSpends::const_iterator> range;

    for (const CTxIn& txin : wtx.tx->vin)
    {
        if (mapTxSpends.count(txin.prevout) <= 1)
            continue;  // No conflict if zero or one spends
        range = mapTxSpends.equal_range(txin.prevout);
        for (TxSpends::const_iterator _it = range.first; _it != range.second; ++_it)
            result.insert(_it->second);
    }
    return result;
}

bool CWallet::HasWalletSpend(const uint256& txid) const
{
    AssertLockHeld(cs_wallet);
    auto iter = mapTxSpends.lower_bound(COutPoint(txid, 0));
    return (iter != mapTxSpends.end() && iter->first.hash == txid);
}

void CWallet::Flush()
{
    GetDatabase().Flush();
}

void CWallet::Close()
{
    GetDatabase().Close();
}

void CWallet::SyncMetaData(std::pair<TxSpends::iterator, TxSpends::iterator> range)
{
    // We want all the wallet transactions in range to have the same metadata as
    // the oldest (smallest nOrderPos).
    // So: find smallest nOrderPos:

    int nMinOrderPos = std::numeric_limits<int>::max();
    const CWalletTx* copyFrom = nullptr;
    for (TxSpends::iterator it = range.first; it != range.second; ++it) {
        const CWalletTx* wtx = &mapWallet.at(it->second);
        if (wtx->nOrderPos < nMinOrderPos) {
            nMinOrderPos = wtx->nOrderPos;
            copyFrom = wtx;
        }
    }

    if (!copyFrom) {
        return;
    }

    // Now copy data from copyFrom to rest:
    for (TxSpends::iterator it = range.first; it != range.second; ++it)
    {
        const uint256& hash = it->second;
        CWalletTx* copyTo = &mapWallet.at(hash);
        if (copyFrom == copyTo) continue;
        assert(copyFrom && "Oldest wallet transaction in range assumed to have been found.");
        if (!copyFrom->IsEquivalentTo(*copyTo)) continue;
        copyTo->mapValue = copyFrom->mapValue;
        copyTo->vOrderForm = copyFrom->vOrderForm;
        // fTimeReceivedIsTxTime not copied on purpose
        // nTimeReceived not copied on purpose
        copyTo->nTimeSmart = copyFrom->nTimeSmart;
        copyTo->fFromMe = copyFrom->fFromMe;
        // nOrderPos not copied on purpose
        // cached members not copied on purpose
    }
}

/**
 * Outpoint is spent if any non-conflicted transaction
 * spends it:
 */
bool CWallet::IsSpent(const uint256& hash, unsigned int n) const
{
    const COutPoint outpoint(hash, n);
    std::pair<TxSpends::const_iterator, TxSpends::const_iterator> range;
    range = mapTxSpends.equal_range(outpoint);

    for (TxSpends::const_iterator it = range.first; it != range.second; ++it)
    {
        const uint256& wtxid = it->second;
        std::map<uint256, CWalletTx>::const_iterator mit = mapWallet.find(wtxid);
        if (mit != mapWallet.end()) {
            int depth = GetTxDepthInMainChain(mit->second);
            if (depth > 0  || (depth == 0 && !mit->second.isAbandoned()))
                return true; // Spent
        }
    }
    return false;
}

void CWallet::AddToSpends(const COutPoint& outpoint, const uint256& wtxid, WalletBatch* batch)
{
    mapTxSpends.insert(std::make_pair(outpoint, wtxid));

    if (batch) {
        UnlockCoin(outpoint, batch);
    } else {
        WalletBatch temp_batch(GetDatabase());
        UnlockCoin(outpoint, &temp_batch);
    }

    std::pair<TxSpends::iterator, TxSpends::iterator> range;
    range = mapTxSpends.equal_range(outpoint);
    SyncMetaData(range);
}


void CWallet::AddToSpends(const uint256& wtxid, WalletBatch* batch)
{
    auto it = mapWallet.find(wtxid);
    assert(it != mapWallet.end());
    const CWalletTx& thisTx = it->second;
    if (thisTx.IsCoinBase()) // Coinbases don't spend anything!
        return;

    for (const CTxIn& txin : thisTx.tx->vin)
        AddToSpends(txin.prevout, wtxid, batch);
}

bool CWallet::EncryptWallet(const SecureString& strWalletPassphrase)
{
    if (IsCrypted())
        return false;

    CKeyingMaterial _vMasterKey;

    _vMasterKey.resize(WALLET_CRYPTO_KEY_SIZE);
    GetStrongRandBytes(_vMasterKey.data(), WALLET_CRYPTO_KEY_SIZE);

    CMasterKey kMasterKey;

    kMasterKey.vchSalt.resize(WALLET_CRYPTO_SALT_SIZE);
    GetStrongRandBytes(kMasterKey.vchSalt.data(), WALLET_CRYPTO_SALT_SIZE);

    CCrypter crypter;
    int64_t nStartTime = GetTimeMillis();
    crypter.SetKeyFromPassphrase(strWalletPassphrase, kMasterKey.vchSalt, 25000, kMasterKey.nDerivationMethod);
    kMasterKey.nDeriveIterations = static_cast<unsigned int>(2500000 / ((double)(GetTimeMillis() - nStartTime)));

    nStartTime = GetTimeMillis();
    crypter.SetKeyFromPassphrase(strWalletPassphrase, kMasterKey.vchSalt, kMasterKey.nDeriveIterations, kMasterKey.nDerivationMethod);
    kMasterKey.nDeriveIterations = (kMasterKey.nDeriveIterations + static_cast<unsigned int>(kMasterKey.nDeriveIterations * 100 / ((double)(GetTimeMillis() - nStartTime)))) / 2;

    if (kMasterKey.nDeriveIterations < 25000)
        kMasterKey.nDeriveIterations = 25000;

    WalletLogPrintf("Encrypting Wallet with an nDeriveIterations of %i\n", kMasterKey.nDeriveIterations);

    if (!crypter.SetKeyFromPassphrase(strWalletPassphrase, kMasterKey.vchSalt, kMasterKey.nDeriveIterations, kMasterKey.nDerivationMethod))
        return false;
    if (!crypter.Encrypt(_vMasterKey, kMasterKey.vchCryptedKey))
        return false;

    {
        LOCK(cs_wallet);
        mapMasterKeys[++nMasterKeyMaxID] = kMasterKey;
        WalletBatch* encrypted_batch = new WalletBatch(GetDatabase());
        if (!encrypted_batch->TxnBegin()) {
            delete encrypted_batch;
            encrypted_batch = nullptr;
            return false;
        }
        encrypted_batch->WriteMasterKey(nMasterKeyMaxID, kMasterKey);

        for (const auto& spk_man_pair : m_spk_managers) {
            auto spk_man = spk_man_pair.second.get();
            if (!spk_man->Encrypt(_vMasterKey, encrypted_batch)) {
                encrypted_batch->TxnAbort();
                delete encrypted_batch;
                encrypted_batch = nullptr;
                // We now probably have half of our keys encrypted in memory, and half not...
                // die and let the user reload the unencrypted wallet.
                assert(false);
            }
        }

        // Encryption was introduced in version 0.4.0
        SetMinVersion(FEATURE_WALLETCRYPT, encrypted_batch);

        if (!encrypted_batch->TxnCommit()) {
            delete encrypted_batch;
            encrypted_batch = nullptr;
            // We now have keys encrypted in memory, but not on disk...
            // die to avoid confusion and let the user reload the unencrypted wallet.
            assert(false);
        }

        delete encrypted_batch;
        encrypted_batch = nullptr;

        Lock();
        Unlock(strWalletPassphrase);

        // If we are using descriptors, make new descriptors with a new seed
        if (IsWalletFlagSet(WALLET_FLAG_DESCRIPTORS) && !IsWalletFlagSet(WALLET_FLAG_BLANK_WALLET)) {
            SetupDescriptorScriptPubKeyMans();
        } else if (auto spk_man = GetLegacyScriptPubKeyMan()) {
            // if we are using HD, replace the HD seed with a new one
            if (spk_man->IsHDEnabled()) {
                if (!spk_man->SetupGeneration(true)) {
                    return false;
                }
            }
        }
        Lock();

        // Need to completely rewrite the wallet file; if we don't, bdb might keep
        // bits of the unencrypted private key in slack space in the database file.
        GetDatabase().Rewrite();

        // BDB seems to have a bad habit of writing old data into
        // slack space in .dat files; that is bad if the old data is
        // unencrypted private keys. So:
        GetDatabase().ReloadDbEnv();

    }
    NotifyStatusChanged(this);

    return true;
}

DBErrors CWallet::ReorderTransactions()
{
    LOCK(cs_wallet);
    WalletBatch batch(GetDatabase());

    // Old wallets didn't have any defined order for transactions
    // Probably a bad idea to change the output of this

    // First: get all CWalletTx into a sorted-by-time multimap.
    typedef std::multimap<int64_t, CWalletTx*> TxItems;
    TxItems txByTime;

    for (auto& entry : mapWallet)
    {
        CWalletTx* wtx = &entry.second;
        txByTime.insert(std::make_pair(wtx->nTimeReceived, wtx));
    }

    nOrderPosNext = 0;
    std::vector<int64_t> nOrderPosOffsets;
    for (TxItems::iterator it = txByTime.begin(); it != txByTime.end(); ++it)
    {
        CWalletTx *const pwtx = (*it).second;
        int64_t& nOrderPos = pwtx->nOrderPos;

        if (nOrderPos == -1)
        {
            nOrderPos = nOrderPosNext++;
            nOrderPosOffsets.push_back(nOrderPos);

            if (!batch.WriteTx(*pwtx))
                return DBErrors::LOAD_FAIL;
        }
        else
        {
            int64_t nOrderPosOff = 0;
            for (const int64_t& nOffsetStart : nOrderPosOffsets)
            {
                if (nOrderPos >= nOffsetStart)
                    ++nOrderPosOff;
            }
            nOrderPos += nOrderPosOff;
            nOrderPosNext = std::max(nOrderPosNext, nOrderPos + 1);

            if (!nOrderPosOff)
                continue;

            // Since we're changing the order, write it back
            if (!batch.WriteTx(*pwtx))
                return DBErrors::LOAD_FAIL;
        }
    }
    batch.WriteOrderPosNext(nOrderPosNext);

    return DBErrors::LOAD_OK;
}

int64_t CWallet::IncOrderPosNext(WalletBatch* batch)
{
    AssertLockHeld(cs_wallet);
    int64_t nRet = nOrderPosNext++;
    if (batch) {
        batch->WriteOrderPosNext(nOrderPosNext);
    } else {
        WalletBatch(GetDatabase()).WriteOrderPosNext(nOrderPosNext);
    }
    return nRet;
}

void CWallet::MarkDirty()
{
    {
        LOCK(cs_wallet);
        for (std::pair<const uint256, CWalletTx>& item : mapWallet)
            item.second.MarkDirty(*this);
    }
}

bool CWallet::MarkReplaced(const uint256& originalHash, const uint256& newHash)
{
    LOCK(cs_wallet);

    auto mi = mapWallet.find(originalHash);

    // There is a bug if MarkReplaced is not called on an existing wallet transaction.
    assert(mi != mapWallet.end());

    CWalletTx& wtx = (*mi).second;

    // Ensure for now that we're not overwriting data
    assert(wtx.mapValue.count("replaced_by_txid") == 0);

    wtx.mapValue["replaced_by_txid"] = newHash.ToString();

    // Refresh mempool status without waiting for transactionRemovedFromMempool
    RefreshMempoolStatus(wtx, chain());

    WalletBatch batch(GetDatabase());

    bool success = true;
    if (!batch.WriteTx(wtx)) {
        WalletLogPrintf("%s: Updating batch tx %s failed\n", __func__, wtx.GetHash().ToString());
        success = false;
    }

    NotifyTransactionChanged(originalHash, CT_UPDATED);

    return success;
}

void CWallet::SetSpentKeyState(WalletBatch& batch, const uint256& hash, unsigned int n, bool used, std::set<CTxDestination>& tx_destinations)
{
    AssertLockHeld(cs_wallet);
    const CWalletTx* srctx = GetWalletTx(hash);
    if (!srctx) return;

    CTxDestination dst;
    if (ExtractDestination(srctx->tx->vout[n].scriptPubKey, dst)) {
        if (IsMine(dst)) {
            if (used != IsAddressUsed(dst)) {
                if (used) {
                    tx_destinations.insert(dst);
                }
                SetAddressUsed(batch, dst, used);
            }
        }
    }
}

bool CWallet::IsSpentKey(const uint256& hash, unsigned int n) const
{
    AssertLockHeld(cs_wallet);
    const CWalletTx* srctx = GetWalletTx(hash);
    if (srctx) {
        assert(srctx->tx->vout.size() > n);
        CTxDestination dest;
        if (!ExtractDestination(srctx->tx->vout[n].scriptPubKey, dest)) {
            return false;
        }
        if (IsAddressUsed(dest)) {
            return true;
        }
        if (IsLegacy()) {
            LegacyScriptPubKeyMan* spk_man = GetLegacyScriptPubKeyMan();
            assert(spk_man != nullptr);
            for (const auto& keyid : GetAffectedKeys(srctx->tx->vout[n].scriptPubKey, *spk_man)) {
                WitnessV0KeyHash wpkh_dest(keyid);
                if (IsAddressUsed(wpkh_dest)) {
                    return true;
                }
                ScriptHash sh_wpkh_dest(GetScriptForDestination(wpkh_dest));
                if (IsAddressUsed(sh_wpkh_dest)) {
                    return true;
                }
                PKHash pkh_dest(keyid);
                if (IsAddressUsed(pkh_dest)) {
                    return true;
                }
            }
        }
    }
    return false;
}

CWalletTx* CWallet::AddToWallet(CTransactionRef tx, const TxState& state, const UpdateWalletTxFn& update_wtx, bool fFlushOnClose, bool rescanning_old_block)
{
    LOCK(cs_wallet);

    WalletBatch batch(GetDatabase(), fFlushOnClose);

    uint256 hash = tx->GetHash();

    if (IsWalletFlagSet(WALLET_FLAG_AVOID_REUSE)) {
        // Mark used destinations
        std::set<CTxDestination> tx_destinations;

        for (const CTxIn& txin : tx->vin) {
            const COutPoint& op = txin.prevout;
            SetSpentKeyState(batch, op.hash, op.n, true, tx_destinations);
        }

        MarkDestinationsDirty(tx_destinations);
    }

    // Inserts only if not already there, returns tx inserted or tx found
    auto ret = mapWallet.emplace(std::piecewise_construct, std::forward_as_tuple(hash), std::forward_as_tuple(tx, state));
    CWalletTx& wtx = (*ret.first).second;
    bool fInsertedNew = ret.second;
    bool fUpdated = update_wtx && update_wtx(wtx, fInsertedNew);
    if (fInsertedNew) {
        wtx.nTimeReceived = GetTime();
        wtx.nOrderPos = IncOrderPosNext(&batch);
        wtx.m_it_wtxOrdered = wtxOrdered.insert(std::make_pair(wtx.nOrderPos, &wtx));
        wtx.nTimeSmart = ComputeTimeSmart(wtx, rescanning_old_block);
        AddToSpends(hash, &batch);
    }

    if (!fInsertedNew)
    {
        if (state.index() != wtx.m_state.index()) {
            wtx.m_state = state;
            fUpdated = true;
        } else {
            assert(TxStateSerializedIndex(wtx.m_state) == TxStateSerializedIndex(state));
            assert(TxStateSerializedBlockHash(wtx.m_state) == TxStateSerializedBlockHash(state));
        }
        // If we have a witness-stripped version of this transaction, and we
        // see a new version with a witness, then we must be upgrading a pre-segwit
        // wallet.  Store the new version of the transaction with the witness,
        // as the stripped-version must be invalid.
        // TODO: Store all versions of the transaction, instead of just one.
        if (tx->HasWitness() && !wtx.tx->HasWitness()) {
            wtx.SetTx(tx);
            fUpdated = true;
        }
    }

    //// debug print
    WalletLogPrintf("AddToWallet %s  %s%s\n", hash.ToString(), (fInsertedNew ? "new" : ""), (fUpdated ? "update" : ""));

    // Write to disk
    if (fInsertedNew || fUpdated)
        if (!batch.WriteTx(wtx))
            return nullptr;

    // Break debit/credit balance caches:
    wtx.MarkDirty(*this);

    // Notify UI of new or updated transaction
    NotifyTransactionChanged(hash, fInsertedNew ? CT_NEW : CT_UPDATED);

#if HAVE_SYSTEM
    // notify an external script when a wallet transaction comes in or is updated
    std::string strCmd = m_args.GetArg("-walletnotify", "");

    if (!strCmd.empty())
    {
        boost::replace_all(strCmd, "%s", hash.GetHex());
        if (auto* conf = wtx.state<TxStateConfirmed>())
        {
            boost::replace_all(strCmd, "%b", conf->confirmed_block_hash.GetHex());
            boost::replace_all(strCmd, "%h", ToString(conf->confirmed_block_height));
        } else {
            boost::replace_all(strCmd, "%b", "unconfirmed");
            boost::replace_all(strCmd, "%h", "-1");
        }
#ifndef WIN32
        // Substituting the wallet name isn't currently supported on windows
        // because windows shell escaping has not been implemented yet:
        // https://github.com/bitcoin/bitcoin/pull/13339#issuecomment-537384875
        // A few ways it could be implemented in the future are described in:
        // https://github.com/bitcoin/bitcoin/pull/13339#issuecomment-461288094
        boost::replace_all(strCmd, "%w", ShellEscape(GetName()));
#endif
        std::thread t(runCommand, strCmd);
        t.detach(); // thread runs free
    }
#endif

    return &wtx;
}

bool CWallet::LoadToWallet(const uint256& hash, const UpdateWalletTxFn& fill_wtx)
{
    const auto& ins = mapWallet.emplace(std::piecewise_construct, std::forward_as_tuple(hash), std::forward_as_tuple(nullptr, TxStateInactive{}));
    CWalletTx& wtx = ins.first->second;
    if (!fill_wtx(wtx, ins.second)) {
        return false;
    }
    // If wallet doesn't have a chain (e.g when using bitcoin-wallet tool),
    // don't bother to update txn.
    if (HaveChain()) {
        bool active;
        auto lookup_block = [&](const uint256& hash, int& height, TxState& state) {
            // If tx block (or conflicting block) was reorged out of chain
            // while the wallet was shutdown, change tx status to UNCONFIRMED
            // and reset block height, hash, and index. ABANDONED tx don't have
            // associated blocks and don't need to be updated. The case where a
            // transaction was reorged out while online and then reconfirmed
            // while offline is covered by the rescan logic.
            if (!chain().findBlock(hash, FoundBlock().inActiveChain(active).height(height)) || !active) {
                state = TxStateInactive{};
            }
        };
        if (auto* conf = wtx.state<TxStateConfirmed>()) {
            lookup_block(conf->confirmed_block_hash, conf->confirmed_block_height, wtx.m_state);
        } else if (auto* conf = wtx.state<TxStateConflicted>()) {
            lookup_block(conf->conflicting_block_hash, conf->conflicting_block_height, wtx.m_state);
        }
    }
    if (/* insertion took place */ ins.second) {
        wtx.m_it_wtxOrdered = wtxOrdered.insert(std::make_pair(wtx.nOrderPos, &wtx));
    }
    AddToSpends(hash);
    for (const CTxIn& txin : wtx.tx->vin) {
        auto it = mapWallet.find(txin.prevout.hash);
        if (it != mapWallet.end()) {
            CWalletTx& prevtx = it->second;
            if (auto* prev = prevtx.state<TxStateConflicted>()) {
                MarkConflicted(prev->conflicting_block_hash, prev->conflicting_block_height, wtx.GetHash());
            }
        }
    }
    return true;
}

bool CWallet::AddToWalletIfInvolvingMe(const CTransactionRef& ptx, const SyncTxState& state, bool fUpdate, bool rescanning_old_block)
{
    const CTransaction& tx = *ptx;
    {
        AssertLockHeld(cs_wallet);

        if (auto* conf = std::get_if<TxStateConfirmed>(&state)) {
            for (const CTxIn& txin : tx.vin) {
                std::pair<TxSpends::const_iterator, TxSpends::const_iterator> range = mapTxSpends.equal_range(txin.prevout);
                while (range.first != range.second) {
                    if (range.first->second != tx.GetHash()) {
                        WalletLogPrintf("Transaction %s (in block %s) conflicts with wallet transaction %s (both spend %s:%i)\n", tx.GetHash().ToString(), conf->confirmed_block_hash.ToString(), range.first->second.ToString(), range.first->first.hash.ToString(), range.first->first.n);
                        MarkConflicted(conf->confirmed_block_hash, conf->confirmed_block_height, range.first->second);
                    }
                    range.first++;
                }
            }
        }

        bool fExisted = mapWallet.count(tx.GetHash()) != 0;
        if (fExisted && !fUpdate) return false;
        if (fExisted || IsMine(tx) || IsFromMe(tx))
        {
            /* Check if any keys in the wallet keypool that were supposed to be unused
             * have appeared in a new transaction. If so, remove those keys from the keypool.
             * This can happen when restoring an old wallet backup that does not contain
             * the mostly recently created transactions from newer versions of the wallet.
             */

            // loop though all outputs
            for (const CTxOut& txout: tx.vout) {
                for (const auto& spk_man : GetScriptPubKeyMans(txout.scriptPubKey)) {
                    for (auto &dest : spk_man->MarkUnusedAddresses(txout.scriptPubKey)) {
                        // If internal flag is not defined try to infer it from the ScriptPubKeyMan
                        if (!dest.internal.has_value()) {
                            dest.internal = IsInternalScriptPubKeyMan(spk_man);
                        }

                        // skip if can't determine whether it's a receiving address or not
                        if (!dest.internal.has_value()) continue;

                        // If this is a receiving address and it's not in the address book yet
                        // (e.g. it wasn't generated on this node or we're restoring from backup)
                        // add it to the address book for proper transaction accounting
                        if (!*dest.internal && !FindAddressBookEntry(dest.dest, /* allow_change= */ false)) {
                            SetAddressBook(dest.dest, "", "receive");
                        }
                    }
                }
            }

            // Block disconnection override an abandoned tx as unconfirmed
            // which means user may have to call abandontransaction again
            TxState tx_state = std::visit([](auto&& s) -> TxState { return s; }, state);
            return AddToWallet(MakeTransactionRef(tx), tx_state, /*update_wtx=*/nullptr, /*fFlushOnClose=*/false, rescanning_old_block);
        }
    }
    return false;
}

bool CWallet::TransactionCanBeAbandoned(const uint256& hashTx) const
{
    LOCK(cs_wallet);
    const CWalletTx* wtx = GetWalletTx(hashTx);
    return wtx && !wtx->isAbandoned() && GetTxDepthInMainChain(*wtx) == 0 && !wtx->InMempool();
}

void CWallet::MarkInputsDirty(const CTransactionRef& tx)
{
    for (const CTxIn& txin : tx->vin) {
        auto it = mapWallet.find(txin.prevout.hash);
        if (it != mapWallet.end()) {
            it->second.MarkDirty(*this);
        }
    }
}

bool CWallet::AbandonTransaction(const uint256& hashTx)
{
    LOCK(cs_wallet);

    WalletBatch batch(GetDatabase());

    std::set<uint256> todo;
    std::set<uint256> done;

    // Can't mark abandoned if confirmed or in mempool
    auto it = mapWallet.find(hashTx);
    assert(it != mapWallet.end());
    const CWalletTx& origtx = it->second;
    if (GetTxDepthInMainChain(origtx) != 0 || origtx.InMempool()) {
        return false;
    }

    todo.insert(hashTx);

    while (!todo.empty()) {
        uint256 now = *todo.begin();
        todo.erase(now);
        done.insert(now);
        auto it = mapWallet.find(now);
        assert(it != mapWallet.end());
        CWalletTx& wtx = it->second;
        int currentconfirm = GetTxDepthInMainChain(wtx);
        // If the orig tx was not in block, none of its spends can be
        assert(currentconfirm <= 0);
        // if (currentconfirm < 0) {Tx and spends are already conflicted, no need to abandon}
        if (currentconfirm == 0 && !wtx.isAbandoned()) {
            // If the orig tx was not in block/mempool, none of its spends can be in mempool
            assert(!wtx.InMempool());
            wtx.m_state = TxStateInactive{/*abandoned=*/true};
            wtx.MarkDirty(*this);
            batch.WriteTx(wtx);
            NotifyTransactionChanged(wtx.GetHash(), CT_UPDATED);
            // Iterate over all its outputs, and mark transactions in the wallet that spend them abandoned too
            TxSpends::const_iterator iter = mapTxSpends.lower_bound(COutPoint(now, 0));
            while (iter != mapTxSpends.end() && iter->first.hash == now) {
                if (!done.count(iter->second)) {
                    todo.insert(iter->second);
                }
                iter++;
            }
            // If a transaction changes 'conflicted' state, that changes the balance
            // available of the outputs it spends. So force those to be recomputed
            MarkInputsDirty(wtx.tx);
        }
    }

    return true;
}

void CWallet::MarkConflicted(const uint256& hashBlock, int conflicting_height, const uint256& hashTx)
{
    LOCK(cs_wallet);

    int conflictconfirms = (m_last_block_processed_height - conflicting_height + 1) * -1;
    // If number of conflict confirms cannot be determined, this means
    // that the block is still unknown or not yet part of the main chain,
    // for example when loading the wallet during a reindex. Do nothing in that
    // case.
    if (conflictconfirms >= 0)
        return;

    // Do not flush the wallet here for performance reasons
    WalletBatch batch(GetDatabase(), false);

    std::set<uint256> todo;
    std::set<uint256> done;

    todo.insert(hashTx);

    while (!todo.empty()) {
        uint256 now = *todo.begin();
        todo.erase(now);
        done.insert(now);
        auto it = mapWallet.find(now);
        assert(it != mapWallet.end());
        CWalletTx& wtx = it->second;
        int currentconfirm = GetTxDepthInMainChain(wtx);
        if (conflictconfirms < currentconfirm) {
            // Block is 'more conflicted' than current confirm; update.
            // Mark transaction as conflicted with this block.
            wtx.m_state = TxStateConflicted{hashBlock, conflicting_height};
            wtx.MarkDirty(*this);
            batch.WriteTx(wtx);
            // Iterate over all its outputs, and mark transactions in the wallet that spend them conflicted too
            TxSpends::const_iterator iter = mapTxSpends.lower_bound(COutPoint(now, 0));
            while (iter != mapTxSpends.end() && iter->first.hash == now) {
                 if (!done.count(iter->second)) {
                     todo.insert(iter->second);
                 }
                 iter++;
            }
            // If a transaction changes 'conflicted' state, that changes the balance
            // available of the outputs it spends. So force those to be recomputed
            MarkInputsDirty(wtx.tx);
        }
    }
}

void CWallet::SyncTransaction(const CTransactionRef& ptx, const SyncTxState& state, bool update_tx, bool rescanning_old_block)
{
    if (!AddToWalletIfInvolvingMe(ptx, state, update_tx, rescanning_old_block))
        return; // Not one of ours

    // If a transaction changes 'conflicted' state, that changes the balance
    // available of the outputs it spends. So force those to be
    // recomputed, also:
    MarkInputsDirty(ptx);
}

void CWallet::transactionAddedToMempool(const CTransactionRef& tx, uint64_t mempool_sequence) {
    LOCK(cs_wallet);
    SyncTransaction(tx, TxStateInMempool{});

    auto it = mapWallet.find(tx->GetHash());
    if (it != mapWallet.end()) {
        RefreshMempoolStatus(it->second, chain());
    }
}

void CWallet::transactionRemovedFromMempool(const CTransactionRef& tx, MemPoolRemovalReason reason, uint64_t mempool_sequence) {
    LOCK(cs_wallet);
    auto it = mapWallet.find(tx->GetHash());
    if (it != mapWallet.end()) {
        RefreshMempoolStatus(it->second, chain());
    }
    // Handle transactions that were removed from the mempool because they
    // conflict with transactions in a newly connected block.
    if (reason == MemPoolRemovalReason::CONFLICT) {
        // Trigger external -walletnotify notifications for these transactions.
        // Set Status::UNCONFIRMED instead of Status::CONFLICTED for a few reasons:
        //
        // 1. The transactionRemovedFromMempool callback does not currently
        //    provide the conflicting block's hash and height, and for backwards
        //    compatibility reasons it may not be not safe to store conflicted
        //    wallet transactions with a null block hash. See
        //    https://github.com/bitcoin/bitcoin/pull/18600#discussion_r420195993.
        // 2. For most of these transactions, the wallet's internal conflict
        //    detection in the blockConnected handler will subsequently call
        //    MarkConflicted and update them with CONFLICTED status anyway. This
        //    applies to any wallet transaction that has inputs spent in the
        //    block, or that has ancestors in the wallet with inputs spent by
        //    the block.
        // 3. Longstanding behavior since the sync implementation in
        //    https://github.com/bitcoin/bitcoin/pull/9371 and the prior sync
        //    implementation before that was to mark these transactions
        //    unconfirmed rather than conflicted.
        //
        // Nothing described above should be seen as an unchangeable requirement
        // when improving this code in the future. The wallet's heuristics for
        // distinguishing between conflicted and unconfirmed transactions are
        // imperfect, and could be improved in general, see
        // https://github.com/bitcoin-core/bitcoin-devwiki/wiki/Wallet-Transaction-Conflict-Tracking
        SyncTransaction(tx, TxStateInactive{});
    }
}

void CWallet::blockConnected(const CBlock& block, int height)
{
    const uint256& block_hash = block.GetHash();
    LOCK(cs_wallet);

    m_last_block_processed_height = height;
    m_last_block_processed = block_hash;
    for (size_t index = 0; index < block.vtx.size(); index++) {
        SyncTransaction(block.vtx[index], TxStateConfirmed{block_hash, height, static_cast<int>(index)});
        transactionRemovedFromMempool(block.vtx[index], MemPoolRemovalReason::BLOCK, 0 /* mempool_sequence */);
    }
}

void CWallet::blockDisconnected(const CBlock& block, int height)
{
    LOCK(cs_wallet);

    // At block disconnection, this will change an abandoned transaction to
    // be unconfirmed, whether or not the transaction is added back to the mempool.
    // User may have to call abandontransaction again. It may be addressed in the
    // future with a stickier abandoned state or even removing abandontransaction call.
    m_last_block_processed_height = height - 1;
    m_last_block_processed = block.hashPrevBlock;
    for (const CTransactionRef& ptx : block.vtx) {
        SyncTransaction(ptx, TxStateInactive{});
    }
}

void CWallet::updatedBlockTip()
{
    m_best_block_time = GetTime();
}

void CWallet::BlockUntilSyncedToCurrentChain() const {
    AssertLockNotHeld(cs_wallet);
    // Skip the queue-draining stuff if we know we're caught up with
    // chain().Tip(), otherwise put a callback in the validation interface queue and wait
    // for the queue to drain enough to execute it (indicating we are caught up
    // at least with the time we entered this function).
    uint256 last_block_hash = WITH_LOCK(cs_wallet, return m_last_block_processed);
    chain().waitForNotificationsIfTipChanged(last_block_hash);
}

// Note that this function doesn't distinguish between a 0-valued input,
// and a not-"is mine" (according to the filter) input.
CAmountMap CWallet::GetDebit(const CTxIn &txin, const isminefilter& filter) const
{
    {
        LOCK(cs_wallet);
        std::map<uint256, CWalletTx>::const_iterator mi = mapWallet.find(txin.prevout.hash);
        if (mi != mapWallet.end())
        {
            const CWalletTx& prev = (*mi).second;
            if (txin.prevout.n < prev.tx->vout.size())
                if (IsMine(prev.tx->vout[txin.prevout.n]) & filter) {
                    CAmountMap amounts;
                    amounts[prev.GetOutputAsset(*this, txin.prevout.n)] = std::max<CAmount>(0, prev.GetOutputValueOut(*this, txin.prevout.n));
                    return amounts;
                }
        }
    }
    return CAmountMap();
}

isminetype CWallet::IsMine(const CTxOut& txout) const
{
    AssertLockHeld(cs_wallet);
    return IsMine(txout.scriptPubKey);
}

isminetype CWallet::IsMine(const CTxDestination& dest) const
{
    AssertLockHeld(cs_wallet);
    return IsMine(GetScriptForDestination(dest));
}

isminetype CWallet::IsMine(const CScript& script) const
{
    AssertLockHeld(cs_wallet);
    isminetype result = ISMINE_NO;
    for (const auto& spk_man_pair : m_spk_managers) {
        result = std::max(result, spk_man_pair.second->IsMine(script));
    }
    return result;
}

bool CWallet::IsMine(const CTransaction& tx) const
{
    AssertLockHeld(cs_wallet);
    for (const CTxOut& txout : tx.vout)
        if (IsMine(txout))
            return true;
    return false;
}

bool CWallet::IsFromMe(const CTransaction& tx) const
{
    return (GetDebit(tx, ISMINE_ALL) > CAmountMap());
}

CAmountMap CWallet::GetDebit(const CTransaction& tx, const isminefilter& filter) const
{
    CAmountMap nDebit;
    for (const CTxIn& txin : tx.vin)
    {
        nDebit += GetDebit(txin, filter);
        if (!MoneyRange(nDebit))
            throw std::runtime_error(std::string(__func__) + ": value out of range");
    }
    return nDebit;
}

bool CWallet::IsHDEnabled() const
{
    // All Active ScriptPubKeyMans must be HD for this to be true
    bool result = false;
    for (const auto& spk_man : GetActiveScriptPubKeyMans()) {
        if (!spk_man->IsHDEnabled()) return false;
        result = true;
    }
    return result;
}

bool CWallet::CanGetAddresses(bool internal) const
{
    LOCK(cs_wallet);
    if (m_spk_managers.empty()) return false;
    for (OutputType t : OUTPUT_TYPES) {
        auto spk_man = GetScriptPubKeyMan(t, internal);
        if (spk_man && spk_man->CanGetAddresses(internal)) {
            return true;
        }
    }
    return false;
}

void CWallet::SetWalletFlag(uint64_t flags)
{
    LOCK(cs_wallet);
    m_wallet_flags |= flags;
    if (!WalletBatch(GetDatabase()).WriteWalletFlags(m_wallet_flags))
        throw std::runtime_error(std::string(__func__) + ": writing wallet flags failed");
}

void CWallet::UnsetWalletFlag(uint64_t flag)
{
    WalletBatch batch(GetDatabase());
    UnsetWalletFlagWithDB(batch, flag);
}

void CWallet::UnsetWalletFlagWithDB(WalletBatch& batch, uint64_t flag)
{
    LOCK(cs_wallet);
    m_wallet_flags &= ~flag;
    if (!batch.WriteWalletFlags(m_wallet_flags))
        throw std::runtime_error(std::string(__func__) + ": writing wallet flags failed");
}

void CWallet::UnsetBlankWalletFlag(WalletBatch& batch)
{
    UnsetWalletFlagWithDB(batch, WALLET_FLAG_BLANK_WALLET);
}

bool CWallet::IsWalletFlagSet(uint64_t flag) const
{
    return (m_wallet_flags & flag);
}

bool CWallet::LoadWalletFlags(uint64_t flags)
{
    LOCK(cs_wallet);
    if (((flags & KNOWN_WALLET_FLAGS) >> 32) ^ (flags >> 32)) {
        // contains unknown non-tolerable wallet flags
        return false;
    }
    m_wallet_flags = flags;

    return true;
}

bool CWallet::AddWalletFlags(uint64_t flags)
{
    LOCK(cs_wallet);
    // We should never be writing unknown non-tolerable wallet flags
    assert(((flags & KNOWN_WALLET_FLAGS) >> 32) == (flags >> 32));
    if (!WalletBatch(GetDatabase()).WriteWalletFlags(flags)) {
        throw std::runtime_error(std::string(__func__) + ": writing wallet flags failed");
    }

    return LoadWalletFlags(flags);
}

bool CWallet::ImportScripts(const std::set<CScript> scripts, int64_t timestamp)
{
    auto spk_man = GetLegacyScriptPubKeyMan();
    if (!spk_man) {
        return false;
    }
    LOCK(spk_man->cs_KeyStore);
    return spk_man->ImportScripts(scripts, timestamp);
}

bool CWallet::ImportPrivKeys(const std::map<CKeyID, CKey>& privkey_map, const int64_t timestamp)
{
    auto spk_man = GetLegacyScriptPubKeyMan();
    if (!spk_man) {
        return false;
    }
    LOCK(spk_man->cs_KeyStore);
    return spk_man->ImportPrivKeys(privkey_map, timestamp);
}

bool CWallet::ImportPubKeys(const std::vector<CKeyID>& ordered_pubkeys, const std::map<CKeyID, CPubKey>& pubkey_map, const std::map<CKeyID, std::pair<CPubKey, KeyOriginInfo>>& key_origins, const bool add_keypool, const bool internal, const int64_t timestamp)
{
    auto spk_man = GetLegacyScriptPubKeyMan();
    if (!spk_man) {
        return false;
    }
    LOCK(spk_man->cs_KeyStore);
    return spk_man->ImportPubKeys(ordered_pubkeys, pubkey_map, key_origins, add_keypool, internal, timestamp);
}

bool CWallet::ImportScriptPubKeys(const std::string& label, const std::set<CScript>& script_pub_keys, const bool have_solving_data, const bool apply_label, const int64_t timestamp)
{
    auto spk_man = GetLegacyScriptPubKeyMan();
    if (!spk_man) {
        return false;
    }
    LOCK(spk_man->cs_KeyStore);
    if (!spk_man->ImportScriptPubKeys(script_pub_keys, have_solving_data, timestamp)) {
        return false;
    }
    if (apply_label) {
        WalletBatch batch(GetDatabase());
        for (const CScript& script : script_pub_keys) {
            CTxDestination dest;
            ExtractDestination(script, dest);
            if (IsValidDestination(dest)) {
                SetAddressBookWithDB(batch, dest, label, "receive");
            }
        }
    }
    return true;
}

/**
 * Scan active chain for relevant transactions after importing keys. This should
 * be called whenever new keys are added to the wallet, with the oldest key
 * creation time.
 *
 * @return Earliest timestamp that could be successfully scanned from. Timestamp
 * returned will be higher than startTime if relevant blocks could not be read.
 */
int64_t CWallet::RescanFromTime(int64_t startTime, const WalletRescanReserver& reserver, bool update)
{
    // Find starting block. May be null if nCreateTime is greater than the
    // highest blockchain timestamp, in which case there is nothing that needs
    // to be scanned.
    int start_height = 0;
    uint256 start_block;
    bool start = chain().findFirstBlockWithTimeAndHeight(startTime - TIMESTAMP_WINDOW, 0, FoundBlock().hash(start_block).height(start_height));
    WalletLogPrintf("%s: Rescanning last %i blocks\n", __func__, start ? WITH_LOCK(cs_wallet, return GetLastBlockHeight()) - start_height + 1 : 0);

    if (start) {
        // TODO: this should take into account failure by ScanResult::USER_ABORT
        ScanResult result = ScanForWalletTransactions(start_block, start_height, {} /* max_height */, reserver, update);
        if (result.status == ScanResult::FAILURE) {
            int64_t time_max;
            CHECK_NONFATAL(chain().findBlock(result.last_failed_block, FoundBlock().maxTime(time_max)));
            return time_max + TIMESTAMP_WINDOW + 1;
        }
    }
    return startTime;
}

/**
 * Scan the block chain (starting in start_block) for transactions
 * from or to us. If fUpdate is true, found transactions that already
 * exist in the wallet will be updated.
 *
 * @param[in] start_block Scan starting block. If block is not on the active
 *                        chain, the scan will return SUCCESS immediately.
 * @param[in] start_height Height of start_block
 * @param[in] max_height  Optional max scanning height. If unset there is
 *                        no maximum and scanning can continue to the tip
 *
 * @return ScanResult returning scan information and indicating success or
 *         failure. Return status will be set to SUCCESS if scan was
 *         successful. FAILURE if a complete rescan was not possible (due to
 *         pruning or corruption). USER_ABORT if the rescan was aborted before
 *         it could complete.
 *
 * @pre Caller needs to make sure start_block (and the optional stop_block) are on
 * the main chain after to the addition of any new keys you want to detect
 * transactions for.
 */
CWallet::ScanResult CWallet::ScanForWalletTransactions(const uint256& start_block, int start_height, std::optional<int> max_height, const WalletRescanReserver& reserver, bool fUpdate)
{
    int64_t nNow = GetTime();
    int64_t start_time = GetTimeMillis();

    assert(reserver.isReserved());

    uint256 block_hash = start_block;
    ScanResult result;

    WalletLogPrintf("Rescan started from block %s...\n", start_block.ToString());

    fAbortRescan = false;
    ShowProgress(strprintf("%s " + _("Rescanning…").translated, GetDisplayName()), 0); // show rescan progress in GUI as dialog or on splashscreen, if rescan required on startup (e.g. due to corruption)
    uint256 tip_hash = WITH_LOCK(cs_wallet, return GetLastBlockHash());
    uint256 end_hash = tip_hash;
    if (max_height) chain().findAncestorByHeight(tip_hash, *max_height, FoundBlock().hash(end_hash));
    double progress_begin = chain().guessVerificationProgress(block_hash);
    double progress_end = chain().guessVerificationProgress(end_hash);
    double progress_current = progress_begin;
    int block_height = start_height;
    while (!fAbortRescan && !chain().shutdownRequested()) {
        if (progress_end - progress_begin > 0.0) {
            m_scanning_progress = (progress_current - progress_begin) / (progress_end - progress_begin);
        } else { // avoid divide-by-zero for single block scan range (i.e. start and stop hashes are equal)
            m_scanning_progress = 0;
        }
        if (block_height % 100 == 0 && progress_end - progress_begin > 0.0) {
            ShowProgress(strprintf("%s " + _("Rescanning…").translated, GetDisplayName()), std::max(1, std::min(99, (int)(m_scanning_progress * 100))));
        }
        if (GetTime() >= nNow + 60) {
            nNow = GetTime();
            WalletLogPrintf("Still rescanning. At block %d. Progress=%f\n", block_height, progress_current);
        }

        // Read block data
        CBlock block;
        chain().findBlock(block_hash, FoundBlock().data(block));

        // Find next block separately from reading data above, because reading
        // is slow and there might be a reorg while it is read.
        bool block_still_active = false;
        bool next_block = false;
        uint256 next_block_hash;
        chain().findBlock(block_hash, FoundBlock().inActiveChain(block_still_active).nextBlock(FoundBlock().inActiveChain(next_block).hash(next_block_hash)));

        if (!block.IsNull()) {
            LOCK(cs_wallet);
            if (!block_still_active) {
                // Abort scan if current block is no longer active, to prevent
                // marking transactions as coming from the wrong block.
                result.last_failed_block = block_hash;
                result.status = ScanResult::FAILURE;
                break;
            }
            for (size_t posInBlock = 0; posInBlock < block.vtx.size(); ++posInBlock) {
                SyncTransaction(block.vtx[posInBlock], TxStateConfirmed{block_hash, block_height, static_cast<int>(posInBlock)}, fUpdate, /*rescanning_old_block=*/true);
            }
            // scan succeeded, record block as most recent successfully scanned
            result.last_scanned_block = block_hash;
            result.last_scanned_height = block_height;
        } else {
            // could not scan block, keep scanning but record this block as the most recent failure
            result.last_failed_block = block_hash;
            result.status = ScanResult::FAILURE;
        }
        if (max_height && block_height >= *max_height) {
            break;
        }
        if (block_height >= WITH_LOCK(cs_wallet, return GetLastBlockHeight())) {
            WalletLogPrintf("Stopping scan. At block %d. Progress=%f\n", block_height, progress_current);
            break;
        }

        {
            if (!next_block) {
                // break successfully when rescan has reached the tip, or
                // previous block is no longer on the chain due to a reorg
                break;
            }

            // increment block and verification progress
            block_hash = next_block_hash;
            ++block_height;
            progress_current = chain().guessVerificationProgress(block_hash);

            // handle updated tip hash
            const uint256 prev_tip_hash = tip_hash;
            tip_hash = WITH_LOCK(cs_wallet, return GetLastBlockHash());
            if (!max_height && prev_tip_hash != tip_hash) {
                // in case the tip has changed, update progress max
                progress_end = chain().guessVerificationProgress(tip_hash);
            }
        }
    }
    ShowProgress(strprintf("%s " + _("Rescanning…").translated, GetDisplayName()), 100); // hide progress dialog in GUI
    if (block_height && fAbortRescan) {
        WalletLogPrintf("Rescan aborted at block %d. Progress=%f\n", block_height, progress_current);
        result.status = ScanResult::USER_ABORT;
    } else if (block_height && chain().shutdownRequested()) {
        WalletLogPrintf("Rescan interrupted by shutdown request at block %d. Progress=%f\n", block_height, progress_current);
        result.status = ScanResult::USER_ABORT;
    } else {
        WalletLogPrintf("Rescan completed in %15dms\n", GetTimeMillis() - start_time);
    }
    return result;
}

void CWallet::ReacceptWalletTransactions()
{
    // If transactions aren't being broadcasted, don't let them into local mempool either
    if (!fBroadcastTransactions)
        return;
    std::map<int64_t, CWalletTx*> mapSorted;

    // Sort pending wallet transactions based on their initial wallet insertion order
    for (std::pair<const uint256, CWalletTx>& item : mapWallet) {
        const uint256& wtxid = item.first;
        CWalletTx& wtx = item.second;
        assert(wtx.GetHash() == wtxid);

        int nDepth = GetTxDepthInMainChain(wtx);

        if (!wtx.IsCoinBase() && (nDepth == 0 && !wtx.isAbandoned())) {
            mapSorted.insert(std::make_pair(wtx.nOrderPos, &wtx));
        }
    }

    // Try to add wallet transactions to memory pool
    for (const std::pair<const int64_t, CWalletTx*>& item : mapSorted) {
        CWalletTx& wtx = *(item.second);
        std::string unused_err_string;
        SubmitTxMemoryPoolAndRelay(wtx, unused_err_string, false);
    }
}

bool CWallet::SubmitTxMemoryPoolAndRelay(CWalletTx& wtx, std::string& err_string, bool relay) const
{
    // Can't relay if wallet is not broadcasting
    if (!GetBroadcastTransactions()) return false;
    // Don't relay abandoned transactions
    if (wtx.isAbandoned()) return false;
    // Don't try to submit coinbase transactions. These would fail anyway but would
    // cause log spam.
    if (wtx.IsCoinBase()) return false;
    // Don't try to submit conflicted or confirmed transactions.
    if (GetTxDepthInMainChain(wtx) != 0) return false;

    // Submit transaction to mempool for relay
    WalletLogPrintf("Submitting wtx %s to mempool for relay\n", wtx.GetHash().ToString());
    // We must set TxStateInMempool here. Even though it will also be set later by the
    // entered-mempool callback, if we did not there would be a race where a
    // user could call sendmoney in a loop and hit spurious out of funds errors
    // because we think that this newly generated transaction's change is
    // unavailable as we're not yet aware that it is in the mempool.
    //
    // If broadcast fails for any reason, trying to set wtx.m_state here would be incorrect.
    // If transaction was previously in the mempool, it should be updated when
    // TransactionRemovedFromMempool fires.
    bool ret = chain().broadcastTransaction(wtx.tx, m_default_max_tx_fee, relay, err_string);
    if (ret) wtx.m_state = TxStateInMempool{};
    return ret;
}

std::set<uint256> CWallet::GetTxConflicts(const CWalletTx& wtx) const
{
    std::set<uint256> result;
    {
        uint256 myHash = wtx.GetHash();
        result = GetConflicts(myHash);
        result.erase(myHash);
    }
    return result;
}

// Rebroadcast transactions from the wallet. We do this on a random timer
// to slightly obfuscate which transactions come from our wallet.
//
// Ideally, we'd only resend transactions that we think should have been
// mined in the most recent block. Any transaction that wasn't in the top
// blockweight of transactions in the mempool shouldn't have been mined,
// and so is probably just sitting in the mempool waiting to be confirmed.
// Rebroadcasting does nothing to speed up confirmation and only damages
// privacy.
void CWallet::ResendWalletTransactions()
{
    // During reindex, importing and IBD, old wallet transactions become
    // unconfirmed. Don't resend them as that would spam other nodes.
    if (!chain().isReadyToBroadcast()) return;

    // Do this infrequently and randomly to avoid giving away
    // that these are our transactions.
    if (GetTime() < nNextResend || !fBroadcastTransactions) return;
    bool fFirst = (nNextResend == 0);
    // resend 12-36 hours from now, ~1 day on average.
    nNextResend = GetTime() + (12 * 60 * 60) + GetRand(24 * 60 * 60);
    if (fFirst) return;

    int submitted_tx_count = 0;

    { // cs_wallet scope
        LOCK(cs_wallet);

        // Relay transactions
        for (std::pair<const uint256, CWalletTx>& item : mapWallet) {
            CWalletTx& wtx = item.second;
            // Attempt to rebroadcast all txes more than 5 minutes older than
            // the last block. SubmitTxMemoryPoolAndRelay() will not rebroadcast
            // any confirmed or conflicting txs.
            if (wtx.nTimeReceived > m_best_block_time - 5 * 60) continue;
            std::string unused_err_string;
            if (SubmitTxMemoryPoolAndRelay(wtx, unused_err_string, true)) ++submitted_tx_count;
        }
    } // cs_wallet

    if (submitted_tx_count > 0) {
        WalletLogPrintf("%s: resubmit %u unconfirmed transactions\n", __func__, submitted_tx_count);
    }
}

/** @} */ // end of mapWallet

void MaybeResendWalletTxs(WalletContext& context)
{
    for (const std::shared_ptr<CWallet>& pwallet : GetWallets(context)) {
        pwallet->ResendWalletTransactions();
    }
}


/** @defgroup Actions
 *
 * @{
 */

bool CWallet::SignTransaction(CMutableTransaction& tx) const
{
    AssertLockHeld(cs_wallet);

    // Build coins map
    std::map<COutPoint, Coin> coins;
    for (auto& input : tx.vin) {
        std::map<uint256, CWalletTx>::const_iterator mi = mapWallet.find(input.prevout.hash);
        if(mi == mapWallet.end() || input.prevout.n >= mi->second.tx->vout.size()) {
            return false;
        }
        const CWalletTx& wtx = mi->second;
        int prev_height = wtx.state<TxStateConfirmed>() ? wtx.state<TxStateConfirmed>()->confirmed_block_height : 0;
        coins[input.prevout] = Coin(wtx.tx->vout[input.prevout.n], prev_height, wtx.IsCoinBase());
    }
    std::map<int, bilingual_str> input_errors;
    return SignTransaction(tx, coins, SIGHASH_DEFAULT, input_errors);
}

bool CWallet::SignTransaction(CMutableTransaction& tx, const std::map<COutPoint, Coin>& coins, int sighash, std::map<int, bilingual_str>& input_errors) const
{
    // Try to sign with all ScriptPubKeyMans
    tx.witness.vtxinwit.resize(tx.vin.size());
    for (ScriptPubKeyMan* spk_man : GetAllScriptPubKeyMans()) {
        // spk_man->SignTransaction will return true if the transaction is complete,
        // so we can exit early and return true if that happens
        if (spk_man->SignTransaction(tx, coins, sighash, input_errors)) {
            return true;
        }
    }

    // At this point, one input was not fully signed otherwise we would have exited already
    return false;
}

// ELEMENTS: split FillPSBT into FillPSBData and SignPSBT
TransactionError CWallet::FillPSBTData(PartiallySignedTransaction& psbtx, bool bip32derivs, bool include_explicit) const
{
    const PrecomputedTransactionData txdata = PrecomputePSBTData(psbtx);
    LOCK(cs_wallet);

    // Get all of the previous transactions
    for (PSBTInput& input : psbtx.inputs) {
        if (PSBTInputSigned(input)) {
            continue;
        }

        // If we have no utxo, grab it from the wallet.
        if (!input.non_witness_utxo) {
            const uint256& txhash = input.prev_txid;
            const auto it = mapWallet.find(txhash);
            if (it != mapWallet.end()) {
                const CWalletTx& wtx = it->second;
                // We only need the non_witness_utxo, which is a superset of the witness_utxo.
                //   The signing code will switch to the smaller witness_utxo if this is ok.
                input.non_witness_utxo = wtx.tx;
                // Set the UTXO rangeproof separately, if it's there
                if (*input.prev_out < wtx.tx->witness.vtxoutwit.size() && !wtx.tx->witness.vtxoutwit[*input.prev_out].vchRangeproof.empty()) {
                    input.m_utxo_rangeproof = wtx.tx->witness.vtxoutwit[*input.prev_out].vchRangeproof;
                }
                const CTxOut& utxo = wtx.tx->vout[*input.prev_out];
                if (include_explicit && utxo.nAsset.IsCommitment()) {
                    const CAsset asset = wtx.GetOutputAsset(*this, *input.prev_out);
                    input.m_explicit_asset = asset.id;
                    CreateBlindAssetProof(input.m_asset_proof, asset, utxo.nAsset, wtx.GetOutputAssetBlindingFactor(*this, *input.prev_out));

                    if (utxo.nValue.IsCommitment()) {
                        input.m_explicit_value = wtx.GetOutputValueOut(*this, *input.prev_out);
                        CreateBlindValueProof(input.m_value_proof, wtx.GetOutputAmountBlindingFactor(*this, *input.prev_out), *input.m_explicit_value, utxo.nValue, utxo.nAsset);
                    }
                }
            }
        }
    }

    // Fill in information from ScriptPubKeyMans
    // Because each ScriptPubKeyMan may be able to fill more than one input, we need to keep track of each ScriptPubKeyMan that has filled this psbt.
    // Each iteration, we may fill more inputs than the input that is specified in that iteration.
    // We assume that each input is filled by only one ScriptPubKeyMan
    std::set<uint256> visited_spk_mans;
    for (PSBTInput& input : psbtx.inputs) {
        if (PSBTInputSigned(input)) {
            continue;
        }

        // Get the scriptPubKey to know which ScriptPubKeyMan to use
        CScript script;
        if (!input.witness_utxo.IsNull()) {
            script = input.witness_utxo.scriptPubKey;
        } else if (input.non_witness_utxo) {
            if (*input.prev_out >= input.non_witness_utxo->vout.size()) {
                return TransactionError::MISSING_INPUTS;
            }
            script = input.non_witness_utxo->vout[*input.prev_out].scriptPubKey;
        } else {
            // There's no UTXO so we can just skip this now
            continue;
        }
        SignatureData sigdata;
        input.FillSignatureData(sigdata);
        std::set<ScriptPubKeyMan*> spk_mans = GetScriptPubKeyMans(script);
        if (spk_mans.size() == 0) {
            continue;
        }

        for (auto& spk_man : spk_mans) {
            // If we've already been signed by this spk_man, skip it
            if (visited_spk_mans.count(spk_man->GetID()) > 0) {
                continue;
            }

            // Fill in the information from the spk_man
            // ELEMENTS: Get key origin info for input, if bip32derivs is true. Does not actually sign anything.
            TransactionError res = spk_man->FillPSBT(psbtx, txdata, 1, false /* don't sign */, bip32derivs, nullptr, false);
            if (res != TransactionError::OK) {
                return res;
            }

            // Add this spk_man to visited_spk_mans so we can skip it later
            visited_spk_mans.insert(spk_man->GetID());
        }
    }

    return TransactionError::OK;
}

BlindingStatus CWallet::WalletBlindPSBT(PartiallySignedTransaction& psbtx) const
{
    // Gather our input data
    LOCK(cs_wallet);
    std::map<uint32_t, std::tuple<CAmount, CAsset, uint256, uint256>> our_input_data;
    std::map<uint32_t, std::pair<CKey, CKey>> our_issuances_to_blind;
    for (unsigned int i = 0; i < psbtx.inputs.size(); ++i) {
        PSBTInput& input = psbtx.inputs[i];

        if (input.m_peg_in_value && !input.m_peg_in_claim_script.empty()) {
            if (!this->IsMine(CTxOut(Params().GetConsensus().pegged_asset, *input.m_peg_in_value, input.m_peg_in_claim_script))) continue;
            our_input_data[i] = std::make_tuple(*input.m_peg_in_value, Params().GetConsensus().pegged_asset, uint256(), uint256());
        } else {
            if (!InputIsMine(*this, COutPoint(input.prev_txid, *input.prev_out))) continue;
            const CWalletTx* wtx = GetWalletTx(input.prev_txid);
            if (!wtx) continue;
            CPubKey blinding_pubkey;
            CAmount amount;
            uint256 value_blinder;
            CAsset asset;
            uint256 asset_blinder;
            wtx->GetNonIssuanceBlindingData(*this, *input.prev_out, &blinding_pubkey, &amount, &value_blinder, &asset, &asset_blinder);
            our_input_data[i] = std::make_tuple(amount, asset, asset_blinder, value_blinder);
        }

        // Blind issuances on our inputs if at least one commitment was provided.
        if (input.m_issuance_value_commitment.IsCommitment() || input.m_issuance_inflation_keys_commitment.IsCommitment()) {
            CScript blinding_script(CScript() << OP_RETURN << std::vector<unsigned char>(input.prev_txid.begin(), input.prev_txid.end()) << *input.prev_out);
            our_issuances_to_blind[i] = std::make_pair(GetBlindingKey(&blinding_script), GetBlindingKey(&blinding_script));
        }
    }

    // Blind the PSBT
    return BlindPSBT(psbtx, our_input_data, our_issuances_to_blind);
}
TransactionError CWallet::SignPSBT(PartiallySignedTransaction& psbtx, bool& complete, int sighash_type, bool sign, bool imbalance_ok, bool bip32derivs, size_t* n_signed, bool finalize) const
{
    LOCK(cs_wallet);

    // If we're signing, check that the transaction is not still in need of blinding
    // Also check that the amount and asset proofs are valid
    if (sign) {
        for (const PSBTOutput& o : psbtx.outputs) {
            if (o.IsBlinded()) {
                switch (VerifyBlindProofs(o)) {
                    case BlindProofResult::OK:
                        break;
                    case BlindProofResult::NOT_FULLY_BLINDED:
                        return TransactionError::BLINDING_REQUIRED;
                    case BlindProofResult::INVALID_VALUE_PROOF:
                    case BlindProofResult::MISSING_VALUE_PROOF:
                        return TransactionError::INVALID_VALUE_PROOF;
                    case BlindProofResult::INVALID_ASSET_PROOF:
                    case BlindProofResult::MISSING_ASSET_PROOF:
                        return TransactionError::INVALID_ASSET_PROOF;
                }

                if (o.script && IsMine(*o.script)) {
                    CKey blinding_key;
                    if ((blinding_key = GetBlindingKey(&*o.script)).IsValid()) {
                        CAmount value;
                        uint256 value_factor;
                        CAsset asset;
                        uint256 asset_factor;

                        CConfidentialNonce nonce;
                        nonce.vchCommitment.insert(nonce.vchCommitment.end(), o.m_ecdh_pubkey.begin(), o.m_ecdh_pubkey.end());
                        if (UnblindConfidentialPair(blinding_key, o.m_value_commitment, o.m_asset_commitment, nonce, *o.script, o.m_value_rangeproof, value, value_factor, asset, asset_factor)) {
                            // These assertions are cryptographically impossible to trigger, as we
                            // checked the proofs above, and then `UnblindConfidentialPair` checks
                            // the extracted value/asset against the commitments.
                            if (o.amount) {
                                assert(*o.amount == value);
                            }
                            if (!o.m_asset.IsNull()) {
                                assert(CAsset(o.m_asset) == asset);
                            }
                        } else {
                            return TransactionError::MISSING_SIDECHANNEL_DATA;
                        }
                    } else {
                        return TransactionError::MISSING_BLINDING_KEY;
                    }
                }
            }
        }
    }

    if (n_signed) {
        *n_signed = 0;
    }

    CMutableTransaction tx = psbtx.GetUnsignedTx();
    tx.witness.vtxoutwit.resize(tx.vout.size());

    // Stuff in auxiliary CA blinding data, if we have it
    for (unsigned int i = 0; i < tx.vout.size(); ++i) {
        PSBTOutput& output = psbtx.outputs.at(i);
        CTxOut& out = tx.vout[i];

        if (!output.m_value_commitment.IsNull()) {
            out.nValue = output.m_value_commitment;
        } else if (output.amount) {
            out.nValue.SetToAmount(*output.amount);
        }
        if (!output.m_asset_commitment.IsNull()) {
            out.nAsset = output.m_asset_commitment;
        } else if (!output.m_asset.IsNull()) {
            out.nAsset.SetToAsset(CAsset(output.m_asset));
        }
        if (output.m_ecdh_pubkey.IsValid()) {
            // The nonce is actually the ecdh pubkey
            out.nNonce.vchCommitment.clear();
            out.nNonce.vchCommitment.insert(out.nNonce.vchCommitment.end(), output.m_ecdh_pubkey.begin(), output.m_ecdh_pubkey.end());
        }

        // The signature can't depend on witness contents, so these are technically not necessary to sign.
        // HOWEVER, as long as we're checking that values balance before signing, they are required.
        CTxOutWitness& outwit = tx.witness.vtxoutwit[i];
        if (!output.m_value_rangeproof.empty()) {
            outwit.vchRangeproof = output.m_value_rangeproof;
        }
        if (!output.m_asset_surjection_proof.empty()) {
            outwit.vchSurjectionproof = output.m_asset_surjection_proof;
        }
    }

    // Stuff in the peg-in and issuance data
    for (unsigned int i = 0; i < tx.vin.size(); ++i) {
        PSBTInput& input = psbtx.inputs[i];
        CTxIn& txin = tx.vin[i];
        CTxInWitness& txinwit = tx.witness.vtxinwit[i];
        if (input.m_peg_in_value &&
                input.m_peg_in_tx.index() > 0 &&
                input.m_peg_in_txout_proof.index() > 0 &&
                !input.m_peg_in_claim_script.empty() &&
                !input.m_peg_in_genesis_hash.IsNull()) {
            CScriptWitness pegin_witness;
            if (Params().GetConsensus().ParentChainHasPow()) {
                pegin_witness = CreatePeginWitness(*input.m_peg_in_value, Params().GetConsensus().pegged_asset, input.m_peg_in_genesis_hash, input.m_peg_in_claim_script, *std::get_if<Sidechain::Bitcoin::CTransactionRef>(&input.m_peg_in_tx), *std::get_if<Sidechain::Bitcoin::CMerkleBlock>(&input.m_peg_in_txout_proof));
            } else {
                pegin_witness = CreatePeginWitness(*input.m_peg_in_value, Params().GetConsensus().pegged_asset, input.m_peg_in_genesis_hash, input.m_peg_in_claim_script, *std::get_if<CTransactionRef>(&input.m_peg_in_tx), *std::get_if<CMerkleBlock>(&input.m_peg_in_txout_proof));
            }
            tx.vin[i].m_is_pegin = true;
            tx.witness.vtxinwit[i].m_pegin_witness = pegin_witness;
            // Set the witness utxo
            input.witness_utxo = GetPeginOutputFromWitness(tx.witness.vtxinwit[i].m_pegin_witness);
        }
        if (!input.m_issuance_value_commitment.IsNull()) {
            txin.assetIssuance.nAmount = input.m_issuance_value_commitment;
        } else if (input.m_issuance_value) {
            txin.assetIssuance.nAmount.SetToAmount(*input.m_issuance_value);
        } else {
            txin.assetIssuance.nAmount.SetNull();
        }
        if (!input.m_issuance_inflation_keys_commitment.IsNull()) {
            txin.assetIssuance.nInflationKeys = input.m_issuance_inflation_keys_commitment;
        } else if (input.m_issuance_inflation_keys_amount) {
            txin.assetIssuance.nInflationKeys.SetToAmount(*input.m_issuance_inflation_keys_amount);
        } else {
            txin.assetIssuance.nInflationKeys.SetNull();
        }
        if (!input.m_issuance_rangeproof.empty()) {
            txinwit.vchIssuanceAmountRangeproof = input.m_issuance_rangeproof;
        }
        if (!input.m_issuance_inflation_keys_rangeproof.empty()) {
            txinwit.vchInflationKeysRangeproof = input.m_issuance_inflation_keys_rangeproof;
        }
    }

    // This is a convenience/usability check -- it's not invalid to sign an unbalanced transaction, but it's easy to shoot yourself in the foot.
    if (!imbalance_ok) {
        // Get UTXOs for all inputs, to check that amounts balance before signing.
        std::vector<CTxOut> inputs_utxos;
        for (const PSBTInput& input : psbtx.inputs) {
            CTxOut utxo;
            if (!input.GetUTXO(utxo)) {
                return TransactionError::UTXOS_MISSING_BALANCE_CHECK;
            }
            inputs_utxos.push_back(utxo);
        }

        CTransaction tx_tmp(tx);
        if (!VerifyAmounts(inputs_utxos, tx_tmp, nullptr, false)) {
            return TransactionError::VALUE_IMBALANCE;
        }
    }

    // ELEMENTS: precompute transaction data only after munging is done
    const PrecomputedTransactionData txdata = PrecomputePSBTData(psbtx);
    for (ScriptPubKeyMan* spk_man : GetAllScriptPubKeyMans()) {
        int n_signed_this_spkm = 0;
        // ELEMENTS: Here we _only_ sign, and do not e.g. fill in key origin data.
        TransactionError res = spk_man->FillPSBT(psbtx, txdata, sighash_type, sign, bip32derivs, &n_signed_this_spkm, finalize);
        if (res != TransactionError::OK) {
            return res;
        }

        if (n_signed) {
            (*n_signed) += n_signed_this_spkm;
        }
    }

    // Complete if every input is now signed
    complete = true;
    for (const auto& input : psbtx.inputs) {
        complete &= PSBTInputSigned(input);
    }

    return TransactionError::OK;
}

// This function remains for backwards compatibility. It will not succeed in Elements unless everything involved is non-blinded.
TransactionError CWallet::FillPSBT(PartiallySignedTransaction& psbtx, bool& complete, int sighash_type, bool sign, bool bip32derivs, bool imbalance_ok, size_t* n_signed, bool include_explicit, bool finalize) const
{
    complete = false;
    TransactionError te;
    te = FillPSBTData(psbtx, bip32derivs, include_explicit);
    if (te != TransactionError::OK) {
        return te;
    }
    // For backwards compatibility, do not check if amounts balance before signing in this case.
    te = SignPSBT(psbtx, complete, sighash_type, sign, imbalance_ok, bip32derivs, n_signed, finalize);
    if (te != TransactionError::OK) {
        return te;
    }
    return TransactionError::OK;
}

SigningResult CWallet::SignMessage(const std::string& message, const PKHash& pkhash, std::string& str_sig) const
{
    SignatureData sigdata;
    CScript script_pub_key = GetScriptForDestination(pkhash);
    for (const auto& spk_man_pair : m_spk_managers) {
        if (spk_man_pair.second->CanProvide(script_pub_key, sigdata)) {
            return spk_man_pair.second->SignMessage(message, pkhash, str_sig);
        }
    }
    return SigningResult::PRIVATE_KEY_NOT_AVAILABLE;
}

OutputType CWallet::TransactionChangeType(const std::optional<OutputType>& change_type, const std::vector<CRecipient>& vecSend) const
{
    // If -changetype is specified, always use that change type.
    if (change_type) {
        return *change_type;
    }

    // if m_default_address_type is legacy, use legacy address as change.
    if (m_default_address_type == OutputType::LEGACY) {
        return OutputType::LEGACY;
    }

    bool any_tr{false};
    bool any_wpkh{false};
    bool any_sh{false};
    bool any_pkh{false};

    for (const auto& recipient : vecSend) {
        std::vector<std::vector<uint8_t>> dummy;
        const TxoutType type{Solver(recipient.scriptPubKey, dummy)};
        if (type == TxoutType::WITNESS_V1_TAPROOT) {
            any_tr = true;
        } else if (type == TxoutType::WITNESS_V0_KEYHASH) {
            any_wpkh = true;
        } else if (type == TxoutType::SCRIPTHASH) {
            any_sh = true;
        } else if (type == TxoutType::PUBKEYHASH) {
            any_pkh = true;
        }
    }

    const bool has_bech32m_spkman(GetScriptPubKeyMan(OutputType::BECH32M, /*internal=*/true));
    if (has_bech32m_spkman && any_tr) {
        // Currently tr is the only type supported by the BECH32M spkman
        return OutputType::BECH32M;
    }
    const bool has_bech32_spkman(GetScriptPubKeyMan(OutputType::BECH32, /*internal=*/true));
    if (has_bech32_spkman && any_wpkh) {
        // Currently wpkh is the only type supported by the BECH32 spkman
        return OutputType::BECH32;
    }
    const bool has_p2sh_segwit_spkman(GetScriptPubKeyMan(OutputType::P2SH_SEGWIT, /*internal=*/true));
    if (has_p2sh_segwit_spkman && any_sh) {
        // Currently sh_wpkh is the only type supported by the P2SH_SEGWIT spkman
        // As of 2021 about 80% of all SH are wrapping WPKH, so use that
        return OutputType::P2SH_SEGWIT;
    }
    const bool has_legacy_spkman(GetScriptPubKeyMan(OutputType::LEGACY, /*internal=*/true));
    if (has_legacy_spkman && any_pkh) {
        // Currently pkh is the only type supported by the LEGACY spkman
        return OutputType::LEGACY;
    }

    if (has_bech32m_spkman) {
        return OutputType::BECH32M;
    }
    if (has_bech32_spkman) {
        return OutputType::BECH32;
    }
    // else use m_default_address_type for change
    return m_default_address_type;
}

void CWallet::CommitTransaction(CTransactionRef tx, mapValue_t mapValue, std::vector<std::pair<std::string, std::string>> orderForm, const BlindDetails* blind_details)
{
    LOCK(cs_wallet);
    WalletLogPrintf("CommitTransaction:\n%s", tx->ToString()); /* Continued */

    // Add tx to wallet, because if it has change it's also ours,
    // otherwise just for transaction history.
    AddToWallet(tx, TxStateInactive{}, [&](CWalletTx& wtx, bool new_tx) {
        CHECK_NONFATAL(wtx.mapValue.empty());
        CHECK_NONFATAL(wtx.vOrderForm.empty());
        wtx.mapValue = std::move(mapValue);
        wtx.vOrderForm = std::move(orderForm);
        wtx.fTimeReceivedIsTxTime = true;
        wtx.fFromMe = true;
        // ELEMENTS: Write down blinding information
        if (blind_details) {
            assert(blind_details->o_amounts.size() == wtx.tx->vout.size());
            assert(blind_details->o_asset_blinds.size() == wtx.tx->vout.size());
            assert(blind_details->o_amount_blinds.size() == wtx.tx->vout.size());
            for (unsigned int i = 0; i < blind_details->o_amounts.size(); i++) {
                wtx.SetBlindingData(i, blind_details->o_pubkeys[i], blind_details->o_amounts[i], blind_details->o_amount_blinds[i], blind_details->o_assets[i], blind_details->o_asset_blinds[i]);
            }
        }
        return true;
    });

    // Notify that old coins are spent
    for (const CTxIn& txin : tx->vin) {
        // ELEMENTS: Pegins are not in our UTXO set.
        if (txin.m_is_pegin)
            continue;

        CWalletTx &coin = mapWallet.at(txin.prevout.hash);
        coin.MarkDirty(*this);
        NotifyTransactionChanged(coin.GetHash(), CT_UPDATED);
    }

    // Get the inserted-CWalletTx from mapWallet so that the
    // wtx cached mempool state is updated correctly
    CWalletTx& wtx = mapWallet.at(tx->GetHash());

    if (!fBroadcastTransactions) {
        // Don't submit tx to the mempool
        return;
    }

    std::string err_string;
    if (!SubmitTxMemoryPoolAndRelay(wtx, err_string, true)) {
        WalletLogPrintf("CommitTransaction(): Transaction cannot be broadcast immediately, %s\n", err_string);
        // TODO: if we expect the failure to be long term or permanent, instead delete wtx from the wallet and return failure.
    }
}

DBErrors CWallet::LoadWallet()
{
    LOCK(cs_wallet);

    DBErrors nLoadWalletRet = WalletBatch(GetDatabase()).LoadWallet(this);
    if (nLoadWalletRet == DBErrors::NEED_REWRITE)
    {
        if (GetDatabase().Rewrite("\x04pool"))
        {
            for (const auto& spk_man_pair : m_spk_managers) {
                spk_man_pair.second->RewriteDB();
            }
        }
    }

    if (m_spk_managers.empty()) {
        assert(m_external_spk_managers.empty());
        assert(m_internal_spk_managers.empty());
    }

    return nLoadWalletRet;
}

DBErrors CWallet::ZapSelectTx(std::vector<uint256>& vHashIn, std::vector<uint256>& vHashOut)
{
    AssertLockHeld(cs_wallet);
    DBErrors nZapSelectTxRet = WalletBatch(GetDatabase()).ZapSelectTx(vHashIn, vHashOut);
    for (const uint256& hash : vHashOut) {
        const auto& it = mapWallet.find(hash);
        wtxOrdered.erase(it->second.m_it_wtxOrdered);
        for (const auto& txin : it->second.tx->vin)
            mapTxSpends.erase(txin.prevout);
        mapWallet.erase(it);
        NotifyTransactionChanged(hash, CT_DELETED);
    }

    if (nZapSelectTxRet == DBErrors::NEED_REWRITE)
    {
        if (GetDatabase().Rewrite("\x04pool"))
        {
            for (const auto& spk_man_pair : m_spk_managers) {
                spk_man_pair.second->RewriteDB();
            }
        }
    }

    if (nZapSelectTxRet != DBErrors::LOAD_OK)
        return nZapSelectTxRet;

    MarkDirty();

    return DBErrors::LOAD_OK;
}

bool CWallet::SetAddressBookWithDB(WalletBatch& batch, const CTxDestination& address, const std::string& strName, const std::string& strPurpose)
{
    bool fUpdated = false;
    bool is_mine;
    {
        LOCK(cs_wallet);
        std::map<CTxDestination, CAddressBookData>::iterator mi = m_address_book.find(address);
        fUpdated = (mi != m_address_book.end() && !mi->second.IsChange());
        m_address_book[address].SetLabel(strName);
        if (!strPurpose.empty()) /* update purpose only if requested */
            m_address_book[address].purpose = strPurpose;
        is_mine = IsMine(address) != ISMINE_NO;
    }
    NotifyAddressBookChanged(address, strName, is_mine,
                             strPurpose, (fUpdated ? CT_UPDATED : CT_NEW));
    if (!strPurpose.empty() && !batch.WritePurpose(EncodeDestination(address), strPurpose))
        return false;
    return batch.WriteName(EncodeDestination(address), strName);
}

bool CWallet::SetAddressBook(const CTxDestination& address, const std::string& strName, const std::string& strPurpose)
{
    WalletBatch batch(GetDatabase());
    return SetAddressBookWithDB(batch, address, strName, strPurpose);
}

bool CWallet::DelAddressBook(const CTxDestination& address)
{
    bool is_mine;
    WalletBatch batch(GetDatabase());
    {
        LOCK(cs_wallet);
        // If we want to delete receiving addresses, we need to take care that DestData "used" (and possibly newer DestData) gets preserved (and the "deleted" address transformed into a change entry instead of actually being deleted)
        // NOTE: This isn't a problem for sending addresses because they never have any DestData yet!
        // When adding new DestData, it should be considered here whether to retain or delete it (or move it?).
        if (IsMine(address)) {
            WalletLogPrintf("%s called with IsMine address, NOT SUPPORTED. Please report this bug! %s\n", __func__, PACKAGE_BUGREPORT);
            return false;
        }
        // Delete destdata tuples associated with address
        std::string strAddress = EncodeDestination(address);
        for (const std::pair<const std::string, std::string> &item : m_address_book[address].destdata)
        {
            batch.EraseDestData(strAddress, item.first);
        }
        m_address_book.erase(address);
        is_mine = IsMine(address) != ISMINE_NO;
    }

    NotifyAddressBookChanged(address, "", is_mine, "", CT_DELETED);

    batch.ErasePurpose(EncodeDestination(address));
    return batch.EraseName(EncodeDestination(address));
}

size_t CWallet::KeypoolCountExternalKeys() const
{
    AssertLockHeld(cs_wallet);

    auto legacy_spk_man = GetLegacyScriptPubKeyMan();
    if (legacy_spk_man) {
        return legacy_spk_man->KeypoolCountExternalKeys();
    }

    unsigned int count = 0;
    for (auto spk_man : m_external_spk_managers) {
        count += spk_man.second->GetKeyPoolSize();
    }

    return count;
}

unsigned int CWallet::GetKeyPoolSize() const
{
    AssertLockHeld(cs_wallet);

    unsigned int count = 0;
    for (auto spk_man : GetActiveScriptPubKeyMans()) {
        count += spk_man->GetKeyPoolSize();
    }
    return count;
}

bool CWallet::TopUpKeyPool(unsigned int kpSize)
{
    LOCK(cs_wallet);
    bool res = true;
    for (auto spk_man : GetActiveScriptPubKeyMans()) {
        res &= spk_man->TopUp(kpSize);
    }
    return res;
}

/// ELEMENTS: get PAK online key
bool CWallet::GetOnlinePakKey(CPubKey& online_pubkey, std::string& error)
{
    LegacyScriptPubKeyMan* spk_man = GetLegacyScriptPubKeyMan();
    if (spk_man) {
        return spk_man->GetOnlinePakKey(online_pubkey, error);
    }
    return false;
}
/// end ELEMENTS

bool CWallet::GetNewDestination(const OutputType type, const std::string label, CTxDestination& dest, bilingual_str& error, bool add_blinding_key)
{
    LOCK(cs_wallet);
    error.clear();
    bool result = false;
    auto spk_man = GetScriptPubKeyMan(type, false /* internal */);
    if (spk_man) {
        spk_man->TopUp();
        result = spk_man->GetNewDestination(type, dest, error);
        if (add_blinding_key) {
            CPubKey blinding_pubkey = GetBlindingPubKey(GetScriptForDestination(dest));
            std::visit(SetBlindingPubKeyVisitor(blinding_pubkey), dest);
        }
    } else {
        error = strprintf(_("Error: No %s addresses available."), FormatOutputType(type));
    }
    if (result) {
        SetAddressBook(dest, label, "receive");
    }

    return result;
}

bool CWallet::GetNewChangeDestination(const OutputType type, CTxDestination& dest, bilingual_str& error, bool add_blinding_key)
{
    LOCK(cs_wallet);
    error.clear();

    ReserveDestination reservedest(this, type);
    if (!reservedest.GetReservedDestination(dest, true, error)) {
        return false;
    }
    if (add_blinding_key) {
        CPubKey blinding_pubkey = GetBlindingPubKey(GetScriptForDestination(dest));
        reservedest.SetBlindingPubKey(blinding_pubkey, dest);
    }

    reservedest.KeepDestination();
    return true;
}

std::optional<int64_t> CWallet::GetOldestKeyPoolTime() const
{
    LOCK(cs_wallet);
    if (m_spk_managers.empty()) {
        return std::nullopt;
    }

    std::optional<int64_t> oldest_key{std::numeric_limits<int64_t>::max()};
    for (const auto& spk_man_pair : m_spk_managers) {
        oldest_key = std::min(oldest_key, spk_man_pair.second->GetOldestKeyPoolTime());
    }
    return oldest_key;
}

void CWallet::MarkDestinationsDirty(const std::set<CTxDestination>& destinations) {
    for (auto& entry : mapWallet) {
        CWalletTx& wtx = entry.second;
        if (wtx.m_is_cache_empty) continue;
        for (unsigned int i = 0; i < wtx.tx->vout.size(); i++) {
            CTxDestination dst;
            if (ExtractDestination(wtx.tx->vout[i].scriptPubKey, dst) && destinations.count(dst)) {
                wtx.MarkDirty(*this);
                break;
            }
        }
    }
}

std::set<CTxDestination> CWallet::GetLabelAddresses(const std::string& label) const
{
    AssertLockHeld(cs_wallet);
    std::set<CTxDestination> result;
    for (const std::pair<const CTxDestination, CAddressBookData>& item : m_address_book)
    {
        if (item.second.IsChange()) continue;
        const CTxDestination& address = item.first;
        const std::string& strName = item.second.GetLabel();
        if (strName == label)
            result.insert(address);
    }
    return result;
}

bool ReserveDestination::GetReservedDestination(CTxDestination& dest, bool internal, bilingual_str& error)
{
    m_spk_man = pwallet->GetScriptPubKeyMan(type, internal);
    if (!m_spk_man) {
        error = strprintf(_("Error: No %s addresses available."), FormatOutputType(type));
        return false;
    }


    if (nIndex == -1)
    {
        m_spk_man->TopUp();

        CKeyPool keypool;
        if (!m_spk_man->GetReservedDestination(type, internal, address, nIndex, keypool, error)) {
            return false;
        }
        fInternal = keypool.fInternal;
    }
    dest = address;
    return true;
}

void ReserveDestination::SetBlindingPubKey(const CPubKey& blinding_pubkey, CTxDestination& dest)
{
    std::visit(SetBlindingPubKeyVisitor(blinding_pubkey), address);
    dest = address;
}

void ReserveDestination::KeepDestination()
{
    if (nIndex != -1) {
        m_spk_man->KeepDestination(nIndex, type);
    }
    nIndex = -1;
    address = CNoDestination();
}

void ReserveDestination::ReturnDestination()
{
    if (nIndex != -1) {
        m_spk_man->ReturnDestination(nIndex, fInternal, address);
    }
    nIndex = -1;
    address = CNoDestination();
}

bool CWallet::DisplayAddress(const CTxDestination& dest)
{
    CScript scriptPubKey = GetScriptForDestination(dest);
    for (const auto& spk_man : GetScriptPubKeyMans(scriptPubKey)) {
        auto signer_spk_man = dynamic_cast<ExternalSignerScriptPubKeyMan *>(spk_man);
        if (signer_spk_man == nullptr) {
            continue;
        }
        ExternalSigner signer = ExternalSignerScriptPubKeyMan::GetExternalSigner();
        return signer_spk_man->DisplayAddress(scriptPubKey, signer);
    }
    return false;
}

bool CWallet::LockCoin(const COutPoint& output, WalletBatch* batch)
{
    AssertLockHeld(cs_wallet);
    setLockedCoins.insert(output);
    if (batch) {
        return batch->WriteLockedUTXO(output);
    }
    return true;
}

bool CWallet::UnlockCoin(const COutPoint& output, WalletBatch* batch)
{
    AssertLockHeld(cs_wallet);
    bool was_locked = setLockedCoins.erase(output);
    if (batch && was_locked) {
        return batch->EraseLockedUTXO(output);
    }
    return true;
}

bool CWallet::UnlockAllCoins()
{
    AssertLockHeld(cs_wallet);
    bool success = true;
    WalletBatch batch(GetDatabase());
    for (auto it = setLockedCoins.begin(); it != setLockedCoins.end(); ++it) {
        success &= batch.EraseLockedUTXO(*it);
    }
    setLockedCoins.clear();
    return success;
}

bool CWallet::IsLockedCoin(uint256 hash, unsigned int n) const
{
    AssertLockHeld(cs_wallet);
    COutPoint outpt(hash, n);

    return (setLockedCoins.count(outpt) > 0);
}

void CWallet::ListLockedCoins(std::vector<COutPoint>& vOutpts) const
{
    AssertLockHeld(cs_wallet);
    for (std::set<COutPoint>::iterator it = setLockedCoins.begin();
         it != setLockedCoins.end(); it++) {
        COutPoint outpt = (*it);
        vOutpts.push_back(outpt);
    }
}

/** @} */ // end of Actions

void CWallet::GetKeyBirthTimes(std::map<CKeyID, int64_t>& mapKeyBirth) const {
    AssertLockHeld(cs_wallet);
    mapKeyBirth.clear();

    // map in which we'll infer heights of other keys
    std::map<CKeyID, const TxStateConfirmed*> mapKeyFirstBlock;
    TxStateConfirmed max_confirm{uint256{}, /*height=*/-1, /*index=*/-1};
    max_confirm.confirmed_block_height = GetLastBlockHeight() > 144 ? GetLastBlockHeight() - 144 : 0; // the tip can be reorganized; use a 144-block safety margin
    CHECK_NONFATAL(chain().findAncestorByHeight(GetLastBlockHash(), max_confirm.confirmed_block_height, FoundBlock().hash(max_confirm.confirmed_block_hash)));

    {
        LegacyScriptPubKeyMan* spk_man = GetLegacyScriptPubKeyMan();
        assert(spk_man != nullptr);
        LOCK(spk_man->cs_KeyStore);

        // get birth times for keys with metadata
        for (const auto& entry : spk_man->mapKeyMetadata) {
            if (entry.second.nCreateTime) {
                mapKeyBirth[entry.first] = entry.second.nCreateTime;
            }
        }

        // Prepare to infer birth heights for keys without metadata
        for (const CKeyID &keyid : spk_man->GetKeys()) {
            if (mapKeyBirth.count(keyid) == 0)
                mapKeyFirstBlock[keyid] = &max_confirm;
        }

        // if there are no such keys, we're done
        if (mapKeyFirstBlock.empty())
            return;

        // find first block that affects those keys, if there are any left
        for (const auto& entry : mapWallet) {
            // iterate over all wallet transactions...
            const CWalletTx &wtx = entry.second;
            if (auto* conf = wtx.state<TxStateConfirmed>()) {
                // ... which are already in a block
                for (const CTxOut &txout : wtx.tx->vout) {
                    // iterate over all their outputs
                    for (const auto &keyid : GetAffectedKeys(txout.scriptPubKey, *spk_man)) {
                        // ... and all their affected keys
                        auto rit = mapKeyFirstBlock.find(keyid);
                        if (rit != mapKeyFirstBlock.end() && conf->confirmed_block_height < rit->second->confirmed_block_height) {
                            rit->second = conf;
                        }
                    }
                }
            }
        }
    }

    // Extract block timestamps for those keys
    for (const auto& entry : mapKeyFirstBlock) {
        int64_t block_time;
        CHECK_NONFATAL(chain().findBlock(entry.second->confirmed_block_hash, FoundBlock().time(block_time)));
        mapKeyBirth[entry.first] = block_time - TIMESTAMP_WINDOW; // block times can be 2h off
    }
}

/**
 * Compute smart timestamp for a transaction being added to the wallet.
 *
 * Logic:
 * - If sending a transaction, assign its timestamp to the current time.
 * - If receiving a transaction outside a block, assign its timestamp to the
 *   current time.
 * - If receiving a transaction during a rescanning process, assign all its
 *   (not already known) transactions' timestamps to the block time.
 * - If receiving a block with a future timestamp, assign all its (not already
 *   known) transactions' timestamps to the current time.
 * - If receiving a block with a past timestamp, before the most recent known
 *   transaction (that we care about), assign all its (not already known)
 *   transactions' timestamps to the same timestamp as that most-recent-known
 *   transaction.
 * - If receiving a block with a past timestamp, but after the most recent known
 *   transaction, assign all its (not already known) transactions' timestamps to
 *   the block time.
 *
 * For more information see CWalletTx::nTimeSmart,
 * https://bitcointalk.org/?topic=54527, or
 * https://github.com/bitcoin/bitcoin/pull/1393.
 */
unsigned int CWallet::ComputeTimeSmart(const CWalletTx& wtx, bool rescanning_old_block) const
{
    std::optional<uint256> block_hash;
    if (auto* conf = wtx.state<TxStateConfirmed>()) {
        block_hash = conf->confirmed_block_hash;
    } else if (auto* conf = wtx.state<TxStateConflicted>()) {
        block_hash = conf->conflicting_block_hash;
    }

    unsigned int nTimeSmart = wtx.nTimeReceived;
    if (block_hash) {
        int64_t blocktime;
        int64_t block_max_time;
        if (chain().findBlock(*block_hash, FoundBlock().time(blocktime).maxTime(block_max_time))) {
            if (rescanning_old_block) {
                nTimeSmart = block_max_time;
            } else {
                int64_t latestNow = wtx.nTimeReceived;
                int64_t latestEntry = 0;

                // Tolerate times up to the last timestamp in the wallet not more than 5 minutes into the future
                int64_t latestTolerated = latestNow + 300;
                const TxItems& txOrdered = wtxOrdered;
                for (auto it = txOrdered.rbegin(); it != txOrdered.rend(); ++it) {
                    CWalletTx* const pwtx = it->second;
                    if (pwtx == &wtx) {
                        continue;
                    }
                    int64_t nSmartTime;
                    nSmartTime = pwtx->nTimeSmart;
                    if (!nSmartTime) {
                        nSmartTime = pwtx->nTimeReceived;
                    }
                    if (nSmartTime <= latestTolerated) {
                        latestEntry = nSmartTime;
                        if (nSmartTime > latestNow) {
                            latestNow = nSmartTime;
                        }
                        break;
                    }
                }

                nTimeSmart = std::max(latestEntry, std::min(blocktime, latestNow));
            }
        } else {
            WalletLogPrintf("%s: found %s in block %s not in index\n", __func__, wtx.GetHash().ToString(), block_hash->ToString());
        }
    }
    return nTimeSmart;
}

bool CWallet::SetAddressUsed(WalletBatch& batch, const CTxDestination& dest, bool used)
{
    const std::string key{"used"};
    if (std::get_if<CNoDestination>(&dest))
        return false;

    if (!used) {
        if (auto* data = util::FindKey(m_address_book, dest)) data->destdata.erase(key);
        return batch.EraseDestData(EncodeDestination(dest), key);
    }

    const std::string value{"1"};
    m_address_book[dest].destdata.insert(std::make_pair(key, value));
    return batch.WriteDestData(EncodeDestination(dest), key, value);
}

void CWallet::LoadDestData(const CTxDestination &dest, const std::string &key, const std::string &value)
{
    m_address_book[dest].destdata.insert(std::make_pair(key, value));
}

bool CWallet::IsAddressUsed(const CTxDestination& dest) const
{
    const std::string key{"used"};
    std::map<CTxDestination, CAddressBookData>::const_iterator i = m_address_book.find(dest);
    if(i != m_address_book.end())
    {
        CAddressBookData::StringMap::const_iterator j = i->second.destdata.find(key);
        if(j != i->second.destdata.end())
        {
            return true;
        }
    }
    return false;
}

std::vector<std::string> CWallet::GetAddressReceiveRequests() const
{
    const std::string prefix{"rr"};
    std::vector<std::string> values;
    for (const auto& address : m_address_book) {
        for (const auto& data : address.second.destdata) {
            if (!data.first.compare(0, prefix.size(), prefix)) {
                values.emplace_back(data.second);
            }
        }
    }
    return values;
}

bool CWallet::SetAddressReceiveRequest(WalletBatch& batch, const CTxDestination& dest, const std::string& id, const std::string& value)
{
    const std::string key{"rr" + id}; // "rr" prefix = "receive request" in destdata
    CAddressBookData& data = m_address_book.at(dest);
    if (value.empty()) {
        if (!batch.EraseDestData(EncodeDestination(dest), key)) return false;
        data.destdata.erase(key);
    } else {
        if (!batch.WriteDestData(EncodeDestination(dest), key, value)) return false;
        data.destdata[key] = value;
    }
    return true;
}

std::unique_ptr<WalletDatabase> MakeWalletDatabase(const std::string& name, const DatabaseOptions& options, DatabaseStatus& status, bilingual_str& error_string)
{
    // Do some checking on wallet path. It should be either a:
    //
    // 1. Path where a directory can be created.
    // 2. Path to an existing directory.
    // 3. Path to a symlink to a directory.
    // 4. For backwards compatibility, the name of a data file in -walletdir.
    const fs::path wallet_path = fsbridge::AbsPathJoin(GetWalletDir(), fs::PathFromString(name));
    fs::file_type path_type = fs::symlink_status(wallet_path).type();
    if (!(path_type == fs::file_type::not_found || path_type == fs::file_type::directory ||
          (path_type == fs::file_type::symlink && fs::is_directory(wallet_path)) ||
          (path_type == fs::file_type::regular && fs::PathFromString(name).filename() == fs::PathFromString(name)))) {
        error_string = Untranslated(strprintf(
              "Invalid -wallet path '%s'. -wallet path should point to a directory where wallet.dat and "
              "database/log.?????????? files can be stored, a location where such a directory could be created, "
              "or (for backwards compatibility) the name of an existing data file in -walletdir (%s)",
              name, fs::quoted(fs::PathToString(GetWalletDir()))));
        status = DatabaseStatus::FAILED_BAD_PATH;
        return nullptr;
    }
    return MakeDatabase(wallet_path, options, status, error_string);
}

std::shared_ptr<CWallet> CWallet::Create(WalletContext& context, const std::string& name, std::unique_ptr<WalletDatabase> database, uint64_t wallet_creation_flags, bilingual_str& error, std::vector<bilingual_str>& warnings)
{
    interfaces::Chain* chain = context.chain;
    ArgsManager& args = *Assert(context.args);
    const std::string& walletFile = database->Filename();

    int64_t nStart = GetTimeMillis();
    // TODO: Can't use std::make_shared because we need a custom deleter but
    // should be possible to use std::allocate_shared.
    const std::shared_ptr<CWallet> walletInstance(new CWallet(chain, name, args, std::move(database)), ReleaseWallet);
    bool rescan_required = false;
    DBErrors nLoadWalletRet = walletInstance->LoadWallet();
    if (nLoadWalletRet != DBErrors::LOAD_OK) {
        if (nLoadWalletRet == DBErrors::CORRUPT) {
            error = strprintf(_("Error loading %s: Wallet corrupted"), walletFile);
            return nullptr;
        }
        else if (nLoadWalletRet == DBErrors::NONCRITICAL_ERROR)
        {
            warnings.push_back(strprintf(_("Error reading %s! All keys read correctly, but transaction data"
                                           " or address book entries might be missing or incorrect."),
                walletFile));
        }
        else if (nLoadWalletRet == DBErrors::TOO_NEW) {
            error = strprintf(_("Error loading %s: Wallet requires newer version of %s"), walletFile, PACKAGE_NAME);
            return nullptr;
        }
        else if (nLoadWalletRet == DBErrors::EXTERNAL_SIGNER_SUPPORT_REQUIRED) {
            error = strprintf(_("Error loading %s: External signer wallet being loaded without external signer support compiled"), walletFile);
            return nullptr;
        }
        else if (nLoadWalletRet == DBErrors::NEED_REWRITE)
        {
            error = strprintf(_("Wallet needed to be rewritten: restart %s to complete"), PACKAGE_NAME);
            return nullptr;
        } else if (nLoadWalletRet == DBErrors::NEED_RESCAN) {
            warnings.push_back(strprintf(_("Error reading %s! Transaction data may be missing or incorrect."
                                           " Rescanning wallet."), walletFile));
            rescan_required = true;
        }
        else {
            error = strprintf(_("Error loading %s"), walletFile);
            return nullptr;
        }
    }

    // This wallet is in its first run if there are no ScriptPubKeyMans and it isn't blank or no privkeys
    const bool fFirstRun = walletInstance->m_spk_managers.empty() &&
                     !walletInstance->IsWalletFlagSet(WALLET_FLAG_DISABLE_PRIVATE_KEYS) &&
                     !walletInstance->IsWalletFlagSet(WALLET_FLAG_BLANK_WALLET);
    if (fFirstRun)
    {
        // ensure this wallet.dat can only be opened by clients supporting HD with chain split and expects no default key
        walletInstance->SetMinVersion(FEATURE_LATEST);

        walletInstance->AddWalletFlags(wallet_creation_flags);

        // Only create LegacyScriptPubKeyMan when not descriptor wallet
        if (!walletInstance->IsWalletFlagSet(WALLET_FLAG_DESCRIPTORS)) {
            walletInstance->SetupLegacyScriptPubKeyMan();
        }

        if ((wallet_creation_flags & WALLET_FLAG_EXTERNAL_SIGNER) || !(wallet_creation_flags & (WALLET_FLAG_DISABLE_PRIVATE_KEYS | WALLET_FLAG_BLANK_WALLET))) {
            LOCK(walletInstance->cs_wallet);
            if (walletInstance->IsWalletFlagSet(WALLET_FLAG_DESCRIPTORS)) {
                walletInstance->SetupDescriptorScriptPubKeyMans();
                // SetupDescriptorScriptPubKeyMans already calls SetupGeneration for us so we don't need to call SetupGeneration separately
            } else {
                // Legacy wallets need SetupGeneration here.
                for (auto spk_man : walletInstance->GetActiveScriptPubKeyMans()) {
                    if (!spk_man->SetupGeneration()) {
                        error = _("Unable to generate initial keys");
                        return nullptr;
                    }
                }
            }
        }

        if (chain) {
            walletInstance->chainStateFlushed(chain->getTipLocator());
        }
    } else if (wallet_creation_flags & WALLET_FLAG_DISABLE_PRIVATE_KEYS) {
        // Make it impossible to disable private keys after creation
        error = strprintf(_("Error loading %s: Private keys can only be disabled during creation"), walletFile);
        return NULL;
    } else if (walletInstance->IsWalletFlagSet(WALLET_FLAG_DISABLE_PRIVATE_KEYS)) {
        for (auto spk_man : walletInstance->GetActiveScriptPubKeyMans()) {
            if (spk_man->HavePrivateKeys()) {
                warnings.push_back(strprintf(_("Warning: Private keys detected in wallet {%s} with disabled private keys"), walletFile));
                break;
            }
        }
    }

    if (!args.GetArg("-addresstype", "").empty()) {
        std::optional<OutputType> parsed = ParseOutputType(args.GetArg("-addresstype", ""));
        if (!parsed) {
            error = strprintf(_("Unknown address type '%s'"), args.GetArg("-addresstype", ""));
            return nullptr;
        }
        walletInstance->m_default_address_type = parsed.value();
    }

    if (!args.GetArg("-changetype", "").empty()) {
        std::optional<OutputType> parsed = ParseOutputType(args.GetArg("-changetype", ""));
        if (!parsed) {
            error = strprintf(_("Unknown change type '%s'"), args.GetArg("-changetype", ""));
            return nullptr;
        }
        walletInstance->m_default_change_type = parsed.value();
    }

    if (args.IsArgSet("-mintxfee")) {
        std::optional<CAmount> min_tx_fee = ParseMoney(args.GetArg("-mintxfee", ""));
        if (!min_tx_fee || min_tx_fee.value() == 0) {
            error = AmountErrMsg("mintxfee", args.GetArg("-mintxfee", ""));
            return nullptr;
        } else if (min_tx_fee.value() > HIGH_TX_FEE_PER_KB) {
            warnings.push_back(AmountHighWarn("-mintxfee") + Untranslated(" ") +
                               _("This is the minimum transaction fee you pay on every transaction."));
        }

        walletInstance->m_min_fee = CFeeRate{min_tx_fee.value()};
    }

    if (args.IsArgSet("-maxapsfee")) {
        const std::string max_aps_fee{args.GetArg("-maxapsfee", "")};
        if (max_aps_fee == "-1") {
            walletInstance->m_max_aps_fee = -1;
        } else if (std::optional<CAmount> max_fee = ParseMoney(max_aps_fee)) {
            if (max_fee.value() > HIGH_APS_FEE) {
                warnings.push_back(AmountHighWarn("-maxapsfee") + Untranslated(" ") +
                                  _("This is the maximum transaction fee you pay (in addition to the normal fee) to prioritize partial spend avoidance over regular coin selection."));
            }
            walletInstance->m_max_aps_fee = max_fee.value();
        } else {
            error = AmountErrMsg("maxapsfee", max_aps_fee);
            return nullptr;
        }
    }

    if (args.IsArgSet("-fallbackfee")) {
        std::optional<CAmount> fallback_fee = ParseMoney(args.GetArg("-fallbackfee", ""));
        if (!fallback_fee) {
            error = strprintf(_("Invalid amount for -fallbackfee=<amount>: '%s'"), args.GetArg("-fallbackfee", ""));
            return nullptr;
        } else if (fallback_fee.value() > HIGH_TX_FEE_PER_KB) {
            warnings.push_back(AmountHighWarn("-fallbackfee") + Untranslated(" ") +
                               _("This is the transaction fee you may pay when fee estimates are not available."));
        }
        walletInstance->m_fallback_fee = CFeeRate(fallback_fee.value());
    } else {
        // ELEMENTS: re-enable fallbackfee at 0.1 sat/byte
        walletInstance->m_fallback_fee = CFeeRate(100);
    }

    // Disable fallback fee in case value was set to 0, enable if non-null value
    walletInstance->m_allow_fallback_fee = walletInstance->m_fallback_fee.GetFeePerK() != 0;

    if (args.IsArgSet("-discardfee")) {
        std::optional<CAmount> discard_fee = ParseMoney(args.GetArg("-discardfee", ""));
        if (!discard_fee) {
            error = strprintf(_("Invalid amount for -discardfee=<amount>: '%s'"), args.GetArg("-discardfee", ""));
            return nullptr;
        } else if (discard_fee.value() > HIGH_TX_FEE_PER_KB) {
            warnings.push_back(AmountHighWarn("-discardfee") + Untranslated(" ") +
                               _("This is the transaction fee you may discard if change is smaller than dust at this level"));
        }
        walletInstance->m_discard_rate = CFeeRate{discard_fee.value()};
    }

    if (args.IsArgSet("-paytxfee")) {
        std::optional<CAmount> pay_tx_fee = ParseMoney(args.GetArg("-paytxfee", ""));
        if (!pay_tx_fee) {
            error = AmountErrMsg("paytxfee", args.GetArg("-paytxfee", ""));
            return nullptr;
        } else if (pay_tx_fee.value() > HIGH_TX_FEE_PER_KB) {
            warnings.push_back(AmountHighWarn("-paytxfee") + Untranslated(" ") +
                               _("This is the transaction fee you will pay if you send a transaction."));
        }

        walletInstance->m_pay_tx_fee = CFeeRate{pay_tx_fee.value(), 1000};

        if (chain && walletInstance->m_pay_tx_fee < chain->relayMinFee()) {
            error = strprintf(_("Invalid amount for -paytxfee=<amount>: '%s' (must be at least %s)"),
                args.GetArg("-paytxfee", ""), chain->relayMinFee().ToString());
            return nullptr;
        }
    }

    if (args.IsArgSet("-maxtxfee")) {
        std::optional<CAmount> max_fee = ParseMoney(args.GetArg("-maxtxfee", ""));
        if (!max_fee) {
            error = AmountErrMsg("maxtxfee", args.GetArg("-maxtxfee", ""));
            return nullptr;
        } else if (max_fee.value() > HIGH_MAX_TX_FEE) {
            warnings.push_back(_("-maxtxfee is set very high! Fees this large could be paid on a single transaction."));
        }

        if (chain && CFeeRate{max_fee.value(), 1000} < chain->relayMinFee()) {
            error = strprintf(_("Invalid amount for -maxtxfee=<amount>: '%s' (must be at least the minrelay fee of %s to prevent stuck transactions)"),
                args.GetArg("-maxtxfee", ""), chain->relayMinFee().ToString());
            return nullptr;
        }

        walletInstance->m_default_max_tx_fee = max_fee.value();
    }

    if (args.IsArgSet("-consolidatefeerate")) {
        if (std::optional<CAmount> consolidate_feerate = ParseMoney(args.GetArg("-consolidatefeerate", ""))) {
            walletInstance->m_consolidate_feerate = CFeeRate(*consolidate_feerate);
        } else {
            error = AmountErrMsg("consolidatefeerate", args.GetArg("-consolidatefeerate", ""));
            return nullptr;
        }
    }

    if (chain && chain->relayMinFee().GetFeePerK() > HIGH_TX_FEE_PER_KB) {
        warnings.push_back(AmountHighWarn("-minrelaytxfee") + Untranslated(" ") +
                           _("The wallet will avoid paying less than the minimum relay fee."));
    }

    walletInstance->m_confirm_target = args.GetIntArg("-txconfirmtarget", DEFAULT_TX_CONFIRM_TARGET);
    walletInstance->m_spend_zero_conf_change = args.GetBoolArg("-spendzeroconfchange", DEFAULT_SPEND_ZEROCONF_CHANGE);
    walletInstance->m_signal_rbf = args.GetBoolArg("-walletrbf", DEFAULT_WALLET_RBF);

    walletInstance->WalletLogPrintf("Wallet completed loading in %15dms\n", GetTimeMillis() - nStart);

    // Try to top up keypool. No-op if the wallet is locked.
    walletInstance->TopUpKeyPool();

    if (chain && !AttachChain(walletInstance, *chain, rescan_required, error, warnings)) {
        return nullptr;
    }

    {
        LOCK(walletInstance->cs_wallet);
        walletInstance->SetBroadcastTransactions(args.GetBoolArg("-walletbroadcast", DEFAULT_WALLETBROADCAST));
        walletInstance->WalletLogPrintf("setKeyPool.size() = %u\n",      walletInstance->GetKeyPoolSize());
        walletInstance->WalletLogPrintf("mapWallet.size() = %u\n",       walletInstance->mapWallet.size());
        walletInstance->WalletLogPrintf("m_address_book.size() = %u\n",  walletInstance->m_address_book.size());
    }

    return walletInstance;
}

bool CWallet::AttachChain(const std::shared_ptr<CWallet>& walletInstance, interfaces::Chain& chain, const bool rescan_required, bilingual_str& error, std::vector<bilingual_str>& warnings)
{
    LOCK(walletInstance->cs_wallet);
    // allow setting the chain if it hasn't been set already but prevent changing it
    assert(!walletInstance->m_chain || walletInstance->m_chain == &chain);
    walletInstance->m_chain = &chain;

    // Register wallet with validationinterface. It's done before rescan to avoid
    // missing block connections between end of rescan and validation subscribing.
    // Because of wallet lock being hold, block connection notifications are going to
    // be pending on the validation-side until lock release. It's likely to have
    // block processing duplicata (if rescan block range overlaps with notification one)
    // but we guarantee at least than wallet state is correct after notifications delivery.
    // This is temporary until rescan and notifications delivery are unified under same
    // interface.
    walletInstance->m_chain_notifications_handler = walletInstance->chain().handleNotifications(walletInstance);

    // If rescan_required = true, rescan_height remains equal to 0
    int rescan_height = 0;
    if (!rescan_required)
    {
        WalletBatch batch(walletInstance->GetDatabase());
        CBlockLocator locator;
        if (batch.ReadBestBlock(locator)) {
            if (const std::optional<int> fork_height = chain.findLocatorFork(locator)) {
                rescan_height = *fork_height;
            }
        }
    }

    const std::optional<int> tip_height = chain.getHeight();
    if (tip_height) {
        walletInstance->m_last_block_processed = chain.getBlockHash(*tip_height);
        walletInstance->m_last_block_processed_height = *tip_height;
    } else {
        walletInstance->m_last_block_processed.SetNull();
        walletInstance->m_last_block_processed_height = -1;
    }

    if (tip_height && *tip_height != rescan_height)
    {
        if (chain.havePruned()) {
            int block_height = *tip_height;
            while (block_height > 0 && chain.haveBlockOnDisk(block_height - 1) && rescan_height != block_height) {
                --block_height;
            }

            if (rescan_height != block_height) {
                // We can't rescan beyond non-pruned blocks, stop and throw an error.
                // This might happen if a user uses an old wallet within a pruned node
                // or if they ran -disablewallet for a longer time, then decided to re-enable
                // Exit early and print an error.
                // If a block is pruned after this check, we will load the wallet,
                // but fail the rescan with a generic error.
                error = _("Prune: last wallet synchronisation goes beyond pruned data. You need to -reindex (download the whole blockchain again in case of pruned node)");
                return false;
            }
        }

        chain.initMessage(_("Rescanning…").translated);
        walletInstance->WalletLogPrintf("Rescanning last %i blocks (from block %i)...\n", *tip_height - rescan_height, rescan_height);

        // No need to read and scan block if block was created before
        // our wallet birthday (as adjusted for block time variability)
        std::optional<int64_t> time_first_key;
        for (auto spk_man : walletInstance->GetAllScriptPubKeyMans()) {
            int64_t time = spk_man->GetTimeFirstKey();
            if (!time_first_key || time < *time_first_key) time_first_key = time;
        }
        if (time_first_key) {
            chain.findFirstBlockWithTimeAndHeight(*time_first_key - TIMESTAMP_WINDOW, rescan_height, FoundBlock().height(rescan_height));
        }

        {
            WalletRescanReserver reserver(*walletInstance);
            if (!reserver.reserve() || (ScanResult::SUCCESS != walletInstance->ScanForWalletTransactions(chain.getBlockHash(rescan_height), rescan_height, {} /* max height */, reserver, true /* update */).status)) {
                error = _("Failed to rescan the wallet during initialization");
                return false;
            }
        }
        walletInstance->chainStateFlushed(chain.getTipLocator());
        walletInstance->GetDatabase().IncrementUpdateCounter();
    }

    return true;
}

const CAddressBookData* CWallet::FindAddressBookEntry(const CTxDestination& dest, bool allow_change) const
{
    const auto& address_book_it = m_address_book.find(dest);
    if (address_book_it == m_address_book.end()) return nullptr;
    if ((!allow_change) && address_book_it->second.IsChange()) {
        return nullptr;
    }
    return &address_book_it->second;
}

bool CWallet::UpgradeWallet(int version, bilingual_str& error)
{
    int prev_version = GetVersion();
    if (version == 0) {
        WalletLogPrintf("Performing wallet upgrade to %i\n", FEATURE_LATEST);
        version = FEATURE_LATEST;
    } else {
        WalletLogPrintf("Allowing wallet upgrade up to %i\n", version);
    }
    if (version < prev_version) {
        error = strprintf(_("Cannot downgrade wallet from version %i to version %i. Wallet version unchanged."), prev_version, version);
        return false;
    }

    LOCK(cs_wallet);

    // Do not upgrade versions to any version between HD_SPLIT and FEATURE_PRE_SPLIT_KEYPOOL unless already supporting HD_SPLIT
    if (!CanSupportFeature(FEATURE_HD_SPLIT) && version >= FEATURE_HD_SPLIT && version < FEATURE_PRE_SPLIT_KEYPOOL) {
        error = strprintf(_("Cannot upgrade a non HD split wallet from version %i to version %i without upgrading to support pre-split keypool. Please use version %i or no version specified."), prev_version, version, FEATURE_PRE_SPLIT_KEYPOOL);
        return false;
    }

    // Permanently upgrade to the version
    SetMinVersion(GetClosestWalletFeature(version));

    for (auto spk_man : GetActiveScriptPubKeyMans()) {
        if (!spk_man->Upgrade(prev_version, version, error)) {
            return false;
        }
    }
    return true;
}

void CWallet::postInitProcess()
{
    LOCK(cs_wallet);

    // Add wallet transactions that aren't already in a block to mempool
    // Do this here as mempool requires genesis block to be loaded
    ReacceptWalletTransactions();

    // Update wallet transactions with current mempool transactions.
    chain().requestMempoolTransactions(*this);
}

bool CWallet::BackupWallet(const std::string& strDest) const
{
    return GetDatabase().Backup(strDest);
}

CKeyPool::CKeyPool()
{
    nTime = GetTime();
    fInternal = false;
    m_pre_split = false;
}

CKeyPool::CKeyPool(const CPubKey& vchPubKeyIn, bool internalIn)
{
    nTime = GetTime();
    vchPubKey = vchPubKeyIn;
    fInternal = internalIn;
    m_pre_split = false;
}

int CWallet::GetTxDepthInMainChain(const CWalletTx& wtx) const
{
    AssertLockHeld(cs_wallet);
    if (auto* conf = wtx.state<TxStateConfirmed>()) {
        return GetLastBlockHeight() - conf->confirmed_block_height + 1;
    } else if (auto* conf = wtx.state<TxStateConflicted>()) {
        return -1 * (GetLastBlockHeight() - conf->conflicting_block_height + 1);
    } else {
        return 0;
    }
}

int CWallet::GetTxBlocksToMaturity(const CWalletTx& wtx) const
{
    if (!wtx.IsCoinBase())
        return 0;
    int chain_depth = GetTxDepthInMainChain(wtx);
    assert(chain_depth >= 0); // coinbase tx should not be conflicted
    return std::max(0, (COINBASE_MATURITY+1) - chain_depth);
}

bool CWallet::IsTxImmatureCoinBase(const CWalletTx& wtx) const
{
    // note GetBlocksToMaturity is 0 for non-coinbase tx
    return GetTxBlocksToMaturity(wtx) > 0;
}

bool CWallet::IsCrypted() const
{
    return HasEncryptionKeys();
}

bool CWallet::IsLocked() const
{
    if (!IsCrypted()) {
        return false;
    }
    LOCK(cs_wallet);
    return vMasterKey.empty();
}

bool CWallet::Lock()
{
    if (!IsCrypted())
        return false;

    {
        LOCK(cs_wallet);
        vMasterKey.clear();
    }

    NotifyStatusChanged(this);
    return true;
}

bool CWallet::Unlock(const CKeyingMaterial& vMasterKeyIn, bool accept_no_keys)
{
    {
        LOCK(cs_wallet);
        for (const auto& spk_man_pair : m_spk_managers) {
            if (!spk_man_pair.second->CheckDecryptionKey(vMasterKeyIn, accept_no_keys)) {
                return false;
            }
        }
        vMasterKey = vMasterKeyIn;
    }
    NotifyStatusChanged(this);
    return true;
}

std::set<ScriptPubKeyMan*> CWallet::GetActiveScriptPubKeyMans() const
{
    std::set<ScriptPubKeyMan*> spk_mans;
    for (bool internal : {false, true}) {
        for (OutputType t : OUTPUT_TYPES) {
            auto spk_man = GetScriptPubKeyMan(t, internal);
            if (spk_man) {
                spk_mans.insert(spk_man);
            }
        }
    }
    return spk_mans;
}

std::set<ScriptPubKeyMan*> CWallet::GetAllScriptPubKeyMans() const
{
    std::set<ScriptPubKeyMan*> spk_mans;
    for (const auto& spk_man_pair : m_spk_managers) {
        spk_mans.insert(spk_man_pair.second.get());
    }
    return spk_mans;
}

ScriptPubKeyMan* CWallet::GetScriptPubKeyMan(const OutputType& type, bool internal) const
{
    const std::map<OutputType, ScriptPubKeyMan*>& spk_managers = internal ? m_internal_spk_managers : m_external_spk_managers;
    std::map<OutputType, ScriptPubKeyMan*>::const_iterator it = spk_managers.find(type);
    if (it == spk_managers.end()) {
        return nullptr;
    }
    return it->second;
}

std::set<ScriptPubKeyMan*> CWallet::GetScriptPubKeyMans(const CScript& script) const
{
    std::set<ScriptPubKeyMan*> spk_mans;
    SignatureData sigdata;
    for (const auto& spk_man_pair : m_spk_managers) {
        if (spk_man_pair.second->CanProvide(script, sigdata)) {
            spk_mans.insert(spk_man_pair.second.get());
        }
    }
    return spk_mans;
}

const CKeyingMaterial& CWallet::GetEncryptionKey() const
{
    return vMasterKey;
}

bool CWallet::HasEncryptionKeys() const
{
    return !mapMasterKeys.empty();
}

ScriptPubKeyMan* CWallet::GetScriptPubKeyMan(const uint256& id) const
{
    if (m_spk_managers.count(id) > 0) {
        return m_spk_managers.at(id).get();
    }
    return nullptr;
}

std::unique_ptr<SigningProvider> CWallet::GetSolvingProvider(const CScript& script) const
{
    SignatureData sigdata;
    return GetSolvingProvider(script, sigdata);
}

std::unique_ptr<SigningProvider> CWallet::GetSolvingProvider(const CScript& script, SignatureData& sigdata) const
{
    for (const auto& spk_man_pair : m_spk_managers) {
        if (spk_man_pair.second->CanProvide(script, sigdata)) {
            return spk_man_pair.second->GetSolvingProvider(script);
        }
    }
    return nullptr;
}

LegacyScriptPubKeyMan* CWallet::GetLegacyScriptPubKeyMan() const
{
    if (IsWalletFlagSet(WALLET_FLAG_DESCRIPTORS)) {
        return nullptr;
    }
    // Legacy wallets only have one ScriptPubKeyMan which is a LegacyScriptPubKeyMan.
    // Everything in m_internal_spk_managers and m_external_spk_managers point to the same legacyScriptPubKeyMan.
    auto it = m_internal_spk_managers.find(OutputType::LEGACY);
    if (it == m_internal_spk_managers.end()) return nullptr;
    return dynamic_cast<LegacyScriptPubKeyMan*>(it->second);
}

LegacyScriptPubKeyMan* CWallet::GetOrCreateLegacyScriptPubKeyMan()
{
    SetupLegacyScriptPubKeyMan();
    return GetLegacyScriptPubKeyMan();
}

void CWallet::SetupLegacyScriptPubKeyMan()
{
    if (!m_internal_spk_managers.empty() || !m_external_spk_managers.empty() || !m_spk_managers.empty() || IsWalletFlagSet(WALLET_FLAG_DESCRIPTORS)) {
        return;
    }

    auto spk_manager = std::unique_ptr<ScriptPubKeyMan>(new LegacyScriptPubKeyMan(*this));
    for (const auto& type : LEGACY_OUTPUT_TYPES) {
        m_internal_spk_managers[type] = spk_manager.get();
        m_external_spk_managers[type] = spk_manager.get();
    }
    m_spk_managers[spk_manager->GetID()] = std::move(spk_manager);
}

//
// ELEMENTS WALLET ADDITIONS
//

bool CWallet::SetOnlinePubKey(const CPubKey& online_key_in)
{
    LOCK(cs_wallet);
    if (!WalletBatch(GetDatabase()).WriteOnlineKey(online_key_in)) {
        return false;
    }
    online_key = online_key_in;
    return true;
}

bool CWallet::SetOfflineXPubKey(const CExtPubKey& offline_xpub_in)
{
    LOCK(cs_wallet);
    if (!WalletBatch(GetDatabase()).WriteOfflineXPubKey(offline_xpub_in)) {
        return false;
    }
    offline_xpub = offline_xpub_in;
    return true;
}

bool CWallet::SetOfflineDescriptor(const std::string& offline_desc_in)
{
    LOCK(cs_wallet);
    if (!WalletBatch(GetDatabase()).WriteOfflineDescriptor(offline_desc_in)) {
        return false;
    }
    offline_desc = offline_desc_in;
    return true;
}

bool CWallet::SetOfflineCounter(int counter) {
    LOCK(cs_wallet);
    if (!WalletBatch(GetDatabase()).WriteOfflineCounter(counter)) {
        return false;
    }
    offline_counter = counter;
    return true;
}

unsigned int CWalletTx::GetPseudoInputOffset(const unsigned int input_index, const bool reissuance_token) const
{
    // There is no mapValue space for null issuances
    assert(reissuance_token ? !tx->vin[input_index].assetIssuance.nInflationKeys.IsNull() : !tx->vin[input_index].assetIssuance.nAmount.IsNull());
    unsigned int mapvalue_loc = 0;
    for (unsigned int i = 0; i < tx->vin.size()*2; i++) {
        if (input_index == i/2 && (reissuance_token ? 1 : 0) == i % 2) {
            break;
        }
        if (!tx->vin[i/2].assetIssuance.IsNull()) {
            if ((i % 2 == 0 && !tx->vin[i/2].assetIssuance.nAmount.IsNull()) ||
                    (i % 2 == 1 && !tx->vin[i/2].assetIssuance.nInflationKeys.IsNull())) {
                mapvalue_loc++;
            }
        }
    }
    return mapvalue_loc;
}

void CWalletTx::SetBlindingData(const unsigned int map_index, const CPubKey& blinding_pubkey, const CAmount value, const uint256& value_factor, const CAsset& asset, const uint256& asset_factor)
{
    if (mapValue["blindingdata"].size() < (map_index + 1) * 138) {
        mapValue["blindingdata"].resize((tx->vout.size() + GetNumIssuances(*tx)) * 138);
    }

    unsigned char* it = (unsigned char*)(&mapValue["blindingdata"][0]) + 138 * map_index;

    *it = 1;
    memcpy(&*(it + 1), &value, 8);
    memcpy(&*(it + 9), value_factor.begin(), 32);
    memcpy(&*(it + 41), asset_factor.begin(), 32);
    memcpy(&*(it + 73), asset.begin(), 32);
    if (blinding_pubkey.IsFullyValid()) {
        memcpy(&*(it + 105), blinding_pubkey.begin(), 33);
    } else {
        memset(&*(it + 105), 0, 33);
    }

}

void CWalletTx::GetBlindingData(const CWallet& wallet, const unsigned int map_index, const std::vector<unsigned char>& vchRangeproof, const CConfidentialValue& conf_value, const CConfidentialAsset& conf_asset, const CConfidentialNonce nonce, const CScript& scriptPubKey, CPubKey* blinding_pubkey_out, CAmount* value_out, uint256* value_factor_out, CAsset* asset_out, uint256* asset_factor_out) const
{
    // Blinding data is cached in a serialized record mapWallet["blindingdata"].
    // It contains a concatenation byte vectors, 74 bytes per txout or pseudo-input.
    // Each consists of:
    // * 1 byte boolean marker (has the output been computed)?
    // * 8 bytes value (-1 if unknown)
    // * 32 bytes value blinding factor
    // * 32 bytes asset blinding factor
    // * 32 bytes asset
    // * 33 bytes blinding pubkey (ECDH pubkey of the destination)
    // This is really ugly, and should use CDataStream serialization instead.

    if (mapValue["blindingdata"].size() < (map_index + 1) * 138) {
        mapValue["blindingdata"].resize((tx->vout.size() + GetNumIssuances(*tx)) * 138);
    }

    unsigned char* it = (unsigned char*)(&mapValue["blindingdata"][0]) + 138 * map_index;

    CAmount amount = -1;
    CPubKey pubkey;
    uint256 value_factor;
    CAsset asset_tag;
    uint256 asset_factor;

    if (*it == 1) {
        memcpy(&amount, &*(it + 1), 8);
        memcpy(value_factor.begin(), &*(it + 9), 32);
        memcpy(asset_factor.begin(), &*(it + 41), 32);
        memcpy(asset_tag.begin(), &*(it + 73), 32);
        pubkey.Set(it + 105, it + 138);

        if (amount != -1 && conf_value.IsExplicit()) {
            assert(conf_value.GetAmount() == amount);
        }
    } else {
        wallet.ComputeBlindingData(conf_value, conf_asset, nonce, scriptPubKey, vchRangeproof, amount, pubkey, value_factor, asset_tag, asset_factor);
        *it = 1;
        memcpy(&*(it + 1), &amount, 8);
        memcpy(&*(it + 9), value_factor.begin(), 32);
        memcpy(&*(it + 41), asset_factor.begin(), 32);
        memcpy(&*(it + 73), asset_tag.begin(), 32);
        if (pubkey.IsFullyValid()) {
            memcpy(&*(it + 105), pubkey.begin(), 33);
        } else {
            memset(&*(it + 105), 0, 33);
        }
    }

    if (value_out) *value_out = amount;
    if (blinding_pubkey_out) *blinding_pubkey_out = pubkey;
    if (value_factor_out) *value_factor_out = value_factor;
    if (asset_factor_out) *asset_factor_out = asset_factor;
    if (asset_out) *asset_out = asset_tag;
}

void CWalletTx::GetNonIssuanceBlindingData(const CWallet& wallet, const unsigned int output_index, CPubKey* blinding_pubkey_out, CAmount* value_out, uint256* value_factor_out, CAsset* asset_out, uint256* asset_factor_out) const {
    assert(output_index < tx->vout.size());
    const CTxOut& out = tx->vout[output_index];
    const CTxWitness& wit = tx->witness;
    GetBlindingData(wallet, output_index, wit.vtxoutwit.size() <= output_index ? std::vector<unsigned char>() : wit.vtxoutwit[output_index].vchRangeproof, out.nValue, out.nAsset, out.nNonce, out.scriptPubKey,
        blinding_pubkey_out, value_out, value_factor_out, asset_out, asset_factor_out);
}

void CWallet::ConnectScriptPubKeyManNotifiers()
{
    for (const auto& spk_man : GetActiveScriptPubKeyMans()) {
        spk_man->NotifyWatchonlyChanged.connect(NotifyWatchonlyChanged);
        spk_man->NotifyCanGetAddressesChanged.connect(NotifyCanGetAddressesChanged);
    }
}

void CWallet::LoadDescriptorScriptPubKeyMan(uint256 id, WalletDescriptor& desc)
{
    if (IsWalletFlagSet(WALLET_FLAG_EXTERNAL_SIGNER)) {
        auto spk_manager = std::unique_ptr<ScriptPubKeyMan>(new ExternalSignerScriptPubKeyMan(*this, desc));
        m_spk_managers[id] = std::move(spk_manager);
    } else {
        auto spk_manager = std::unique_ptr<ScriptPubKeyMan>(new DescriptorScriptPubKeyMan(*this, desc));
        m_spk_managers[id] = std::move(spk_manager);
    }
}

void CWallet::SetupDescriptorScriptPubKeyMans()
{
    AssertLockHeld(cs_wallet);

    if (!IsWalletFlagSet(WALLET_FLAG_EXTERNAL_SIGNER)) {
        // Make a seed
        CKey seed_key;
        seed_key.MakeNewKey(true);
        CPubKey seed = seed_key.GetPubKey();
        assert(seed_key.VerifyPubKey(seed));

        // Get the extended key
        CExtKey master_key;
        master_key.SetSeed(seed_key);

        for (bool internal : {false, true}) {
            for (OutputType t : OUTPUT_TYPES) {
                auto spk_manager = std::unique_ptr<DescriptorScriptPubKeyMan>(new DescriptorScriptPubKeyMan(*this));
                if (IsCrypted()) {
                    if (IsLocked()) {
                        throw std::runtime_error(std::string(__func__) + ": Wallet is locked, cannot setup new descriptors");
                    }
                    if (!spk_manager->CheckDecryptionKey(vMasterKey) && !spk_manager->Encrypt(vMasterKey, nullptr)) {
                        throw std::runtime_error(std::string(__func__) + ": Could not encrypt new descriptors");
                    }
                }
                spk_manager->SetupDescriptorGeneration(master_key, t, internal);
                uint256 id = spk_manager->GetID();
                m_spk_managers[id] = std::move(spk_manager);
                AddActiveScriptPubKeyMan(id, t, internal);
            }
        }
    } else {
        ExternalSigner signer = ExternalSignerScriptPubKeyMan::GetExternalSigner();

        // TODO: add account parameter
        int account = 0;
        UniValue signer_res = signer.GetDescriptors(account);

        if (!signer_res.isObject()) throw std::runtime_error(std::string(__func__) + ": Unexpected result");
        for (bool internal : {false, true}) {
            const UniValue& descriptor_vals = find_value(signer_res, internal ? "internal" : "receive");
            if (!descriptor_vals.isArray()) throw std::runtime_error(std::string(__func__) + ": Unexpected result");
            for (const UniValue& desc_val : descriptor_vals.get_array().getValues()) {
                std::string desc_str = desc_val.getValStr();
                FlatSigningProvider keys;
                std::string desc_error;
                std::unique_ptr<Descriptor> desc = Parse(desc_str, keys, desc_error, false);
                if (desc == nullptr) {
                    throw std::runtime_error(std::string(__func__) + ": Invalid descriptor \"" + desc_str + "\" (" + desc_error + ")");
                }
                if (!desc->GetOutputType()) {
                    continue;
                }
                OutputType t =  *desc->GetOutputType();
                auto spk_manager = std::unique_ptr<ExternalSignerScriptPubKeyMan>(new ExternalSignerScriptPubKeyMan(*this));
                spk_manager->SetupDescriptor(std::move(desc));
                uint256 id = spk_manager->GetID();
                m_spk_managers[id] = std::move(spk_manager);
                AddActiveScriptPubKeyMan(id, t, internal);
            }
        }
    }
}

void CWallet::AddActiveScriptPubKeyMan(uint256 id, OutputType type, bool internal)
{
    WalletBatch batch(GetDatabase());
    if (!batch.WriteActiveScriptPubKeyMan(static_cast<uint8_t>(type), id, internal)) {
        throw std::runtime_error(std::string(__func__) + ": writing active ScriptPubKeyMan id failed");
    }
    LoadActiveScriptPubKeyMan(id, type, internal);
}

void CWallet::LoadActiveScriptPubKeyMan(uint256 id, OutputType type, bool internal)
{
    // Activating ScriptPubKeyManager for a given output and change type is incompatible with legacy wallets.
    // Legacy wallets have only one ScriptPubKeyManager and it's active for all output and change types.
    Assert(IsWalletFlagSet(WALLET_FLAG_DESCRIPTORS));

    WalletLogPrintf("Setting spkMan to active: id = %s, type = %d, internal = %d\n", id.ToString(), static_cast<int>(type), static_cast<int>(internal));
    auto& spk_mans = internal ? m_internal_spk_managers : m_external_spk_managers;
    auto& spk_mans_other = internal ? m_external_spk_managers : m_internal_spk_managers;
    auto spk_man = m_spk_managers.at(id).get();
    spk_mans[type] = spk_man;

    const auto it = spk_mans_other.find(type);
    if (it != spk_mans_other.end() && it->second == spk_man) {
        spk_mans_other.erase(type);
    }

    NotifyCanGetAddressesChanged();
}

void CWallet::DeactivateScriptPubKeyMan(uint256 id, OutputType type, bool internal)
{
    auto spk_man = GetScriptPubKeyMan(type, internal);
    if (spk_man != nullptr && spk_man->GetID() == id) {
        WalletLogPrintf("Deactivate spkMan: id = %s, type = %d, internal = %d\n", id.ToString(), static_cast<int>(type), static_cast<int>(internal));
        WalletBatch batch(GetDatabase());
        if (!batch.EraseActiveScriptPubKeyMan(static_cast<uint8_t>(type), internal)) {
            throw std::runtime_error(std::string(__func__) + ": erasing active ScriptPubKeyMan id failed");
        }

        auto& spk_mans = internal ? m_internal_spk_managers : m_external_spk_managers;
        spk_mans.erase(type);
    }

    NotifyCanGetAddressesChanged();
}

bool CWallet::IsLegacy() const
{
    if (m_internal_spk_managers.count(OutputType::LEGACY) == 0) {
        return false;
    }
    auto spk_man = dynamic_cast<LegacyScriptPubKeyMan*>(m_internal_spk_managers.at(OutputType::LEGACY));
    return spk_man != nullptr;
}

DescriptorScriptPubKeyMan* CWallet::GetDescriptorScriptPubKeyMan(const WalletDescriptor& desc) const
{
    for (auto& spk_man_pair : m_spk_managers) {
        // Try to downcast to DescriptorScriptPubKeyMan then check if the descriptors match
        DescriptorScriptPubKeyMan* spk_manager = dynamic_cast<DescriptorScriptPubKeyMan*>(spk_man_pair.second.get());
        if (spk_manager != nullptr && spk_manager->HasWalletDescriptor(desc)) {
            return spk_manager;
        }
    }

    return nullptr;
}

std::optional<bool> CWallet::IsInternalScriptPubKeyMan(ScriptPubKeyMan* spk_man) const
{
    // Legacy script pubkey man can't be either external or internal
    if (IsLegacy()) {
        return std::nullopt;
    }

    // only active ScriptPubKeyMan can be internal
    if (!GetActiveScriptPubKeyMans().count(spk_man)) {
        return std::nullopt;
    }

    const auto desc_spk_man = dynamic_cast<DescriptorScriptPubKeyMan*>(spk_man);
    if (!desc_spk_man) {
        throw std::runtime_error(std::string(__func__) + ": unexpected ScriptPubKeyMan type.");
    }

    LOCK(desc_spk_man->cs_desc_man);
    const auto& type = desc_spk_man->GetWalletDescriptor().descriptor->GetOutputType();
    assert(type.has_value());

    return GetScriptPubKeyMan(*type, /* internal= */ true) == desc_spk_man;
}

ScriptPubKeyMan* CWallet::AddWalletDescriptor(WalletDescriptor& desc, const FlatSigningProvider& signing_provider, const std::string& label, bool internal)
{
    AssertLockHeld(cs_wallet);

    if (!IsWalletFlagSet(WALLET_FLAG_DESCRIPTORS)) {
        WalletLogPrintf("Cannot add WalletDescriptor to a non-descriptor wallet\n");
        return nullptr;
    }

    auto spk_man = GetDescriptorScriptPubKeyMan(desc);
    if (spk_man) {
        WalletLogPrintf("Update existing descriptor: %s\n", desc.descriptor->ToString());
        spk_man->UpdateWalletDescriptor(desc);
    } else {
        auto new_spk_man = std::unique_ptr<DescriptorScriptPubKeyMan>(new DescriptorScriptPubKeyMan(*this, desc));
        spk_man = new_spk_man.get();

        // Save the descriptor to memory
        m_spk_managers[new_spk_man->GetID()] = std::move(new_spk_man);
    }

    // Add the private keys to the descriptor
    for (const auto& entry : signing_provider.keys) {
        const CKey& key = entry.second;
        spk_man->AddDescriptorKey(key, key.GetPubKey());
    }

    // Top up key pool, the manager will generate new scriptPubKeys internally
    if (!spk_man->TopUp()) {
        WalletLogPrintf("Could not top up scriptPubKeys\n");
        return nullptr;
    }

    // Apply the label if necessary
    // Note: we disable labels for ranged descriptors
    if (!desc.descriptor->IsRange()) {
        auto script_pub_keys = spk_man->GetScriptPubKeys();
        if (script_pub_keys.empty()) {
            WalletLogPrintf("Could not generate scriptPubKeys (cache is empty)\n");
            return nullptr;
        }

        CTxDestination dest;
        if (!internal && ExtractDestination(script_pub_keys.at(0), dest)) {
            SetAddressBook(dest, label, "receive");
        }
    }

    // Save the descriptor to DB
    spk_man->WriteDescriptor();

    return spk_man;
}

CAmount CWalletTx::GetOutputValueOut(const CWallet& wallet, unsigned int output_index) const {
    CAmount ret;
    GetNonIssuanceBlindingData(wallet, output_index, nullptr, &ret, nullptr, nullptr, nullptr);
    return ret;
}

uint256 CWalletTx::GetOutputAmountBlindingFactor(const CWallet& wallet, unsigned int output_index) const {
    uint256 ret;
    GetNonIssuanceBlindingData(wallet, output_index, nullptr, nullptr, &ret, nullptr, nullptr);
    return ret;
}

uint256 CWalletTx::GetOutputAssetBlindingFactor(const CWallet& wallet, unsigned int output_index) const {
    uint256 ret;
    GetNonIssuanceBlindingData(wallet, output_index, nullptr, nullptr, nullptr, nullptr, &ret);
    return ret;
}

CAsset CWalletTx::GetOutputAsset(const CWallet& wallet, unsigned int output_index) const {
    CAsset ret;
    GetNonIssuanceBlindingData(wallet, output_index, nullptr, nullptr, nullptr, &ret, nullptr);
    return ret;
}

CPubKey CWalletTx::GetOutputBlindingPubKey(const CWallet& wallet, unsigned int output_index) const {
    CPubKey ret;
    GetNonIssuanceBlindingData(wallet, output_index, &ret, nullptr, nullptr, nullptr, nullptr);
    return ret;
}

void CWalletTx::GetIssuanceAssets(unsigned int input_index, CAsset* out_asset, CAsset* out_reissuance_token) const {
    assert(input_index < tx->vin.size());
    const CAssetIssuance& issuance = tx->vin[input_index].assetIssuance;

    if (out_asset && issuance.nAmount.IsNull()) {
        out_asset->SetNull();
        out_asset = nullptr;
    }
    if (out_reissuance_token && issuance.nInflationKeys.IsNull()) {
        out_reissuance_token->SetNull();
        out_reissuance_token = nullptr;
    }
    if (!(out_asset || out_reissuance_token)) return;

    if (issuance.assetBlindingNonce.IsNull()) {
        uint256 entropy;
        GenerateAssetEntropy(entropy, tx->vin[input_index].prevout, issuance.assetEntropy);
        if (out_reissuance_token) {
            CalculateReissuanceToken(*out_reissuance_token, entropy, issuance.nAmount.IsCommitment());
        }
        if (out_asset) {
            CalculateAsset(*out_asset, entropy);
        }
    }
    else {
        if (out_reissuance_token) {
            // Re-issuances don't emit issuance tokens
            out_reissuance_token->SetNull();
        }
        if (out_asset) {
            CalculateAsset(*out_asset, issuance.assetEntropy);
        }
    }
}

uint256 CWalletTx::GetIssuanceBlindingFactor(const CWallet& wallet, unsigned int input_index, bool reissuance_token) const {
    assert(input_index < tx->vin.size());
    CAsset asset;
    const CAssetIssuance& issuance = tx->vin[input_index].assetIssuance;
    const CTxWitness& wit = tx->witness;
    GetIssuanceAssets(input_index, reissuance_token ? nullptr : &asset, reissuance_token ? &asset : nullptr);
    if (asset.IsNull()) {
        return uint256();
    }
    const std::vector<unsigned char>& rangeproof = wit.vtxinwit.size() <= input_index ? std::vector<unsigned char>() : (reissuance_token ? wit.vtxinwit[input_index].vchInflationKeysRangeproof : wit.vtxinwit[input_index].vchIssuanceAmountRangeproof);
    unsigned int mapValueInd = GetPseudoInputOffset(input_index, reissuance_token) + tx->vout.size();

    uint256 ret;
    CScript blindingScript(CScript() << OP_RETURN << std::vector<unsigned char>(tx->vin[input_index].prevout.hash.begin(), tx->vin[input_index].prevout.hash.end()) << tx->vin[input_index].prevout.n);
    GetBlindingData(wallet, mapValueInd, rangeproof, reissuance_token ? issuance.nInflationKeys : issuance.nAmount, CConfidentialAsset(asset), CConfidentialNonce(), blindingScript, nullptr, nullptr, &ret, nullptr, nullptr);
    return ret;
}

CAmount CWalletTx::GetIssuanceAmount(const CWallet& wallet, unsigned int input_index, bool reissuance_token) const {
    assert(input_index < tx->vin.size());
    CAsset asset;
    const CAssetIssuance& issuance = tx->vin[input_index].assetIssuance;
    const CTxWitness& wit = tx->witness;
    GetIssuanceAssets(input_index, reissuance_token ? nullptr : &asset, reissuance_token ? &asset : nullptr);
    if (asset.IsNull()) {
        return -1;
    }
    unsigned int mapValueInd = GetPseudoInputOffset(input_index, reissuance_token) + tx->vout.size();
    const std::vector<unsigned char>& rangeproof = wit.vtxinwit.size() <= input_index ? std::vector<unsigned char>() : (reissuance_token ? wit.vtxinwit[input_index].vchInflationKeysRangeproof : wit.vtxinwit[input_index].vchIssuanceAmountRangeproof);

    CAmount ret;
    CScript blindingScript(CScript() << OP_RETURN << std::vector<unsigned char>(tx->vin[input_index].prevout.hash.begin(), tx->vin[input_index].prevout.hash.end()) << tx->vin[input_index].prevout.n);
    GetBlindingData(wallet, mapValueInd, rangeproof, reissuance_token ? issuance.nInflationKeys : issuance.nAmount, CConfidentialAsset(asset), CConfidentialNonce(), blindingScript, nullptr, &ret, nullptr, nullptr, nullptr);
    return ret;
}

void CWallet::ComputeBlindingData(const CConfidentialValue& conf_value, const CConfidentialAsset& conf_asset, const CConfidentialNonce& nonce, const CScript& scriptPubKey, const std::vector<unsigned char>& vchRangeproof, CAmount& value, CPubKey& blinding_pubkey, uint256& value_factor, CAsset& asset, uint256& asset_factor) const
{
    if (conf_value.IsExplicit() && conf_asset.IsExplicit()) {
        value = conf_value.GetAmount();
        asset = conf_asset.GetAsset();
        blinding_pubkey = CPubKey();
        value_factor.SetNull();
        asset_factor.SetNull();
        return;
    }

    CKey blinding_key;
    if ((blinding_key = GetBlindingKey(&scriptPubKey)).IsValid()) {
        // For outputs using derived blinding.
        if (UnblindConfidentialPair(blinding_key, conf_value, conf_asset, nonce, scriptPubKey, vchRangeproof, value, value_factor, asset, asset_factor)) {
            // TODO: make sure SetBlindingData sets it as receiver's blinding pubkey
            blinding_pubkey = blinding_key.GetPubKey();
            return;
        }
    }

    value = -1;
    blinding_pubkey = CPubKey();
    value_factor.SetNull();
    asset.SetNull();
    asset_factor.SetNull();
}

void CWalletTx::WipeUnknownBlindingData(const CWallet& wallet)
{
    for (unsigned int n = 0; n < tx->vout.size(); n++) {
        if (GetOutputValueOut(wallet, n) == -1) {
            mapValue["blindingdata"][138 * n] = 0;
        }
    }
    for (unsigned int n = 0; n < tx->vin.size(); n++) {
        if (!tx->vin[n].assetIssuance.nAmount.IsNull()) {
            if (GetIssuanceAmount(wallet, n, false) == -1) {
                mapValue["blindingdata"][138 * (tx->vout.size() + GetPseudoInputOffset(n, false))] = 0;
            }
        }
        if (!tx->vin[n].assetIssuance.nInflationKeys.IsNull()) {
            if (GetIssuanceAmount(wallet, n, true) == -1) {
                mapValue["blindingdata"][138 * (tx->vout.size() + GetPseudoInputOffset(n, true))] = 0;
            }
        }
    }
}

std::map<uint256, std::pair<CAsset, CAsset> > CWallet::GetReissuanceTokenTypes() const {
    std::map<uint256, std::pair<CAsset, CAsset> > tokenMap;
    {
        LOCK(cs_wallet);
        for (std::map<uint256, CWalletTx>::const_iterator it = mapWallet.begin(); it != mapWallet.end(); ++it) {
            const CWalletTx* pcoin = &(*it).second;
            CAsset asset;
            CAsset token;
            uint256 entropy;
            for (unsigned int input_index = 0; input_index < pcoin->tx->vin.size(); input_index++) {
                const CAssetIssuance& issuance = pcoin->tx->vin[input_index].assetIssuance;
                if (issuance.IsNull()) {
                    continue;
                }
                // Only looking at initial issuances
                if (issuance.assetBlindingNonce.IsNull()) {
                    GenerateAssetEntropy(entropy, pcoin->tx->vin[input_index].prevout, issuance.assetEntropy);
                    CalculateAsset(asset, entropy);
                    // TODO handle the case with null nAmount (not decided yet)
                    CalculateReissuanceToken(token, entropy, issuance.nAmount.IsCommitment());
                    tokenMap[entropy] = std::make_pair(token, asset);
                }
            }
        }
    }
    return tokenMap;
}

CKey CWallet::GetBlindingKey(const CScript* script) const {
    CKey key;

    if (script != NULL) {
        std::map<CScriptID, uint256>::const_iterator it = mapSpecificBlindingKeys.find(CScriptID(*script));
        if (it != mapSpecificBlindingKeys.end()) {
            key.Set(it->second.begin(), it->second.end(), true);
            if (key.IsValid()) {
                return key;
            }
        }
    }

    if (script != NULL && !blinding_derivation_key.IsNull()) {
        unsigned char vch[32];
        CHMAC_SHA256(blinding_derivation_key.begin(), blinding_derivation_key.size()).Write(&((*script)[0]), script->size()).Finalize(vch);
        key.Set(&vch[0], &vch[32], true);
        if (key.IsValid()) {
            return key;
        }
    }

    return CKey();
}

CPubKey CWallet::GetBlindingPubKey(const CScript& script) const
{
    CKey key = GetBlindingKey(&script);
    if (key.IsValid()) {
        return key.GetPubKey();
    }

    return CPubKey();
}

bool CWallet::LoadSpecificBlindingKey(const CScriptID& scriptid, const uint256& key)
{
    AssertLockHeld(cs_wallet); // mapSpecificBlindingKeys
    mapSpecificBlindingKeys[scriptid] = key;
    return true;
}

bool CWallet::AddSpecificBlindingKey(const CScriptID& scriptid, const uint256& key)
{
    AssertLockHeld(cs_wallet); // mapSpecificBlindingKeys
    if (!LoadSpecificBlindingKey(scriptid, key))
        return false;

    return WalletBatch(GetDatabase()).WriteSpecificBlindingKey(scriptid, key);
}

bool CWallet::SetMasterBlindingKey(const uint256& key)
{
    AssertLockHeld(cs_wallet);
    if (!WalletBatch(GetDatabase()).WriteBlindingDerivationKey(key)) {
        return false;
    }
    blinding_derivation_key = key;
    return true;
}

// END ELEMENTS
//
} // namespace wallet
