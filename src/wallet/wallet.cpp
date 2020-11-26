// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2020 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <wallet/wallet.h>

#include <chain.h>
#include <consensus/consensus.h>
#include <consensus/validation.h>
#include <fs.h>
#include <interfaces/chain.h>
#include <interfaces/wallet.h>
#include <key.h>
#include <key_io.h>
#include <optional.h>
#include <policy/fees.h>
#include <policy/policy.h>
#include <primitives/block.h>
#include <primitives/transaction.h>
#include <script/descriptor.h>
#include <script/script.h>
#include <script/signingprovider.h>
#include <util/bip32.h>
#include <util/error.h>
#include <util/fees.h>
#include <util/moneystr.h>
#include <util/rbf.h>
#include <util/translation.h>
#include <util/validation.h>
#include <validation.h>
#include <wallet/coincontrol.h>
#include <wallet/fees.h>

#include <algorithm>
#include <assert.h>

#include <boost/algorithm/string/replace.hpp>

#include <blind.h>
#include <issuance.h>
#include <crypto/hmac_sha256.h>
#include <random.h>

const std::map<uint64_t,std::string> WALLET_FLAG_CAVEATS{
    {WALLET_FLAG_AVOID_REUSE,
        "You need to rescan the blockchain in order to correctly mark used "
        "destinations in the past. Until this is done, some destinations may "
        "be considered unused, even if the opposite is the case."
    },
};

static const size_t OUTPUT_GROUP_MAX_ENTRIES = 10;

static RecursiveMutex cs_wallets;
static std::vector<std::shared_ptr<CWallet>> vpwallets GUARDED_BY(cs_wallets);
static std::list<LoadWalletFn> g_load_wallet_fns GUARDED_BY(cs_wallets);

bool AddWallet(const std::shared_ptr<CWallet>& wallet)
{
    LOCK(cs_wallets);
    assert(wallet);
    std::vector<std::shared_ptr<CWallet>>::const_iterator i = std::find(vpwallets.begin(), vpwallets.end(), wallet);
    if (i != vpwallets.end()) return false;
    vpwallets.push_back(wallet);
    wallet->ConnectScriptPubKeyManNotifiers();
    return true;
}

bool RemoveWallet(const std::shared_ptr<CWallet>& wallet)
{
    LOCK(cs_wallets);
    assert(wallet);
    std::vector<std::shared_ptr<CWallet>>::iterator i = std::find(vpwallets.begin(), vpwallets.end(), wallet);
    if (i == vpwallets.end()) return false;
    vpwallets.erase(i);
    return true;
}

bool HasWallets()
{
    LOCK(cs_wallets);
    return !vpwallets.empty();
}

std::vector<std::shared_ptr<CWallet>> GetWallets()
{
    LOCK(cs_wallets);
    return vpwallets;
}

std::shared_ptr<CWallet> GetWallet(const std::string& name)
{
    LOCK(cs_wallets);
    for (const std::shared_ptr<CWallet>& wallet : vpwallets) {
        if (wallet->GetName() == name) return wallet;
    }
    return nullptr;
}

std::unique_ptr<interfaces::Handler> HandleLoadWallet(LoadWalletFn load_wallet)
{
    LOCK(cs_wallets);
    auto it = g_load_wallet_fns.emplace(g_load_wallet_fns.end(), std::move(load_wallet));
    return interfaces::MakeHandler([it] { LOCK(cs_wallets); g_load_wallet_fns.erase(it); });
}

static Mutex g_wallet_release_mutex;
static std::condition_variable g_wallet_release_cv;
static std::set<std::string> g_unloading_wallet_set;

// Custom deleter for shared_ptr<CWallet>.
static void ReleaseWallet(CWallet* wallet)
{
    // Unregister and delete the wallet right after BlockUntilSyncedToCurrentChain
    // so that it's in sync with the current chainstate.
    const std::string name = wallet->GetName();
    wallet->WalletLogPrintf("Releasing wallet\n");
    wallet->BlockUntilSyncedToCurrentChain();
    wallet->Flush();
    wallet->m_chain_notifications_handler.reset();
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

std::shared_ptr<CWallet> LoadWallet(interfaces::Chain& chain, const WalletLocation& location, std::string& error, std::vector<std::string>& warnings)
{
    if (!CWallet::Verify(chain, location, false, error, warnings)) {
        error = "Wallet file verification failed: " + error;
        return nullptr;
    }

    std::shared_ptr<CWallet> wallet = CWallet::CreateWalletFromFile(chain, location, error, warnings);
    if (!wallet) {
        error = "Wallet loading failed: " + error;
        return nullptr;
    }
    AddWallet(wallet);
    wallet->postInitProcess();
    return wallet;
}

std::shared_ptr<CWallet> LoadWallet(interfaces::Chain& chain, const std::string& name, std::string& error, std::vector<std::string>& warnings)
{
    return LoadWallet(chain, WalletLocation(name), error, warnings);
}

WalletCreationStatus CreateWallet(interfaces::Chain& chain, const SecureString& passphrase, uint64_t wallet_creation_flags, const std::string& name, std::string& error, std::vector<std::string>& warnings, std::shared_ptr<CWallet>& result)
{
    // Indicate that the wallet is actually supposed to be blank and not just blank to make it encrypted
    bool create_blank = (wallet_creation_flags & WALLET_FLAG_BLANK_WALLET);

    // Born encrypted wallets need to be created blank first.
    if (!passphrase.empty()) {
        wallet_creation_flags |= WALLET_FLAG_BLANK_WALLET;
    }

    // Check the wallet file location
    WalletLocation location(name);
    if (location.Exists()) {
        error = "Wallet " + location.GetName() + " already exists.";
        return WalletCreationStatus::CREATION_FAILED;
    }

    // Wallet::Verify will check if we're trying to create a wallet with a duplicate name.
    if (!CWallet::Verify(chain, location, false, error, warnings)) {
        error = "Wallet file verification failed: " + error;
        return WalletCreationStatus::CREATION_FAILED;
    }

    // Do not allow a passphrase when private keys are disabled
    if (!passphrase.empty() && (wallet_creation_flags & WALLET_FLAG_DISABLE_PRIVATE_KEYS)) {
        error = "Passphrase provided but private keys are disabled. A passphrase is only used to encrypt private keys, so cannot be used for wallets with private keys disabled.";
        return WalletCreationStatus::CREATION_FAILED;
    }

    // Make the wallet
    std::shared_ptr<CWallet> wallet = CWallet::CreateWalletFromFile(chain, location, error, warnings, wallet_creation_flags);
    if (!wallet) {
        error = "Wallet creation failed: " + error;
        return WalletCreationStatus::CREATION_FAILED;
    }

    // Encrypt the wallet
    if (!passphrase.empty() && !(wallet_creation_flags & WALLET_FLAG_DISABLE_PRIVATE_KEYS)) {
        if (!wallet->EncryptWallet(passphrase)) {
            error = "Error: Wallet created but failed to encrypt.";
            return WalletCreationStatus::ENCRYPTION_FAILED;
        }
        if (!create_blank) {
            // Unlock the wallet
            if (!wallet->Unlock(passphrase)) {
                error = "Error: Wallet was encrypted but could not be unlocked";
                return WalletCreationStatus::ENCRYPTION_FAILED;
            }

            // Set a seed for the wallet
            {
                LOCK(wallet->cs_wallet);
                for (auto spk_man : wallet->GetActiveScriptPubKeyMans()) {
                    if (!spk_man->SetupGeneration()) {
                        error = "Unable to generate initial keys";
                        return WalletCreationStatus::CREATION_FAILED;
                    }
                }
            }

            // Relock the wallet
            wallet->Lock();
        }
    }
    AddWallet(wallet);
    wallet->postInitProcess();
    result = wallet;
    return WalletCreationStatus::SUCCESS;
}

const uint256 CWalletTx::ABANDON_HASH(UINT256_ONE());

/** @defgroup mapWallet
 *
 * @{
 */

std::string COutput::ToString() const
{
    return strprintf("COutput(%s, %d, %d) [%s] [%s]", tx->GetHash().ToString(), i, nDepth, FormatMoney(tx->GetOutputValueOut(i)), tx->GetOutputAsset(i).GetHex());
}

const CWalletTx* CWallet::GetWalletTx(const uint256& hash) const
{
    LOCK(cs_wallet);
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
                WalletBatch(*database).WriteMasterKey(pMasterKey.first, pMasterKey.second);
                if (fWasLocked)
                    Lock();
                return true;
            }
        }
    }

    return false;
}

void CWallet::ChainStateFlushed(const CBlockLocator& loc)
{
    WalletBatch batch(*database);
    batch.WriteBestBlock(loc);
}

void CWallet::SetMinVersion(enum WalletFeature nVersion, WalletBatch* batch_in, bool fExplicit)
{
    LOCK(cs_wallet);
    if (nWalletVersion >= nVersion)
        return;

    // when doing an explicit upgrade, if we pass the max version permitted, upgrade all the way
    if (fExplicit && nVersion > nWalletMaxVersion)
            nVersion = FEATURE_LATEST;

    nWalletVersion = nVersion;

    if (nVersion > nWalletMaxVersion)
        nWalletMaxVersion = nVersion;

    {
        WalletBatch* batch = batch_in ? batch_in : new WalletBatch(*database);
        if (nWalletVersion > 40000)
            batch->WriteMinVersion(nWalletVersion);
        if (!batch_in)
            delete batch;
    }
}

bool CWallet::SetMaxVersion(int nVersion)
{
    LOCK(cs_wallet);
    // cannot downgrade below current version
    if (nWalletVersion > nVersion)
        return false;

    nWalletMaxVersion = nVersion;

    return true;
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

void CWallet::Flush(bool shutdown)
{
    database->Flush(shutdown);
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
            int depth = mit->second.GetDepthInMainChain();
            if (depth > 0  || (depth == 0 && !mit->second.isAbandoned()))
                return true; // Spent
        }
    }
    return false;
}

void CWallet::AddToSpends(const COutPoint& outpoint, const uint256& wtxid)
{
    mapTxSpends.insert(std::make_pair(outpoint, wtxid));

    setLockedCoins.erase(outpoint);

    std::pair<TxSpends::iterator, TxSpends::iterator> range;
    range = mapTxSpends.equal_range(outpoint);
    SyncMetaData(range);
}


void CWallet::AddToSpends(const uint256& wtxid)
{
    auto it = mapWallet.find(wtxid);
    assert(it != mapWallet.end());
    CWalletTx& thisTx = it->second;
    if (thisTx.IsCoinBase()) // Coinbases don't spend anything!
        return;

    for (const CTxIn& txin : thisTx.tx->vin)
        AddToSpends(txin.prevout, wtxid);
}

bool CWallet::EncryptWallet(const SecureString& strWalletPassphrase)
{
    if (IsCrypted())
        return false;

    CKeyingMaterial _vMasterKey;

    _vMasterKey.resize(WALLET_CRYPTO_KEY_SIZE);
    GetStrongRandBytes(&_vMasterKey[0], WALLET_CRYPTO_KEY_SIZE);

    CMasterKey kMasterKey;

    kMasterKey.vchSalt.resize(WALLET_CRYPTO_SALT_SIZE);
    GetStrongRandBytes(&kMasterKey.vchSalt[0], WALLET_CRYPTO_SALT_SIZE);

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
        WalletBatch* encrypted_batch = new WalletBatch(*database);
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
        SetMinVersion(FEATURE_WALLETCRYPT, encrypted_batch, true);

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

        // if we are using HD, replace the HD seed with a new one
        if (auto spk_man = GetLegacyScriptPubKeyMan()) {
            if (spk_man->IsHDEnabled()) {
                if (!spk_man->SetupGeneration(true)) {
                    return false;
                }
            }
        }
        Lock();

        // Need to completely rewrite the wallet file; if we don't, bdb might keep
        // bits of the unencrypted private key in slack space in the database file.
        database->Rewrite();

        // BDB seems to have a bad habit of writing old data into
        // slack space in .dat files; that is bad if the old data is
        // unencrypted private keys. So:
        database->ReloadDbEnv();

    }
    NotifyStatusChanged(this);

    return true;
}

DBErrors CWallet::ReorderTransactions()
{
    LOCK(cs_wallet);
    WalletBatch batch(*database);

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
        WalletBatch(*database).WriteOrderPosNext(nOrderPosNext);
    }
    return nRet;
}

void CWallet::MarkDirty()
{
    {
        LOCK(cs_wallet);
        for (std::pair<const uint256, CWalletTx>& item : mapWallet)
            item.second.MarkDirty();
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

    WalletBatch batch(*database, "r+");

    bool success = true;
    if (!batch.WriteTx(wtx)) {
        WalletLogPrintf("%s: Updating batch tx %s failed\n", __func__, wtx.GetHash().ToString());
        success = false;
    }

    NotifyTransactionChanged(this, originalHash, CT_UPDATED);

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
            if (used && !GetDestData(dst, "used", nullptr)) {
                if (AddDestData(batch, dst, "used", "p")) { // p for "present", opposite of absent (null)
                    tx_destinations.insert(dst);
                }
            } else if (!used && GetDestData(dst, "used", nullptr)) {
                EraseDestData(batch, dst, "used");
            }
        }
    }
}

bool CWallet::IsSpentKey(const uint256& hash, unsigned int n) const
{
    AssertLockHeld(cs_wallet);
    CTxDestination dst;
    const CWalletTx* srctx = GetWalletTx(hash);
    if (srctx) {
        assert(srctx->tx->vout.size() > n);
        LegacyScriptPubKeyMan* spk_man = GetLegacyScriptPubKeyMan();
        // When descriptor wallets arrive, these additional checks are
        // likely superfluous and can be optimized out
        assert(spk_man != nullptr);
        for (const auto& keyid : GetAffectedKeys(srctx->tx->vout[n].scriptPubKey, *spk_man)) {
            WitnessV0KeyHash wpkh_dest(keyid);
            if (GetDestData(wpkh_dest, "used", nullptr)) {
                return true;
            }
            ScriptHash sh_wpkh_dest(GetScriptForDestination(wpkh_dest));
            if (GetDestData(sh_wpkh_dest, "used", nullptr)) {
                return true;
            }
            PKHash pkh_dest(keyid);
            if (GetDestData(pkh_dest, "used", nullptr)) {
                return true;
            }
        }
    }
    return false;
}

bool CWallet::AddToWallet(const CWalletTx& wtxIn, bool fFlushOnClose)
{
    LOCK(cs_wallet);

    WalletBatch batch(*database, "r+", fFlushOnClose);

    uint256 hash = wtxIn.GetHash();

    if (IsWalletFlagSet(WALLET_FLAG_AVOID_REUSE)) {
        // Mark used destinations
        std::set<CTxDestination> tx_destinations;

        for (const CTxIn& txin : wtxIn.tx->vin) {
            const COutPoint& op = txin.prevout;
            SetSpentKeyState(batch, op.hash, op.n, true, tx_destinations);
        }

        MarkDestinationsDirty(tx_destinations);
    }

    // Inserts only if not already there, returns tx inserted or tx found
    std::pair<std::map<uint256, CWalletTx>::iterator, bool> ret = mapWallet.insert(std::make_pair(hash, wtxIn));
    CWalletTx& wtx = (*ret.first).second;
    wtx.BindWallet(this);
    bool fInsertedNew = ret.second;
    if (fInsertedNew) {
        wtx.nTimeReceived = chain().getAdjustedTime();
        wtx.nOrderPos = IncOrderPosNext(&batch);
        wtx.m_it_wtxOrdered = wtxOrdered.insert(std::make_pair(wtx.nOrderPos, &wtx));
        wtx.nTimeSmart = ComputeTimeSmart(wtx);
        AddToSpends(hash);
    }

    bool fUpdated = false;
    if (!fInsertedNew)
    {
        if (wtxIn.m_confirm.status != wtx.m_confirm.status) {
            wtx.m_confirm.status = wtxIn.m_confirm.status;
            wtx.m_confirm.nIndex = wtxIn.m_confirm.nIndex;
            wtx.m_confirm.hashBlock = wtxIn.m_confirm.hashBlock;
            wtx.m_confirm.block_height = wtxIn.m_confirm.block_height;
            fUpdated = true;
        } else {
            assert(wtx.m_confirm.nIndex == wtxIn.m_confirm.nIndex);
            assert(wtx.m_confirm.hashBlock == wtxIn.m_confirm.hashBlock);
            assert(wtx.m_confirm.block_height == wtxIn.m_confirm.block_height);
        }
        if (wtxIn.fFromMe && wtxIn.fFromMe != wtx.fFromMe)
        {
            wtx.fFromMe = wtxIn.fFromMe;
            fUpdated = true;
        }
        // If we have a witness-stripped version of this transaction, and we
        // see a new version with a witness, then we must be upgrading a pre-segwit
        // wallet.  Store the new version of the transaction with the witness,
        // as the stripped-version must be invalid.
        // TODO: Store all versions of the transaction, instead of just one.
        if (wtxIn.tx->HasWitness() && !wtx.tx->HasWitness()) {
            wtx.SetTx(wtxIn.tx);
            fUpdated = true;
        }
    }

    //// debug print
    WalletLogPrintf("AddToWallet %s  %s%s\n", wtxIn.GetHash().ToString(), (fInsertedNew ? "new" : ""), (fUpdated ? "update" : ""));

    // Write to disk
    if (fInsertedNew || fUpdated)
        if (!batch.WriteTx(wtx))
            return false;

    // Break debit/credit balance caches:
    wtx.MarkDirty();

    // Notify UI of new or updated transaction
    NotifyTransactionChanged(this, hash, fInsertedNew ? CT_NEW : CT_UPDATED);

#if HAVE_SYSTEM
    // notify an external script when a wallet transaction comes in or is updated
    std::string strCmd = gArgs.GetArg("-walletnotify", "");

    if (!strCmd.empty())
    {
        boost::replace_all(strCmd, "%s", wtxIn.GetHash().GetHex());
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

    return true;
}

void CWallet::LoadToWallet(CWalletTx& wtxIn)
{
    // If wallet doesn't have a chain (e.g bitcoin-wallet), lock can't be taken.
    auto locked_chain = LockChain();
    if (locked_chain) {
        Optional<int> block_height = locked_chain->getBlockHeight(wtxIn.m_confirm.hashBlock);
        if (block_height) {
            // Update cached block height variable since it not stored in the
            // serialized transaction.
            wtxIn.m_confirm.block_height = *block_height;
        } else if (wtxIn.isConflicted() || wtxIn.isConfirmed()) {
            // If tx block (or conflicting block) was reorged out of chain
            // while the wallet was shutdown, change tx status to UNCONFIRMED
            // and reset block height, hash, and index. ABANDONED tx don't have
            // associated blocks and don't need to be updated. The case where a
            // transaction was reorged out while online and then reconfirmed
            // while offline is covered by the rescan logic.
            wtxIn.setUnconfirmed();
            wtxIn.m_confirm.hashBlock = uint256();
            wtxIn.m_confirm.block_height = 0;
            wtxIn.m_confirm.nIndex = 0;
        }
    }
    uint256 hash = wtxIn.GetHash();
    const auto& ins = mapWallet.emplace(hash, wtxIn);
    CWalletTx& wtx = ins.first->second;
    wtx.BindWallet(this);
    if (/* insertion took place */ ins.second) {
        wtx.m_it_wtxOrdered = wtxOrdered.insert(std::make_pair(wtx.nOrderPos, &wtx));
    }
    AddToSpends(hash);
    for (const CTxIn& txin : wtx.tx->vin) {
        auto it = mapWallet.find(txin.prevout.hash);
        if (it != mapWallet.end()) {
            CWalletTx& prevtx = it->second;
            if (prevtx.isConflicted()) {
                MarkConflicted(prevtx.m_confirm.hashBlock, prevtx.m_confirm.block_height, wtx.GetHash());
            }
        }
    }
}

bool CWallet::AddToWalletIfInvolvingMe(const CTransactionRef& ptx, CWalletTx::Confirmation confirm, bool fUpdate)
{
    const CTransaction& tx = *ptx;
    {
        AssertLockHeld(cs_wallet);

        if (!confirm.hashBlock.IsNull()) {
            for (const CTxIn& txin : tx.vin) {
                std::pair<TxSpends::const_iterator, TxSpends::const_iterator> range = mapTxSpends.equal_range(txin.prevout);
                while (range.first != range.second) {
                    if (range.first->second != tx.GetHash()) {
                        WalletLogPrintf("Transaction %s (in block %s) conflicts with wallet transaction %s (both spend %s:%i)\n", tx.GetHash().ToString(), confirm.hashBlock.ToString(), range.first->second.ToString(), range.first->first.hash.ToString(), range.first->first.n);
                        MarkConflicted(confirm.hashBlock, confirm.block_height, range.first->second);
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
                for (const auto& spk_man_pair : m_spk_managers) {
                    spk_man_pair.second->MarkUnusedAddresses(txout.scriptPubKey);
                }
            }

            CWalletTx wtx(this, ptx);

            // Block disconnection override an abandoned tx as unconfirmed
            // which means user may have to call abandontransaction again
            wtx.m_confirm = confirm;

            return AddToWallet(wtx, false);
        }
    }
    return false;
}

bool CWallet::TransactionCanBeAbandoned(const uint256& hashTx) const
{
    auto locked_chain = chain().lock();
    LOCK(cs_wallet);
    const CWalletTx* wtx = GetWalletTx(hashTx);
    return wtx && !wtx->isAbandoned() && wtx->GetDepthInMainChain() == 0 && !wtx->InMempool();
}

void CWallet::MarkInputsDirty(const CTransactionRef& tx)
{
    for (const CTxIn& txin : tx->vin) {
        auto it = mapWallet.find(txin.prevout.hash);
        if (it != mapWallet.end()) {
            it->second.MarkDirty();
        }
    }
}

bool CWallet::AbandonTransaction(const uint256& hashTx)
{
    auto locked_chain = chain().lock(); // Temporary. Removed in upcoming lock cleanup
    LOCK(cs_wallet);

    WalletBatch batch(*database, "r+");

    std::set<uint256> todo;
    std::set<uint256> done;

    // Can't mark abandoned if confirmed or in mempool
    auto it = mapWallet.find(hashTx);
    assert(it != mapWallet.end());
    CWalletTx& origtx = it->second;
    if (origtx.GetDepthInMainChain() != 0 || origtx.InMempool()) {
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
        int currentconfirm = wtx.GetDepthInMainChain();
        // If the orig tx was not in block, none of its spends can be
        assert(currentconfirm <= 0);
        // if (currentconfirm < 0) {Tx and spends are already conflicted, no need to abandon}
        if (currentconfirm == 0 && !wtx.isAbandoned()) {
            // If the orig tx was not in block/mempool, none of its spends can be in mempool
            assert(!wtx.InMempool());
            wtx.setAbandoned();
            wtx.MarkDirty();
            batch.WriteTx(wtx);
            NotifyTransactionChanged(this, wtx.GetHash(), CT_UPDATED);
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
    auto locked_chain = chain().lock();
    LOCK(cs_wallet);

    int conflictconfirms = (m_last_block_processed_height - conflicting_height + 1) * -1;
    // If number of conflict confirms cannot be determined, this means
    // that the block is still unknown or not yet part of the main chain,
    // for example when loading the wallet during a reindex. Do nothing in that
    // case.
    if (conflictconfirms >= 0)
        return;

    // Do not flush the wallet here for performance reasons
    WalletBatch batch(*database, "r+", false);

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
        int currentconfirm = wtx.GetDepthInMainChain();
        if (conflictconfirms < currentconfirm) {
            // Block is 'more conflicted' than current confirm; update.
            // Mark transaction as conflicted with this block.
            wtx.m_confirm.nIndex = 0;
            wtx.m_confirm.hashBlock = hashBlock;
            wtx.m_confirm.block_height = conflicting_height;
            wtx.setConflicted();
            wtx.MarkDirty();
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

void CWallet::SyncTransaction(const CTransactionRef& ptx, CWalletTx::Confirmation confirm, bool update_tx)
{
    if (!AddToWalletIfInvolvingMe(ptx, confirm, update_tx))
        return; // Not one of ours

    // If a transaction changes 'conflicted' state, that changes the balance
    // available of the outputs it spends. So force those to be
    // recomputed, also:
    MarkInputsDirty(ptx);
}

void CWallet::TransactionAddedToMempool(const CTransactionRef& ptx) {
    auto locked_chain = chain().lock();
    LOCK(cs_wallet);
    CWalletTx::Confirmation confirm(CWalletTx::Status::UNCONFIRMED, /* block_height */ 0, {}, /* nIndex */ 0);
    SyncTransaction(ptx, confirm);

    auto it = mapWallet.find(ptx->GetHash());
    if (it != mapWallet.end()) {
        it->second.fInMempool = true;
    }
}

void CWallet::TransactionRemovedFromMempool(const CTransactionRef &ptx) {
    LOCK(cs_wallet);
    auto it = mapWallet.find(ptx->GetHash());
    if (it != mapWallet.end()) {
        it->second.fInMempool = false;
    }
}

void CWallet::BlockConnected(const CBlock& block, const std::vector<CTransactionRef>& vtxConflicted, int height)
{
    const uint256& block_hash = block.GetHash();
    auto locked_chain = chain().lock();
    LOCK(cs_wallet);

    m_last_block_processed_height = height;
    m_last_block_processed = block_hash;
    for (size_t index = 0; index < block.vtx.size(); index++) {
        CWalletTx::Confirmation confirm(CWalletTx::Status::CONFIRMED, height, block_hash, index);
        SyncTransaction(block.vtx[index], confirm);
        TransactionRemovedFromMempool(block.vtx[index]);
    }
    for (const CTransactionRef& ptx : vtxConflicted) {
        TransactionRemovedFromMempool(ptx);
    }
}

void CWallet::BlockDisconnected(const CBlock& block, int height)
{
    auto locked_chain = chain().lock();
    LOCK(cs_wallet);

    // At block disconnection, this will change an abandoned transaction to
    // be unconfirmed, whether or not the transaction is added back to the mempool.
    // User may have to call abandontransaction again. It may be addressed in the
    // future with a stickier abandoned state or even removing abandontransaction call.
    m_last_block_processed_height = height - 1;
    m_last_block_processed = block.hashPrevBlock;
    for (const CTransactionRef& ptx : block.vtx) {
        CWalletTx::Confirmation confirm(CWalletTx::Status::UNCONFIRMED, /* block_height */ 0, {}, /* nIndex */ 0);
        SyncTransaction(ptx, confirm);
    }
}

void CWallet::UpdatedBlockTip()
{
    m_best_block_time = GetTime();
}


void CWallet::BlockUntilSyncedToCurrentChain() {
    AssertLockNotHeld(cs_wallet);
    // Skip the queue-draining stuff if we know we're caught up with
    // ::ChainActive().Tip(), otherwise put a callback in the validation interface queue and wait
    // for the queue to drain enough to execute it (indicating we are caught up
    // at least with the time we entered this function).
    uint256 last_block_hash = WITH_LOCK(cs_wallet, return m_last_block_processed);
    chain().waitForNotificationsIfTipChanged(last_block_hash);
}


isminetype CWallet::IsMine(const CTxIn &txin) const
{
    {
        LOCK(cs_wallet);
        std::map<uint256, CWalletTx>::const_iterator mi = mapWallet.find(txin.prevout.hash);
        if (mi != mapWallet.end())
        {
            const CWalletTx& prev = (*mi).second;
            if (txin.prevout.n < prev.tx->vout.size())
                return IsMine(prev.tx->vout[txin.prevout.n]);
        }
    }
    return ISMINE_NO;
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
                    amounts[prev.GetOutputAsset(txin.prevout.n)] = std::max<CAmount>(0, prev.GetOutputValueOut(txin.prevout.n));
                    return amounts;
                }
        }
    }
    return CAmountMap();
}

isminetype CWallet::IsMine(const CTxOut& txout) const
{
    return IsMine(txout.scriptPubKey);
}

isminetype CWallet::IsMine(const CTxDestination& dest) const
{
    return IsMine(GetScriptForDestination(dest));
}

isminetype CWallet::IsMine(const CScript& script) const
{
    isminetype result = ISMINE_NO;
    for (const auto& spk_man_pair : m_spk_managers) {
        result = std::max(result, spk_man_pair.second->IsMine(script));
    }
    return result;
}

CAmountMap CWallet::GetCredit(const CTransaction& tx, const size_t out_index, const isminefilter& filter) const
{
    {
        LOCK(cs_wallet);
        std::map<uint256, CWalletTx>::const_iterator mi = mapWallet.find(tx.GetHash());
        if (mi != mapWallet.end())
        {
            const CWalletTx& wtx = (*mi).second;
            if (out_index < wtx.tx->vout.size() && IsMine(wtx.tx->vout[out_index]) & filter) {
                CAmountMap amounts;
                amounts[wtx.GetOutputAsset(out_index)] = std::max<CAmount>(0, wtx.GetOutputValueOut(out_index));
                return amounts;
            }
        }
    }
    return CAmountMap();
}

bool CWallet::IsChange(const CTxOut& txout) const
{
    return IsChange(txout.scriptPubKey);
}

bool CWallet::IsChange(const CScript& script) const
{
    // TODO: fix handling of 'change' outputs. The assumption is that any
    // payment to a script that is ours, but is not in the address book
    // is change. That assumption is likely to break when we implement multisignature
    // wallets that return change back into a multi-signature-protected address;
    // a better way of identifying which outputs are 'the send' and which are
    // 'the change' will need to be implemented (maybe extend CWalletTx to remember
    // which output, if any, was change).
    if (IsMine(script))
    {
        CTxDestination address;
        if (!ExtractDestination(script, address))
            return true;

        LOCK(cs_wallet);
        if (!mapAddressBook.count(address))
            return true;
    }
    return false;
}

CAmountMap CWallet::GetChange(const CTxOut& txout) const
{
    CAmountMap change;
    change[txout.nAsset.GetAsset()] = txout.nValue.GetAmount();
    if (!MoneyRange(change))
        throw std::runtime_error(std::string(__func__) + ": value out of range");
    return (IsChange(txout) ? change : CAmountMap());
}

bool CWallet::IsMine(const CTransaction& tx) const
{
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

bool CWallet::IsAllFromMe(const CTransaction& tx, const isminefilter& filter) const
{
    LOCK(cs_wallet);

    for (const CTxIn& txin : tx.vin)
    {
        auto mi = mapWallet.find(txin.prevout.hash);
        if (mi == mapWallet.end())
            return false; // any unknown inputs can't be from us

        const CWalletTx& prev = (*mi).second;

        if (txin.prevout.n >= prev.tx->vout.size())
            return false; // invalid input!

        if (!(IsMine(prev.tx->vout[txin.prevout.n]) & filter))
            return false;
    }
    return true;
}

CAmountMap CWallet::GetCredit(const CWalletTx& wtx, const isminefilter& filter) const {
    CAmountMap nCredit;
    for (unsigned int i = 0; i < wtx.tx->vout.size(); ++i) {
        if (IsMine(wtx.tx->vout[i]) & filter) {
            CAmount credit = std::max<CAmount>(0, wtx.GetOutputValueOut(i));
            if (!MoneyRange(credit))
                throw std::runtime_error(std::string(__func__) + ": value out of range");

            nCredit[wtx.GetOutputAsset(i)] += credit;
            if (!MoneyRange(nCredit))
                throw std::runtime_error(std::string(__func__) + ": value out of range");
        }
    }
    return nCredit;
}

CAmountMap CWallet::GetChange(const CWalletTx& wtx) const {
    CAmountMap nChange;
    for (unsigned int i = 0; i < wtx.tx->vout.size(); ++i) {
        if (IsChange(wtx.tx->vout[i])) {
            CAmount change = wtx.GetOutputValueOut(i);
            if (change < 0) {
                continue;
            }

            if (!MoneyRange(change))
                throw std::runtime_error(std::string(__func__) + ": value out of range");

            nChange[wtx.GetOutputAsset(i)] += change;
            if (!MoneyRange(nChange))
                throw std::runtime_error(std::string(__func__) + ": value out of range");
        }
    }
    return nChange;
}

CAmountMap CWallet::GetChange(const CTransaction& tx) const
{
    CAmountMap nChange;
    for (const CTxOut& txout : tx.vout)
    {
        nChange += GetChange(txout);
        if (!MoneyRange(nChange))
            throw std::runtime_error(std::string(__func__) + ": value out of range");
    }
    return nChange;
}

bool CWallet::IsHDEnabled() const
{
    bool result = true;
    for (const auto& spk_man_pair : m_spk_managers) {
        result &= spk_man_pair.second->IsHDEnabled();
    }
    return result;
}

bool CWallet::CanGetAddresses(bool internal)
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
    if (!WalletBatch(*database).WriteWalletFlags(m_wallet_flags))
        throw std::runtime_error(std::string(__func__) + ": writing wallet flags failed");
}

void CWallet::UnsetWalletFlag(uint64_t flag)
{
    WalletBatch batch(*database);
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

bool CWallet::SetWalletFlags(uint64_t overwriteFlags, bool memonly)
{
    LOCK(cs_wallet);
    m_wallet_flags = overwriteFlags;
    if (((overwriteFlags & KNOWN_WALLET_FLAGS) >> 32) ^ (overwriteFlags >> 32)) {
        // contains unknown non-tolerable wallet flags
        return false;
    }
    if (!memonly && !WalletBatch(*database).WriteWalletFlags(m_wallet_flags)) {
        throw std::runtime_error(std::string(__func__) + ": writing wallet flags failed");
    }

    return true;
}

int64_t CWalletTx::GetTxTime() const
{
    int64_t n = nTimeSmart;
    return n ? n : nTimeReceived;
}

// Helper for producing a max-sized low-S low-R signature (eg 71 bytes)
// or a max-sized low-S signature (e.g. 72 bytes) if use_max_sig is true
static bool DummySignInput(const SigningProvider* provider, CMutableTransaction& tx, const size_t nIn, const CTxOut& txout, bool use_max_sig)
{
    // Fill in dummy signatures for fee calculation.
    const CScript& scriptPubKey = txout.scriptPubKey;
    SignatureData sigdata;

    if (!ProduceSignature(*provider, use_max_sig ? DUMMY_MAXIMUM_SIGNATURE_CREATOR : DUMMY_SIGNATURE_CREATOR, scriptPubKey, sigdata)) {
        return false;
    }
    UpdateTransaction(tx, nIn, sigdata);
    return true;
}

// Helper for producing a bunch of max-sized low-S low-R signatures (eg 71 bytes)
bool CWallet::DummySignTx(CMutableTransaction &txNew, const std::vector<CTxOut> &txouts, const CCoinControl* coin_control) const
{
    // Fill in dummy signatures for fee calculation.
    int nIn = 0;
    for (const auto& txout : txouts)
    {
        std::unique_ptr<SigningProvider> provider = GetSigningProvider(txout.scriptPubKey);
        // Use max sig if watch only inputs were used or if this particular input is an external input
        bool use_max_sig = coin_control && (coin_control->fAllowWatchOnly || (coin_control && coin_control->IsExternalSelected(txNew.vin[nIn].prevout)));
        if (!provider || !DummySignInput(provider.get(), txNew, nIn, txout, use_max_sig)) {
            if (!coin_control || !DummySignInput(&coin_control->m_external_provider, txNew, nIn, txout, use_max_sig)) {
                return false;
            }
        }

        nIn++;
    }
    return true;
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
        WalletBatch batch(*database);
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

int64_t CalculateMaximumSignedTxSize(const CTransaction &tx, const CWallet *wallet, const CCoinControl* coin_control)
{
    std::vector<CTxOut> txouts;
    // Look up the inputs. The inputs are either in the wallet, or in coin_control.
    for (const CTxIn& input : tx.vin) {
        const auto mi = wallet->mapWallet.find(input.prevout.hash);
        if (mi != wallet->mapWallet.end()) {
            assert(input.prevout.n < mi->second.tx->vout.size());
            txouts.emplace_back(mi->second.tx->vout[input.prevout.n]);
        } else if (coin_control) {
            CTxOut txout;
            if (!coin_control->GetExternalOutput(input.prevout, txout)) {
                return -1;
            }
            txouts.emplace_back(txout);
        } else {
            return -1;
        }
    }
    return CalculateMaximumSignedTxSize(tx, wallet, txouts, coin_control);
}

// txouts needs to be in the order of tx.vin
int64_t CalculateMaximumSignedTxSize(const CTransaction &tx, const CWallet *wallet, const std::vector<CTxOut>& txouts, const CCoinControl* coin_control)
{
    CMutableTransaction txNew(tx);
    if (!wallet->DummySignTx(txNew, txouts, coin_control)) {
        return -1;
    }
    return GetVirtualTransactionSize(CTransaction(txNew));
}

int CalculateMaximumSignedInputSize(const CTxOut& txout, const SigningProvider* provider, bool use_max_sig) {
    CMutableTransaction txn;
    txn.vin.push_back(CTxIn(COutPoint()));
    if (!provider || !DummySignInput(provider, txn, 0, txout, use_max_sig)) {
        return -1;
    }
    return GetVirtualTransactionInputSize(CTransaction(txn));
}

int CalculateMaximumSignedInputSize(const CTxOut& txout, const CWallet* wallet, bool use_max_sig)
{
    std::unique_ptr<SigningProvider> provider = wallet->GetSigningProvider(txout.scriptPubKey);
    return CalculateMaximumSignedInputSize(txout, provider.get(), use_max_sig);
}

void CWalletTx::GetAmounts(std::list<COutputEntry>& listReceived,
                           std::list<COutputEntry>& listSent, CAmount& nFee, const isminefilter& filter) const
{
    nFee = 0;
    listReceived.clear();
    listSent.clear();

    // Compute fee:
    CAmountMap mapDebit = GetDebit(filter);
    if (mapDebit > CAmountMap()) // debit>0 means we signed/sent this transaction
    {
        nFee = -GetFeeMap(*tx)[::policyAsset];
    }

    // Sent/received.
    for (unsigned int i = 0; i < tx->vout.size(); ++i)
    {
        const CTxOut& txout = tx->vout[i];
        CAmount output_value = GetOutputValueOut(i);
        // Don't list unknown assets
        isminetype fIsMine = output_value != -1 ?  pwallet->IsMine(txout) : ISMINE_NO;
        // Only need to handle txouts if AT LEAST one of these is true:
        //   1) they debit from us (sent)
        //   2) the output is to us (received)
        if (mapDebit > CAmountMap())
        {
            // Don't report 'change' txouts
            if (pwallet->IsChange(txout))
                continue;
        }
        else if (!(fIsMine & filter))
            continue;

        // In either case, we need to get the destination address
        CTxDestination address;

        if (!ExtractDestination(txout.scriptPubKey, address) && !txout.scriptPubKey.IsUnspendable())
        {
            pwallet->WalletLogPrintf("CWalletTx::GetAmounts: Unknown transaction type found, txid %s\n",
                                    this->GetHash().ToString());
            address = CNoDestination();
        }

        COutputEntry output = {address, output_value, (int)i, GetOutputAsset(i), GetOutputAmountBlindingFactor(i), GetOutputAssetBlindingFactor(i)};

        // If we are debited by the transaction, add the output as a "sent" entry
        if (mapDebit > CAmountMap() && !txout.IsFee())
            listSent.push_back(output);

        // If we are receiving the output, add it as a "received" entry
        if (fIsMine & filter)
            listReceived.push_back(output);
    }

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
    uint256 start_block;
    {
        auto locked_chain = chain().lock();
        const Optional<int> start_height = locked_chain->findFirstBlockWithTimeAndHeight(startTime - TIMESTAMP_WINDOW, 0, &start_block);
        const Optional<int> tip_height = locked_chain->getHeight();
        WalletLogPrintf("%s: Rescanning last %i blocks\n", __func__, tip_height && start_height ? *tip_height - *start_height + 1 : 0);
    }

    if (!start_block.IsNull()) {
        // TODO: this should take into account failure by ScanResult::USER_ABORT
        ScanResult result = ScanForWalletTransactions(start_block, {} /* stop_block */, reserver, update);
        if (result.status == ScanResult::FAILURE) {
            int64_t time_max;
            if (!chain().findBlock(result.last_failed_block, nullptr /* block */, nullptr /* time */, &time_max)) {
                throw std::logic_error("ScanForWalletTransactions returned invalid block hash");
            }
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
 * @param[in] stop_block  Scan ending block. If block is not on the active
 *                        chain, the scan will continue until it reaches the
 *                        chain tip.
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
CWallet::ScanResult CWallet::ScanForWalletTransactions(const uint256& start_block, const uint256& stop_block, const WalletRescanReserver& reserver, bool fUpdate)
{
    int64_t nNow = GetTime();
    int64_t start_time = GetTimeMillis();

    assert(reserver.isReserved());

    uint256 block_hash = start_block;
    ScanResult result;

    WalletLogPrintf("Rescan started from block %s...\n", start_block.ToString());

    fAbortRescan = false;
    ShowProgress(strprintf("%s " + _("Rescanning...").translated, GetDisplayName()), 0); // show rescan progress in GUI as dialog or on splashscreen, if -rescan on startup
    uint256 tip_hash;
    // The way the 'block_height' is initialized is just a workaround for the gcc bug #47679 since version 4.6.0.
    Optional<int> block_height = MakeOptional(false, int());
    double progress_begin;
    double progress_end;
    {
        auto locked_chain = chain().lock();
        if (Optional<int> tip_height = locked_chain->getHeight()) {
            tip_hash = locked_chain->getBlockHash(*tip_height);
        }
        block_height = locked_chain->getBlockHeight(block_hash);
        progress_begin = chain().guessVerificationProgress(block_hash);
        progress_end = chain().guessVerificationProgress(stop_block.IsNull() ? tip_hash : stop_block);
    }
    double progress_current = progress_begin;
    while (block_height && !fAbortRescan && !chain().shutdownRequested()) {
        m_scanning_progress = (progress_current - progress_begin) / (progress_end - progress_begin);
        if (*block_height % 100 == 0 && progress_end - progress_begin > 0.0) {
            ShowProgress(strprintf("%s " + _("Rescanning...").translated, GetDisplayName()), std::max(1, std::min(99, (int)(m_scanning_progress * 100))));
        }
        if (GetTime() >= nNow + 60) {
            nNow = GetTime();
            WalletLogPrintf("Still rescanning. At block %d. Progress=%f\n", *block_height, progress_current);
        }

        CBlock block;
        if (chain().findBlock(block_hash, &block) && !block.IsNull()) {
            auto locked_chain = chain().lock();
            LOCK(cs_wallet);
            if (!locked_chain->getBlockHeight(block_hash)) {
                // Abort scan if current block is no longer active, to prevent
                // marking transactions as coming from the wrong block.
                // TODO: This should return success instead of failure, see
                // https://github.com/bitcoin/bitcoin/pull/14711#issuecomment-458342518
                result.last_failed_block = block_hash;
                result.status = ScanResult::FAILURE;
                break;
            }
            for (size_t posInBlock = 0; posInBlock < block.vtx.size(); ++posInBlock) {
                CWalletTx::Confirmation confirm(CWalletTx::Status::CONFIRMED, *block_height, block_hash, posInBlock);
                SyncTransaction(block.vtx[posInBlock], confirm, fUpdate);
            }
            // scan succeeded, record block as most recent successfully scanned
            result.last_scanned_block = block_hash;
            result.last_scanned_height = *block_height;
        } else {
            // could not scan block, keep scanning but record this block as the most recent failure
            result.last_failed_block = block_hash;
            result.status = ScanResult::FAILURE;
        }
        if (block_hash == stop_block) {
            break;
        }
        {
            auto locked_chain = chain().lock();
            Optional<int> tip_height = locked_chain->getHeight();
            if (!tip_height || *tip_height <= block_height || !locked_chain->getBlockHeight(block_hash)) {
                // break successfully when rescan has reached the tip, or
                // previous block is no longer on the chain due to a reorg
                break;
            }

            // increment block and verification progress
            block_hash = locked_chain->getBlockHash(++*block_height);
            progress_current = chain().guessVerificationProgress(block_hash);

            // handle updated tip hash
            const uint256 prev_tip_hash = tip_hash;
            tip_hash = locked_chain->getBlockHash(*tip_height);
            if (stop_block.IsNull() && prev_tip_hash != tip_hash) {
                // in case the tip has changed, update progress max
                progress_end = chain().guessVerificationProgress(tip_hash);
            }
        }
    }
    ShowProgress(strprintf("%s " + _("Rescanning...").translated, GetDisplayName()), 100); // hide progress dialog in GUI
    if (block_height && fAbortRescan) {
        WalletLogPrintf("Rescan aborted at block %d. Progress=%f\n", *block_height, progress_current);
        result.status = ScanResult::USER_ABORT;
    } else if (block_height && chain().shutdownRequested()) {
        WalletLogPrintf("Rescan interrupted by shutdown request at block %d. Progress=%f\n", *block_height, progress_current);
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

        int nDepth = wtx.GetDepthInMainChain();

        if (!wtx.IsCoinBase() && (nDepth == 0 && !wtx.isAbandoned())) {
            mapSorted.insert(std::make_pair(wtx.nOrderPos, &wtx));
        }
    }

    // Try to add wallet transactions to memory pool
    for (const std::pair<const int64_t, CWalletTx*>& item : mapSorted) {
        CWalletTx& wtx = *(item.second);
        std::string unused_err_string;
        wtx.SubmitMemoryPoolAndRelay(unused_err_string, false);
    }
}

bool CWalletTx::SubmitMemoryPoolAndRelay(std::string& err_string, bool relay)
{
    // Can't relay if wallet is not broadcasting
    if (!pwallet->GetBroadcastTransactions()) return false;
    // Don't relay abandoned transactions
    if (isAbandoned()) return false;
    // Don't try to submit coinbase transactions. These would fail anyway but would
    // cause log spam.
    if (IsCoinBase()) return false;
    // Don't try to submit conflicted or confirmed transactions.
    if (GetDepthInMainChain() != 0) return false;

    // Submit transaction to mempool for relay
    pwallet->WalletLogPrintf("Submitting wtx %s to mempool for relay\n", GetHash().ToString());
    // We must set fInMempool here - while it will be re-set to true by the
    // entered-mempool callback, if we did not there would be a race where a
    // user could call sendmoney in a loop and hit spurious out of funds errors
    // because we think that this newly generated transaction's change is
    // unavailable as we're not yet aware that it is in the mempool.
    //
    // Irrespective of the failure reason, un-marking fInMempool
    // out-of-order is incorrect - it should be unmarked when
    // TransactionRemovedFromMempool fires.
    bool ret = pwallet->chain().broadcastTransaction(tx, err_string, pwallet->m_default_max_tx_fee, relay);
    fInMempool |= ret;
    return ret;
}

std::set<uint256> CWalletTx::GetConflicts() const
{
    std::set<uint256> result;
    if (pwallet != nullptr)
    {
        uint256 myHash = GetHash();
        result = pwallet->GetConflicts(myHash);
        result.erase(myHash);
    }
    return result;
}

CAmountMap CWalletTx::GetCachableAmount(AmountType type, const isminefilter& filter, bool recalculate) const
{
    auto& amount = m_amounts[type];
    if (recalculate || !amount.m_cached[filter]) {
        amount.Set(filter, type == DEBIT ? pwallet->GetDebit(*tx, filter) : pwallet->GetCredit(*this, filter));
        m_is_cache_empty = false;
    }
    return amount.m_value[filter];
}

CAmountMap CWalletTx::GetDebit(const isminefilter& filter) const
{
    if (tx->vin.empty())
        return CAmountMap();

    CAmountMap debit;
    if (filter & ISMINE_SPENDABLE) {
        debit += GetCachableAmount(DEBIT, ISMINE_SPENDABLE);
    }
    if (filter & ISMINE_WATCH_ONLY) {
        debit += GetCachableAmount(DEBIT, ISMINE_WATCH_ONLY);
    }
    return debit;
}

CAmountMap CWalletTx::GetCredit(const isminefilter& filter) const
{
    // Must wait until coinbase is safely deep enough in the chain before valuing it
    if (IsImmatureCoinBase())
        return CAmountMap();

    CAmountMap credit;
    if (filter & ISMINE_SPENDABLE) {
        // GetBalance can assume transactions in mapWallet won't change
        credit += GetCachableAmount(CREDIT, ISMINE_SPENDABLE);
    }
    if (filter & ISMINE_WATCH_ONLY) {
        credit += GetCachableAmount(CREDIT, ISMINE_WATCH_ONLY);
    }
    return credit;
}

CAmountMap CWalletTx::GetImmatureCredit(bool fUseCache) const
{
    if (IsImmatureCoinBase() && IsInMainChain()) {
        return GetCachableAmount(IMMATURE_CREDIT, ISMINE_SPENDABLE, !fUseCache);
    }

    return CAmountMap();
}

CAmountMap CWalletTx::GetAvailableCredit(bool fUseCache, const isminefilter& filter) const
{
    if (pwallet == nullptr)
        return CAmountMap();

    // Avoid caching ismine for NO or ALL cases (could remove this check and simplify in the future).
    bool allow_cache = (filter & ISMINE_ALL) && (filter & ISMINE_ALL) != ISMINE_ALL;

    // Must wait until coinbase is safely deep enough in the chain before valuing it
    if (IsImmatureCoinBase())
        return CAmountMap();

    if (fUseCache && allow_cache && m_amounts[AVAILABLE_CREDIT].m_cached[filter]) {
        return m_amounts[AVAILABLE_CREDIT].m_value[filter];
    }

    bool allow_used_addresses = (filter & ISMINE_USED) || !pwallet->IsWalletFlagSet(WALLET_FLAG_AVOID_REUSE);
    CAmountMap nCredit;
    uint256 hashTx = GetHash();
    for (unsigned int i = 0; i < tx->vout.size(); i++)
    {
        if (!pwallet->IsSpent(hashTx, i) && (allow_used_addresses || !pwallet->IsSpentKey(hashTx, i))) {
            if (pwallet->IsMine(tx->vout[i]) & filter) {
                CAmount credit = std::max<CAmount>(0, GetOutputValueOut(i));
                if (!MoneyRange(credit))
                    throw std::runtime_error(std::string(__func__) + ": value out of range");

                nCredit[GetOutputAsset(i)] += std::max<CAmount>(0, GetOutputValueOut(i));
                if (!MoneyRange(nCredit))
                    throw std::runtime_error(std::string(__func__) + ": value out of range");
            }
        }
    }

    if (allow_cache) {
        m_amounts[AVAILABLE_CREDIT].Set(filter, nCredit);
        m_is_cache_empty = false;
    }

    return nCredit;
}

CAmountMap CWalletTx::GetImmatureWatchOnlyCredit(const bool fUseCache) const
{
    if (IsImmatureCoinBase() && IsInMainChain()) {
        return GetCachableAmount(IMMATURE_CREDIT, ISMINE_WATCH_ONLY, !fUseCache);
    }

    return CAmountMap();
}

CAmountMap CWalletTx::GetChange() const
{
    if (fChangeCached)
        return nChangeCached;
    nChangeCached = pwallet->GetChange(*this);
    fChangeCached = true;
    return nChangeCached;
}

bool CWalletTx::InMempool() const
{
    return fInMempool;
}

bool CWalletTx::IsTrusted(interfaces::Chain::Lock& locked_chain) const
{
    std::set<uint256> s;
    return IsTrusted(locked_chain, s);
}

bool CWalletTx::IsTrusted(interfaces::Chain::Lock& locked_chain, std::set<uint256>& trusted_parents) const
{
    // Quick answer in most cases
    if (!locked_chain.checkFinalTx(*tx)) return false;
    int nDepth = GetDepthInMainChain();
    if (nDepth >= 1) return true;
    if (nDepth < 0) return false;
    // using wtx's cached debit
    if (!pwallet->m_spend_zero_conf_change || !IsFromMe(ISMINE_ALL)) return false;

    // Don't trust unconfirmed transactions from us unless they are in the mempool.
    if (!InMempool()) return false;

    // Trusted if all inputs are from us and are in the mempool:
    for (const CTxIn& txin : tx->vin)
    {
        // Transactions not sent by us: not trusted
        const CWalletTx* parent = pwallet->GetWalletTx(txin.prevout.hash);
        if (parent == nullptr) return false;
        const CTxOut& parentOut = parent->tx->vout[txin.prevout.n];
        // Check that this specific input being spent is trusted
        if (pwallet->IsMine(parentOut) != ISMINE_SPENDABLE) return false;
        // If we've already trusted this parent, continue
        if (trusted_parents.count(parent->GetHash())) continue;
        // Recurse to check that the parent is also trusted
        if (!parent->IsTrusted(locked_chain, trusted_parents)) return false;
        trusted_parents.insert(parent->GetHash());
    }
    return true;
}

bool CWalletTx::IsEquivalentTo(const CWalletTx& _tx) const
{
        CMutableTransaction tx1 {*this->tx};
        CMutableTransaction tx2 {*_tx.tx};
        for (auto& txin : tx1.vin) txin.scriptSig = CScript();
        for (auto& txin : tx2.vin) txin.scriptSig = CScript();
        return CTransaction(tx1) == CTransaction(tx2);
}

CAmountMap CWalletTx::GetIssuanceAssets(unsigned int input_index) const {
    CAmountMap ret;
    CAsset asset, token;
    GetIssuanceAssets(input_index, &asset, &token);
    if (!asset.IsNull()) {
        ret[asset] = GetIssuanceAmount(input_index, false);
    }
    if (!token.IsNull()) {
        ret[token] = GetIssuanceAmount(input_index, true);
    }
    return ret;
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
    nNextResend = GetTime() + GetRand(30 * 60);
    if (fFirst) return;

    // Only do it if there's been a new block since last time
    if (m_best_block_time < nLastResend) return;
    nLastResend = GetTime();

    int submitted_tx_count = 0;

    { // locked_chain and cs_wallet scope
        auto locked_chain = chain().lock();
        LOCK(cs_wallet);

        // Relay transactions
        for (std::pair<const uint256, CWalletTx>& item : mapWallet) {
            CWalletTx& wtx = item.second;
            // Attempt to rebroadcast all txes more than 5 minutes older than
            // the last block. SubmitMemoryPoolAndRelay() will not rebroadcast
            // any confirmed or conflicting txs.
            if (wtx.nTimeReceived > m_best_block_time - 5 * 60) continue;
            std::string unused_err_string;
            if (wtx.SubmitMemoryPoolAndRelay(unused_err_string, true)) ++submitted_tx_count;
        }
    } // locked_chain and cs_wallet

    if (submitted_tx_count > 0) {
        WalletLogPrintf("%s: resubmit %u unconfirmed transactions\n", __func__, submitted_tx_count);
    }
}

/** @} */ // end of mapWallet

void MaybeResendWalletTxs()
{
    for (const std::shared_ptr<CWallet>& pwallet : GetWallets()) {
        pwallet->ResendWalletTransactions();
    }
}


/** @defgroup Actions
 *
 * @{
 */


CWallet::Balance CWallet::GetBalance(const int min_depth, bool avoid_reuse) const
{
    Balance ret;
    isminefilter reuse_filter = avoid_reuse ? ISMINE_NO : ISMINE_USED;
    {
        auto locked_chain = chain().lock();
        LOCK(cs_wallet);
        std::set<uint256> trusted_parents;
        for (const auto& entry : mapWallet)
        {
            const CWalletTx& wtx = entry.second;
            const bool is_trusted{wtx.IsTrusted(*locked_chain, trusted_parents)};
            const int tx_depth{wtx.GetDepthInMainChain()};
            const CAmountMap tx_credit_mine{wtx.GetAvailableCredit(/* fUseCache */ true, ISMINE_SPENDABLE | reuse_filter)};
            const CAmountMap tx_credit_watchonly{wtx.GetAvailableCredit(/* fUseCache */ true, ISMINE_WATCH_ONLY | reuse_filter)};
            if (is_trusted && tx_depth >= min_depth) {
                ret.m_mine_trusted += tx_credit_mine;
                ret.m_watchonly_trusted += tx_credit_watchonly;
            }
            if (!is_trusted && tx_depth == 0 && wtx.InMempool()) {
                ret.m_mine_untrusted_pending += tx_credit_mine;
                ret.m_watchonly_untrusted_pending += tx_credit_watchonly;
            }
            ret.m_mine_immature += wtx.GetImmatureCredit();
            ret.m_watchonly_immature += wtx.GetImmatureWatchOnlyCredit();
        }
    }
    return ret;
}

CAmountMap CWallet::GetAvailableBalance(const CCoinControl* coinControl) const
{
    auto locked_chain = chain().lock();
    LOCK(cs_wallet);

    CAmountMap balance;
    std::vector<COutput> vCoins;
    AvailableCoins(*locked_chain, vCoins, true, coinControl);
    for (const COutput& out : vCoins) {
        if (out.fSpendable) {
            CAmount amt = out.tx->GetOutputValueOut(out.i);
            if (amt < 0) {
                continue;
            }
            balance[out.tx->GetOutputAsset(out.i)] += amt;
        }
    }
    return balance;
}

void CWallet::AvailableCoins(interfaces::Chain::Lock& locked_chain, std::vector<COutput> &vCoins, bool fOnlySafe, const CCoinControl *coinControl, const CAmount &nMinimumAmount, const CAmount &nMaximumAmount, const CAmount &nMinimumSumAmount, const uint64_t nMaximumCount, const CAsset* asset_filter) const
{
    AssertLockHeld(cs_wallet);

    vCoins.clear();
    CAmount nTotal = 0;
    // Either the WALLET_FLAG_AVOID_REUSE flag is not set (in which case we always allow), or we default to avoiding, and only in the case where
    // a coin control object is provided, and has the avoid address reuse flag set to false, do we allow already used addresses
    bool allow_used_addresses = !IsWalletFlagSet(WALLET_FLAG_AVOID_REUSE) || (coinControl && !coinControl->m_avoid_address_reuse);
    const int min_depth = {coinControl ? coinControl->m_min_depth : DEFAULT_MIN_DEPTH};
    const int max_depth = {coinControl ? coinControl->m_max_depth : DEFAULT_MAX_DEPTH};

    std::set<uint256> trusted_parents;
    for (const auto& entry : mapWallet)
    {
        const uint256& wtxid = entry.first;
        const CWalletTx& wtx = entry.second;

        if (!locked_chain.checkFinalTx(*wtx.tx)) {
            continue;
        }

        if (wtx.IsImmatureCoinBase())
            continue;

        int nDepth = wtx.GetDepthInMainChain();
        if (nDepth < 0)
            continue;

        // We should not consider coins which aren't at least in our mempool
        // It's possible for these to be conflicted via ancestors which we may never be able to detect
        if (nDepth == 0 && !wtx.InMempool())
            continue;

        bool safeTx = wtx.IsTrusted(locked_chain, trusted_parents);

        // We should not consider coins from transactions that are replacing
        // other transactions.
        //
        // Example: There is a transaction A which is replaced by bumpfee
        // transaction B. In this case, we want to prevent creation of
        // a transaction B' which spends an output of B.
        //
        // Reason: If transaction A were initially confirmed, transactions B
        // and B' would no longer be valid, so the user would have to create
        // a new transaction C to replace B'. However, in the case of a
        // one-block reorg, transactions B' and C might BOTH be accepted,
        // when the user only wanted one of them. Specifically, there could
        // be a 1-block reorg away from the chain where transactions A and C
        // were accepted to another chain where B, B', and C were all
        // accepted.
        if (nDepth == 0 && wtx.mapValue.count("replaces_txid")) {
            safeTx = false;
        }

        // Similarly, we should not consider coins from transactions that
        // have been replaced. In the example above, we would want to prevent
        // creation of a transaction A' spending an output of A, because if
        // transaction B were initially confirmed, conflicting with A and
        // A', we wouldn't want to the user to create a transaction D
        // intending to replace A', but potentially resulting in a scenario
        // where A, A', and D could all be accepted (instead of just B and
        // D, or just A and A' like the user would want).
        if (nDepth == 0 && wtx.mapValue.count("replaced_by_txid")) {
            safeTx = false;
        }

        if (fOnlySafe && !safeTx) {
            continue;
        }

        if (nDepth < min_depth || nDepth > max_depth) {
            continue;
        }

        for (unsigned int i = 0; i < wtx.tx->vout.size(); i++) {
            CAmount outValue = wtx.GetOutputValueOut(i);
            CAsset asset = wtx.GetOutputAsset(i);
            if (asset_filter && asset != *asset_filter) {
                continue;
            }
            if (outValue < nMinimumAmount || outValue > nMaximumAmount)
                continue;

            if (coinControl && coinControl->HasSelected() && !coinControl->fAllowOtherInputs && !coinControl->IsSelected(COutPoint(entry.first, i)))
                continue;

            if (IsLockedCoin(entry.first, i))
                continue;

            if (IsSpent(wtxid, i))
                continue;

            isminetype mine = IsMine(wtx.tx->vout[i]);

            if (mine == ISMINE_NO) {
                continue;
            }

            if (!allow_used_addresses && IsSpentKey(wtxid, i)) {
                continue;
            }

            std::unique_ptr<SigningProvider> provider = GetSigningProvider(wtx.tx->vout[i].scriptPubKey);

            bool solvable = provider ? IsSolvable(*provider, wtx.tx->vout[i].scriptPubKey) : false;
            bool spendable = ((mine & ISMINE_SPENDABLE) != ISMINE_NO) || (((mine & ISMINE_WATCH_ONLY) != ISMINE_NO) && (coinControl && coinControl->fAllowWatchOnly && solvable));

            vCoins.push_back(COutput(&wtx, i, nDepth, spendable, solvable, safeTx, (coinControl && coinControl->fAllowWatchOnly)));

            // Checks the sum amount of all UTXO's.
            if (nMinimumSumAmount != MAX_MONEY) {
                nTotal += outValue;

                if (nTotal >= nMinimumSumAmount) {
                    return;
                }
            }

            // Checks the maximum number of UTXO's.
            if (nMaximumCount > 0 && vCoins.size() >= nMaximumCount) {
                return;
            }
        }
    }
}

std::map<CTxDestination, std::vector<COutput>> CWallet::ListCoins(interfaces::Chain::Lock& locked_chain) const
{
    AssertLockHeld(cs_wallet);

    std::map<CTxDestination, std::vector<COutput>> result;
    std::vector<COutput> availableCoins;

    AvailableCoins(locked_chain, availableCoins);

    for (const COutput& coin : availableCoins) {
        CTxDestination address;
        if ((coin.fSpendable || (IsWalletFlagSet(WALLET_FLAG_DISABLE_PRIVATE_KEYS) && coin.fSolvable)) &&
            ExtractDestination(FindNonChangeParentOutput(*coin.tx->tx, coin.i).scriptPubKey, address)) {
            result[address].emplace_back(std::move(coin));
        }
    }

    std::vector<COutPoint> lockedCoins;
    ListLockedCoins(lockedCoins);
    // Include watch-only for LegacyScriptPubKeyMan wallets without private keys
    const bool include_watch_only = GetLegacyScriptPubKeyMan() && IsWalletFlagSet(WALLET_FLAG_DISABLE_PRIVATE_KEYS);
    const isminetype is_mine_filter = include_watch_only ? ISMINE_WATCH_ONLY : ISMINE_SPENDABLE;
    for (const COutPoint& output : lockedCoins) {
        auto it = mapWallet.find(output.hash);
        if (it != mapWallet.end()) {
            int depth = it->second.GetDepthInMainChain();
            if (depth >= 0 && output.n < it->second.tx->vout.size() &&
                IsMine(it->second.tx->vout[output.n]) == is_mine_filter
            ) {
                CTxDestination address;
                if (ExtractDestination(FindNonChangeParentOutput(*it->second.tx, output.n).scriptPubKey, address)) {
                    result[address].emplace_back(
                        &it->second, output.n, depth, true /* spendable */, true /* solvable */, false /* safe */);
                }
            }
        }
    }

    return result;
}

const CTxOut& CWallet::FindNonChangeParentOutput(const CTransaction& tx, int output) const
{
    const CTransaction* ptx = &tx;
    int n = output;
    while (IsChange(ptx->vout[n]) && ptx->vin.size() > 0) {
        const COutPoint& prevout = ptx->vin[0].prevout;
        auto it = mapWallet.find(prevout.hash);
        if (it == mapWallet.end() || it->second.tx->vout.size() <= prevout.n ||
            !IsMine(it->second.tx->vout[prevout.n])) {
            break;
        }
        ptx = it->second.tx.get();
        n = prevout.n;
    }
    return ptx->vout[n];
}

bool CWallet::SelectCoinsMinConf(const CAmountMap& mapTargetValue, const CoinEligibilityFilter& eligibility_filter, std::vector<OutputGroup> groups,
                                 std::set<CInputCoin>& setCoinsRet, CAmountMap& mapValueRet, const CoinSelectionParams& coin_selection_params, bool& bnb_used) const
{
    setCoinsRet.clear();
    mapValueRet.clear();

    std::vector<OutputGroup> utxo_pool;
    if (coin_selection_params.use_bnb && mapTargetValue.size() == 1) {
        // ELEMENTS:
        CAsset asset = mapTargetValue.begin()->first;
        CAmount nTargetValue = mapTargetValue.begin()->second;
        // Get output groups that only contain this asset.
        std::vector<OutputGroup> asset_groups;
        for (OutputGroup g : groups) {
            bool add = true;
            for (CInputCoin c : g.m_outputs) {
                if (c.asset != asset) {
                    add = false;
                    break;
                }
            }

            if (add) {
                asset_groups.push_back(g);
            }
        }
        // END ELEMENTS

        // Get long term estimate
        FeeCalculation feeCalc;
        CCoinControl temp;
        temp.m_confirm_target = 1008;
        CFeeRate long_term_feerate = GetMinimumFeeRate(*this, temp, &feeCalc);

        // Calculate cost of change
        CAmount cost_of_change = GetDiscardRate(*this).GetFee(coin_selection_params.change_spend_size) + coin_selection_params.effective_fee.GetFee(coin_selection_params.change_output_size);

        // Filter by the min conf specs and add to utxo_pool and calculate effective value
        for (OutputGroup& group : asset_groups) {
            if (!group.EligibleForSpending(eligibility_filter)) continue;

            group.fee = 0;
            group.long_term_fee = 0;
            group.effective_value = 0;
            for (auto it = group.m_outputs.begin(); it != group.m_outputs.end(); ) {
                const CInputCoin& coin = *it;
                CAmount effective_value = coin.value - (coin.m_input_bytes < 0 ? 0 : coin_selection_params.effective_fee.GetFee(coin.m_input_bytes));
                // Only include outputs that are positive effective value (i.e. not dust)
                if (effective_value > 0) {
                    group.fee += coin.m_input_bytes < 0 ? 0 : coin_selection_params.effective_fee.GetFee(coin.m_input_bytes);
                    group.long_term_fee += coin.m_input_bytes < 0 ? 0 : long_term_feerate.GetFee(coin.m_input_bytes);
                    if (coin_selection_params.m_subtract_fee_outputs) {
                        group.effective_value += coin.value;
                    } else {
                        group.effective_value += effective_value;
                    }
                    ++it;
                } else {
                    it = group.Discard(coin);
                }
            }
            if (group.effective_value > 0) utxo_pool.push_back(group);
        }
        // Calculate the fees for things that aren't inputs
        CAmount not_input_fees = coin_selection_params.effective_fee.GetFee(coin_selection_params.tx_noinputs_size);
        bnb_used = true;
        CAmount nValueRet;
        bool ret = SelectCoinsBnB(utxo_pool, nTargetValue, cost_of_change, setCoinsRet, nValueRet, not_input_fees);
        mapValueRet[asset] = nValueRet;
        return ret;
    } else {
        // Filter by the min conf specs and add to utxo_pool
        for (const OutputGroup& group : groups) {
            if (!group.EligibleForSpending(eligibility_filter)) continue;
            utxo_pool.push_back(group);
        }
        bnb_used = false;
        return KnapsackSolver(mapTargetValue, utxo_pool, setCoinsRet, mapValueRet);
    }
}

bool CWallet::SelectCoins(const std::vector<COutput>& vAvailableCoins, const CAmountMap& mapTargetValue, std::set<CInputCoin>& setCoinsRet, CAmountMap& mapValueRet, const CCoinControl& coin_control, CoinSelectionParams& coin_selection_params, bool& bnb_used) const
{
    AssertLockHeld(cs_wallet); // mapWallet
    std::vector<COutput> vCoins(vAvailableCoins);
    CAmountMap value_to_select = mapTargetValue;

    // Default to bnb was not used. If we use it, we set it later
    bnb_used = false;

    // coin control -> return all selected outputs (we want all selected to go into the transaction for sure)
    if (coin_control.HasSelected() && !coin_control.fAllowOtherInputs)
    {
        for (const COutput& out : vCoins)
        {
            if (!out.fSpendable)
                 continue;

            CAmount amt = out.tx->GetOutputValueOut(out.i);
            if (amt < 0) {
                continue;
            }
            mapValueRet[out.tx->GetOutputAsset(out.i)] += amt;
            setCoinsRet.insert(out.GetInputCoin());
        }
        return (mapValueRet >= mapTargetValue);
    }

    // calculate value from preset inputs and store them
    std::set<CInputCoin> setPresetCoins;
    CAmountMap mapValueFromPresetInputs;

    std::vector<COutPoint> vPresetInputs;
    coin_control.ListSelected(vPresetInputs);
    for (const COutPoint& outpoint : vPresetInputs)
    {
        std::map<uint256, CWalletTx>::const_iterator it = mapWallet.find(outpoint.hash);
        // ELEMENTS: this code pulled from unmerged Core PR #17211
        int input_bytes = -1;
        CTxOut txout;
        CInputCoin coin(outpoint, txout, 0); // dummy initialization
        if (it != mapWallet.end()) {
            const CWalletTx& wtx = it->second;
            // Clearly invalid input, fail
            if (wtx.tx->vout.size() <= outpoint.n) {
                return false;
            }
            // Just to calculate the marginal byte size
            if (wtx.GetOutputValueOut(outpoint.n) < 0) {
                continue;
            }
            input_bytes = wtx.GetSpendSize(outpoint.n, false);
            txout = wtx.tx->vout[outpoint.n];
            // ELEMENTS: must assign coin from wtx if we can, so the wallet
            //  can look up any confidential amounts/assets
            coin = CInputCoin(&wtx, outpoint.n, input_bytes);
        }
        if (input_bytes == -1) {
            // The input is external. We either did not find the tx in mapWallet, or we did but couldn't compute the input size with wallet data
            if (!coin_control.GetExternalOutput(outpoint, txout)) {
                // Not ours, and we don't have solving data.
                return false;
            }
            input_bytes = CalculateMaximumSignedInputSize(txout, &coin_control.m_external_provider, /* use_max_sig */ true);
            // ELEMENTS: one more try to get a signed input size: for pegins,
            //  the outpoint is provided as external data but the information
            //  needed to spend is in the wallet (not the external provider,
            //  as the user is expecting the wallet to remember this information
            //  after they called getpeginaddress). So try estimating size with
            //  the wallet rather than the external provider.
            if (input_bytes == -1) {
                input_bytes = CalculateMaximumSignedInputSize(txout, this, /* use_max_sig */ true);
            }
            if (!txout.nValue.IsExplicit() || !txout.nAsset.IsExplicit()) {
                return false; // We can't get its value, so abort
            }
            coin = CInputCoin(outpoint, txout, input_bytes);
        }

        mapValueFromPresetInputs[coin.asset] += coin.value;
        if (coin.m_input_bytes <= 0) {
            // ELEMENTS: if we're here we can't compute the coin's effective value. At
	    //  this point in the rebase this is only used for BnB, and our functional
            //  tests expect the user to get a "missing data" error rather than an
            //  "insufficient funds" error, which means we need some way to make
            //  SelectCoins pass. So rather than "return false;" as in upstream we
            //  just turn off bnb and keep going.
            coin_selection_params.use_bnb = false;
            coin.m_input_bytes = 0;
        }
        coin.effective_value = coin.value - coin_selection_params.effective_fee.GetFee(coin.m_input_bytes);
        if (coin_selection_params.use_bnb) {
            value_to_select[coin.asset] -= coin.effective_value;
        } else {
            value_to_select[coin.asset] -= coin.value;
        }
        setPresetCoins.insert(coin);
    }

    // remove preset inputs from vCoins
    for (std::vector<COutput>::iterator it = vCoins.begin(); it != vCoins.end() && coin_control.HasSelected();)
    {
        if (setPresetCoins.count(it->GetInputCoin()))
            it = vCoins.erase(it);
        else
            ++it;
    }

    // ELEMENTS: filter coins for assets we are interested in; always keep policyAsset for fees
    for (std::vector<COutput>::iterator it = vCoins.begin(); it != vCoins.end() && coin_control.HasSelected();) {
        CAsset asset = it->GetInputCoin().asset;
        if (asset != ::policyAsset && mapTargetValue.find(asset) == mapTargetValue.end()) {
            it = vCoins.erase(it);
        } else {
            ++it;
        }
    }

    // form groups from remaining coins; note that preset coins will not
    // automatically have their associated (same address) coins included
    if (coin_control.m_avoid_partial_spends && vCoins.size() > OUTPUT_GROUP_MAX_ENTRIES) {
        // Cases where we have 11+ outputs all pointing to the same destination may result in
        // privacy leaks as they will potentially be deterministically sorted. We solve that by
        // explicitly shuffling the outputs before processing
        Shuffle(vCoins.begin(), vCoins.end(), FastRandomContext());
    }
    std::vector<OutputGroup> groups = GroupOutputs(vCoins, !coin_control.m_avoid_partial_spends);

    unsigned int limit_ancestor_count;
    unsigned int limit_descendant_count;
    chain().getPackageLimits(limit_ancestor_count, limit_descendant_count);
    size_t max_ancestors = (size_t)std::max<int64_t>(1, limit_ancestor_count);
    size_t max_descendants = (size_t)std::max<int64_t>(1, limit_descendant_count);
    bool fRejectLongChains = gArgs.GetBoolArg("-walletrejectlongchains", DEFAULT_WALLET_REJECT_LONG_CHAINS);

    // We will have to do coin selection on the difference between the target and the provided values.
    // If value_to_select <= 0 for all asset types, we are done; but unlike in Bitcoin, this may be
    // true for some assets whlie being false for others. So clear all the "completed" assets out
    // of value_to_select before calling SelectCoinsMinConf.
    for (CAmountMap::const_iterator it = value_to_select.begin(); it != value_to_select.end();) {
        if (it->second <= 0) {
            it = value_to_select.erase(it);
        } else {
            ++it;
        }
    }

    bool res = value_to_select.empty() ||
        SelectCoinsMinConf(value_to_select, CoinEligibilityFilter(1, 6, 0), groups, setCoinsRet, mapValueRet, coin_selection_params, bnb_used) ||
        SelectCoinsMinConf(value_to_select, CoinEligibilityFilter(1, 1, 0), groups, setCoinsRet, mapValueRet, coin_selection_params, bnb_used) ||
        (m_spend_zero_conf_change && SelectCoinsMinConf(value_to_select, CoinEligibilityFilter(0, 1, 2), groups, setCoinsRet, mapValueRet, coin_selection_params, bnb_used)) ||
        (m_spend_zero_conf_change && SelectCoinsMinConf(value_to_select, CoinEligibilityFilter(0, 1, std::min((size_t)4, max_ancestors/3), std::min((size_t)4, max_descendants/3)), groups, setCoinsRet, mapValueRet, coin_selection_params, bnb_used)) ||
        (m_spend_zero_conf_change && SelectCoinsMinConf(value_to_select, CoinEligibilityFilter(0, 1, max_ancestors/2, max_descendants/2), groups, setCoinsRet, mapValueRet, coin_selection_params, bnb_used)) ||
        (m_spend_zero_conf_change && SelectCoinsMinConf(value_to_select, CoinEligibilityFilter(0, 1, max_ancestors-1, max_descendants-1), groups, setCoinsRet, mapValueRet, coin_selection_params, bnb_used)) ||
        (m_spend_zero_conf_change && !fRejectLongChains && SelectCoinsMinConf(value_to_select, CoinEligibilityFilter(0, 1, std::numeric_limits<uint64_t>::max()), groups, setCoinsRet, mapValueRet, coin_selection_params, bnb_used));

    // because SelectCoinsMinConf clears the setCoinsRet, we now add the possible inputs to the coinset
    util::insert(setCoinsRet, setPresetCoins);

    // add preset inputs to the total value selected
    mapValueRet += mapValueFromPresetInputs;

    return res;
}

bool CWallet::SignTransaction(CMutableTransaction& tx)
{
    AssertLockHeld(cs_wallet);

    // sign the new tx
    int nIn = 0;
    for (auto& input : tx.vin) {
        std::map<uint256, CWalletTx>::const_iterator mi = mapWallet.find(input.prevout.hash);
        if(mi == mapWallet.end() || input.prevout.n >= mi->second.tx->vout.size()) {
            return false;
        }
        const CScript& scriptPubKey = mi->second.tx->vout[input.prevout.n].scriptPubKey;
        const CConfidentialValue& amount = mi->second.tx->vout[input.prevout.n].nValue;
        SignatureData sigdata;

        std::unique_ptr<SigningProvider> provider = GetSigningProvider(scriptPubKey);
        if (!provider) {
            // We don't know about this scriptpbuKey;
            return false;
        }

        if (!ProduceSignature(*provider, MutableTransactionSignatureCreator(&tx, nIn, amount, SIGHASH_ALL), scriptPubKey, sigdata)) {
            return false;
        }
        UpdateTransaction(tx, nIn, sigdata);
        nIn++;
    }
    return true;
}

bool CWallet::FundTransaction(CMutableTransaction& tx, CAmount& nFeeRet, int& nChangePosInOut, std::string& strFailReason, bool lockUnspents, const std::set<int>& setSubtractFeeFromOutputs, CCoinControl coinControl)
{
    std::vector<CRecipient> vecSend;

    // Turn the txout set into a CRecipient vector.
    for (size_t idx = 0; idx < tx.vout.size(); idx++) {
        const CTxOut& txOut = tx.vout[idx];

        // ELEMENTS:
        if (!txOut.nValue.IsExplicit() || !txOut.nAsset.IsExplicit()) {
            strFailReason = _("Pre-funded amounts must be non-blinded").translated;
            return false;
        }

        // Fee outputs should not be added to avoid overpayment of fees
        if (txOut.IsFee()) {
            continue;
        }

        CRecipient recipient = {txOut.scriptPubKey, txOut.nValue.GetAmount(), txOut.nAsset.GetAsset(), CPubKey(txOut.nNonce.vchCommitment), setSubtractFeeFromOutputs.count(idx) == 1};
        vecSend.push_back(recipient);
    }

    coinControl.fAllowOtherInputs = true;

    for (const CTxIn& txin : tx.vin) {
        coinControl.Select(txin.prevout);
    }

    // Acquire the locks to prevent races to the new locked unspents between the
    // CreateTransaction call and LockCoin calls (when lockUnspents is true).
    auto locked_chain = chain().lock();
    LOCK(cs_wallet);

    CTransactionRef tx_new;
    BlindDetails* blind_details = g_con_elementsmode ? new BlindDetails() : NULL;
    if (!CreateTransaction(*locked_chain, vecSend, tx_new, nFeeRet, nChangePosInOut, strFailReason, coinControl, false, blind_details)) {
        return false;
    }

    // Wipe outputs and output witness and re-add one by one
    tx.vout.clear();
    tx.witness.vtxoutwit.clear();
    for (unsigned int i = 0; i < tx_new->vout.size(); i++) {
        const CTxOut& out = tx_new->vout[i];
        tx.vout.push_back(out);
        if (tx_new->witness.vtxoutwit.size() > i) {
            // We want to re-add previously existing outwitnesses
            // even though we don't create any new ones
            const CTxOutWitness& outwit = tx_new->witness.vtxoutwit[i];
            tx.witness.vtxoutwit.push_back(outwit);
        }
    }

    // Add new txins while keeping original txin scriptSig/order.
    for (const CTxIn& txin : tx_new->vin) {
        if (!coinControl.IsSelected(txin.prevout)) {
            tx.vin.push_back(txin);

            if (lockUnspents) {
                LockCoin(txin.prevout);
            }
        }
    }

    return true;
}

static bool IsCurrentForAntiFeeSniping(interfaces::Chain& chain, interfaces::Chain::Lock& locked_chain)
{
    if (chain.isInitialBlockDownload()) {
        return false;
    }
    constexpr int64_t MAX_ANTI_FEE_SNIPING_TIP_AGE = 8 * 60 * 60; // in seconds
    if (locked_chain.getBlockTime(*locked_chain.getHeight()) < (GetTime() - MAX_ANTI_FEE_SNIPING_TIP_AGE)) {
        return false;
    }
    return true;
}

/**
 * Return a height-based locktime for new transactions (uses the height of the
 * current chain tip unless we are not synced with the current chain
 */
static uint32_t GetLocktimeForNewTransaction(interfaces::Chain& chain, interfaces::Chain::Lock& locked_chain)
{
    uint32_t const height = locked_chain.getHeight().get_value_or(-1);
    uint32_t locktime;
    // Discourage fee sniping.
    //
    // For a large miner the value of the transactions in the best block and
    // the mempool can exceed the cost of deliberately attempting to mine two
    // blocks to orphan the current best block. By setting nLockTime such that
    // only the next block can include the transaction, we discourage this
    // practice as the height restricted and limited blocksize gives miners
    // considering fee sniping fewer options for pulling off this attack.
    //
    // A simple way to think about this is from the wallet's point of view we
    // always want the blockchain to move forward. By setting nLockTime this
    // way we're basically making the statement that we only want this
    // transaction to appear in the next block; we don't want to potentially
    // encourage reorgs by allowing transactions to appear at lower heights
    // than the next block in forks of the best chain.
    //
    // Of course, the subsidy is high enough, and transaction volume low
    // enough, that fee sniping isn't a problem yet, but by implementing a fix
    // now we ensure code won't be written that makes assumptions about
    // nLockTime that preclude a fix later.
    if (IsCurrentForAntiFeeSniping(chain, locked_chain)) {
        locktime = height;

        // Secondly occasionally randomly pick a nLockTime even further back, so
        // that transactions that are delayed after signing for whatever reason,
        // e.g. high-latency mix networks and some CoinJoin implementations, have
        // better privacy.
        if (GetRandInt(10) == 0)
            locktime = std::max(0, (int)locktime - GetRandInt(100));
    } else {
        // If our chain is lagging behind, we can't discourage fee sniping nor help
        // the privacy of high-latency transactions. To avoid leaking a potentially
        // unique "nLockTime fingerprint", set nLockTime to a constant.
        locktime = 0;
    }
    assert(locktime <= height);
    assert(locktime < LOCKTIME_THRESHOLD);
    return locktime;
}

OutputType CWallet::TransactionChangeType(OutputType change_type, const std::vector<CRecipient>& vecSend)
{
    // If -changetype is specified, always use that change type.
    if (change_type != OutputType::CHANGE_AUTO) {
        return change_type;
    }

    // if m_default_address_type is legacy, use legacy address as change (even
    // if some of the outputs are P2WPKH or P2WSH).
    if (m_default_address_type == OutputType::LEGACY) {
        return OutputType::LEGACY;
    }

    // if any destination is P2WPKH or P2WSH, use P2WPKH for the change
    // output.
    for (const auto& recipient : vecSend) {
        // Check if any destination contains a witness program:
        int witnessversion = 0;
        std::vector<unsigned char> witnessprogram;
        if (recipient.scriptPubKey.IsWitnessProgram(witnessversion, witnessprogram)) {
            return OutputType::BECH32;
        }
    }

    // else use m_default_address_type for change
    return m_default_address_type;
}

// Reset all non-global blinding details.
void resetBlindDetails(BlindDetails* det) {
    det->i_amount_blinds.clear();
    det->i_asset_blinds.clear();
    det->i_assets.clear();
    det->i_amounts.clear();

    det->o_amounts.clear();
    det->o_pubkeys.clear();
    det->o_amount_blinds.clear();
    det->o_assets.clear();
    det->o_asset_blinds.clear();

    det->tx_unblinded_unsigned = CMutableTransaction();
    det->num_to_blind = 0;
    det->change_to_blind = 0;
    det->only_recipient_blind_index = -1;
    det->only_change_pos = -1;
}

bool fillBlindDetails(BlindDetails* det, CWallet* wallet, CMutableTransaction& txNew, std::vector<CInputCoin>& selected_coins, std::string& strFailReason) {
    int num_inputs_blinded = 0;

    // Fill in input blinding details
    for (const CInputCoin& coin : selected_coins) {
        det->i_amount_blinds.push_back(coin.bf_value);
        det->i_asset_blinds.push_back(coin.bf_asset);
        det->i_assets.push_back(coin.asset);
        det->i_amounts.push_back(coin.value);
        if (coin.txout.nValue.IsCommitment() || coin.txout.nAsset.IsCommitment()) {
            num_inputs_blinded++;
        }
    }
    // Fill in output blinding details
    for (size_t nOut = 0; nOut < txNew.vout.size(); nOut++) {
        //TODO(CA) consider removing all blind setting before BlindTransaction as they get cleared anyway
        det->o_amount_blinds.push_back(uint256());
        det->o_asset_blinds.push_back(uint256());
        det->o_assets.push_back(txNew.vout[nOut].nAsset.GetAsset());
        det->o_amounts.push_back(txNew.vout[nOut].nValue.GetAmount());
    }

    // There are a few edge-cases of blinding we need to take care of
    //
    // First, if there are blinded inputs but not outputs to blind
    // We need this to go through, even though no privacy is gained.
    if (num_inputs_blinded > 0 &&  det->num_to_blind == 0) {
        // We need to make sure to dupe an asset that is in input set
        //TODO Have blinding do some extremely minimal rangeproof
        CTxOut newTxOut(det->o_assets.back(), 0, CScript() << OP_RETURN);
        txNew.vout.push_back(newTxOut);
        det->o_pubkeys.push_back(wallet->GetBlindingPubKey(newTxOut.scriptPubKey));
        det->o_amount_blinds.push_back(uint256());
        det->o_asset_blinds.push_back(uint256());
        det->o_amounts.push_back(0);
        det->o_assets.push_back(det->o_assets.back());
        det->num_to_blind++;
        wallet->WalletLogPrintf("Adding OP_RETURN output to complete blinding since there are %d blinded inputs and no blinded outputs\n", num_inputs_blinded);

        // No blinded inputs, but 1 blinded output
    } else if (num_inputs_blinded == 0 && det->num_to_blind == 1) {
        if (det->change_to_blind == 1) {
            // Only 1 blinded change, unblind the change
            //TODO Split up change instead if possible
            if (det->ignore_blind_failure) {
                det->num_to_blind--;
                det->change_to_blind--;
                txNew.vout[det->only_change_pos].nNonce.SetNull();
                det->o_pubkeys[det->only_change_pos] = CPubKey();
                det->o_amount_blinds[det->only_change_pos] = uint256();
                det->o_asset_blinds[det->only_change_pos] = uint256();
                wallet->WalletLogPrintf("Unblinding change at index %d due to lack of inputs and other outputs being blinded.\n", det->only_change_pos);
            } else {
                strFailReason = _("Change output could not be blinded as there are no blinded inputs and no other blinded outputs.").translated;
                return false;
            }
        } else {
            // 1 blinded destination
            // TODO Attempt to get a blinded input, OR add unblinded coin to make blinded change
            assert(det->only_recipient_blind_index != -1);
            if (det->ignore_blind_failure) {
                det->num_to_blind--;
                txNew.vout[det->only_recipient_blind_index].nNonce.SetNull();
                det->o_pubkeys[det->only_recipient_blind_index] = CPubKey();
                det->o_amount_blinds[det->only_recipient_blind_index] = uint256();
                det->o_asset_blinds[det->only_recipient_blind_index] = uint256();
                wallet->WalletLogPrintf("Unblinding single blinded output at index %d due to lack of inputs and other outputs being blinded.\n", det->only_recipient_blind_index);
            } else {
                strFailReason = _("Transaction output could not be blinded as there are no blinded inputs and no other blinded outputs.").translated;
                return false;
            }
        }
    }
    // All other combinations should work.
    return true;
}

bool CWallet::CreateTransaction(interfaces::Chain::Lock& locked_chain, const std::vector<CRecipient>& vecSend, CTransactionRef& tx, CAmount& nFeeRet, int& nChangePosInOut, std::string& strFailReason, const CCoinControl& coin_control, bool sign, BlindDetails* blind_details, const IssuanceDetails* issuance_details) {
    if (blind_details || issuance_details) {
        assert(g_con_elementsmode);
    }

    CAmountMap mapValue;
    // Always assume that we are at least sending policyAsset.
    mapValue[::policyAsset] = 0;
    std::vector<std::unique_ptr<ReserveDestination>> reservedest;
    const OutputType change_type = TransactionChangeType(coin_control.m_change_type ? *coin_control.m_change_type : m_default_change_type, vecSend);
    reservedest.emplace_back(new ReserveDestination(this, change_type)); // policy asset
    int nChangePosRequest = nChangePosInOut;
    std::map<CAsset, int> vChangePosInOut;
    unsigned int nSubtractFeeFromAmount = 0;

    std::set<CAsset> assets_seen;
    for (const auto& recipient : vecSend)
    {
        // Pad change keys to cover total possible number of assets
        // One already exists(for policyAsset), so one for each destination
        if (assets_seen.insert(recipient.asset).second) {
            reservedest.emplace_back(new ReserveDestination(this, change_type));
        }

        // Skip over issuance outputs, no need to select those coins
        if (recipient.asset == CAsset(uint256S("1")) || recipient.asset == CAsset(uint256S("2"))) {
            continue;
        }

        if (g_con_elementsmode && recipient.asset.IsNull()) {
            strFailReason = _("No asset provided for recipient").translated;
            return false;
        }

        if (mapValue[recipient.asset] < 0 || recipient.nAmount < 0) {
            strFailReason = _("Transaction amounts must not be negative").translated;
            return false;
        }
        mapValue[recipient.asset] += recipient.nAmount;

        if (recipient.fSubtractFeeFromAmount)
            nSubtractFeeFromAmount++;
    }
    if (vecSend.empty())
    {
        strFailReason = _("Transaction must have at least one recipient").translated;
        return false;
    }

    CMutableTransaction txNew;

    txNew.nLockTime = GetLocktimeForNewTransaction(chain(), locked_chain);

    FeeCalculation feeCalc;
    CAmount nFeeNeeded;
    int nBytes;
    {
        std::set<CInputCoin> setCoins;

        // Preserve order of selected inputs for surjection proofs
        std::vector<CInputCoin> selected_coins;

        // A map that keeps track of the change script for each asset and also
        // the index of the reservedest used for that script (-1 if none).
        std::map<CAsset, std::pair<int, CScript>> mapScriptChange;

        auto locked_chain = chain().lock();
        LOCK(cs_wallet);
        {
            std::vector<COutput> vAvailableCoins;
            AvailableCoins(*locked_chain, vAvailableCoins, true, &coin_control, 1, MAX_MONEY, MAX_MONEY, 0);
            CoinSelectionParams coin_selection_params; // Parameters for coin selection, init with dummy

            mapScriptChange.clear();
            if (coin_control.destChange.size() > 0) {
                for (const auto& dest : coin_control.destChange) {
                    // No need to test we cover all assets.  We produce error for that later.
                    mapScriptChange[dest.first] = std::pair<int, CScript>(-1, GetScriptForDestination(dest.second));
                }
            } else { // no coin control: send change to newly generated address
                // Note: We use a new key here to keep it from being obvious which side is the change.
                //  The drawback is that by not reusing a previous key, the change may be lost if a
                //  backup is restored, if the backup doesn't have the new private key for the change.
                //  If we reused the old key, it would be possible to add code to look for and
                //  rediscover unknown transactions that were written with keys of ours to recover
                //  post-backup change.

                // Reserve a new key pair from key pool
                if (!CanGetAddresses(true)) {
                    strFailReason = _("Can't generate a change-address key. No keys in the internal keypool and can't generate any keys.").translated;
                    return false;
                }

                // One change script per output asset.
                size_t index = 0;
                for (const auto& value : mapValue) {
                    CTxDestination dest;
                    if (index >= reservedest.size() || !reservedest[index]->GetReservedDestination(dest, true)) {
                        strFailReason = _("Keypool ran out, please call keypoolrefill first").translated;
                        return false;
                    }

                    mapScriptChange[value.first] = std::pair<int, CScript>(index, GetScriptForDestination(dest));
                    ++index;
                }

                // Also make sure we have change scripts for the pre-selected inputs.
                std::vector<COutPoint> vPresetInputs;
                coin_control.ListSelected(vPresetInputs);
                for (const COutPoint& presetInput : vPresetInputs) {
                    CAsset asset;
                    std::map<uint256, CWalletTx>::const_iterator it = mapWallet.find(presetInput.hash);
                    CTxOut txout;
                    if (it != mapWallet.end()) {
                         asset = it->second.GetOutputAsset(presetInput.n);
                    } else if (coin_control.GetExternalOutput(presetInput, txout)) {
                        asset = txout.nAsset.GetAsset();
                    } else {
                        // Ignore this here, will fail more gracefully later.
                        continue;
                    }

                    if (mapScriptChange.find(asset) != mapScriptChange.end()) {
                        // This asset already has a change script.
                        continue;
                    }

                    CTxDestination dest;
                    if (index >= reservedest.size() || !reservedest[index]->GetReservedDestination(dest, true)) {
                        strFailReason = _("Keypool ran out, please call keypoolrefill first").translated;
                        return false;
                    }

                    mapScriptChange[asset] = std::pair<int, CScript>(index, GetScriptForDestination(dest));
                    ++index;
                }
            }
            assert(mapScriptChange.size() > 0);

            CTxOut change_prototype_txout(mapScriptChange.begin()->first, 0, mapScriptChange.begin()->second.second);
            // TODO CA: Set this for each change output
            coin_selection_params.change_output_size = GetSerializeSize(change_prototype_txout);
            if (g_con_elementsmode) {
                // Assume blinded output for coin selection purposes. Over-paying is ok!
                change_prototype_txout.nAsset.vchCommitment.resize(33);
                change_prototype_txout.nValue.vchCommitment.resize(33);
                change_prototype_txout.nNonce.vchCommitment.resize(33);
                coin_selection_params.change_output_size = GetSerializeSize(change_prototype_txout);
                coin_selection_params.change_output_size += (MAX_RANGEPROOF_SIZE + DEFAULT_SURJECTIONPROOF_SIZE + WITNESS_SCALE_FACTOR - 1)/WITNESS_SCALE_FACTOR;
            }

            CFeeRate discard_rate = GetDiscardRate(*this);

            // Get the fee rate to use effective values in coin selection
            CFeeRate nFeeRateNeeded = GetMinimumFeeRate(*this, coin_control, &feeCalc);

            // ELEMENTS:
            // Start with tiny non-zero fee for issuance entropy and loop until there is enough fee
            nFeeRet = 1;
            bool pick_new_inputs = true;
            CAmountMap mapValueIn;

            // BnB selector is the only selector used when this is true.
            // That should only happen on the first pass through the loop.
            coin_selection_params.use_bnb = true;
            coin_selection_params.m_subtract_fee_outputs = nSubtractFeeFromAmount != 0; // If we are doing subtract fee from recipient, don't use effective values
            //ELEMENTS: stopgap solution to https://github.com/bitcoin/bitcoin/issues/20347
            bool one_more_try_20347 = false;
            // Start with no fee and loop until there is enough fee
            while (true)
            {
                if (blind_details) {
                    // Clear out previous blinding/data info as needed
                    resetBlindDetails(blind_details);
                }

                // We need to output the position of the policyAsset change output.
                // So we keep track of the change position of all assets
                // individually and set the export variable in the end.
                vChangePosInOut.clear();
                if (nChangePosRequest >= 0) {
                    vChangePosInOut[::policyAsset] = nChangePosRequest;
                }

                txNew.vin.clear();
                txNew.vout.clear();
                txNew.witness.SetNull();
                bool fFirst = true;

                CAmountMap mapValueToSelect = mapValue;
                if (nSubtractFeeFromAmount == 0)
                    mapValueToSelect[::policyAsset] += nFeeRet;

                // vouts to the payees
                if (!coin_selection_params.m_subtract_fee_outputs) {
                    coin_selection_params.tx_noinputs_size = 11; // Static vsize overhead + outputs vsize. 4 nVersion, 4 nLocktime, 1 input count, 1 output count, 1 witness overhead (dummy, flag, stack size)
                }
                for (const auto& recipient : vecSend)
                {
                    CTxOut txout(recipient.asset, recipient.nAmount, recipient.scriptPubKey);
                    txout.nNonce.vchCommitment = std::vector<unsigned char>(recipient.confidentiality_key.begin(), recipient.confidentiality_key.end());

                    if (recipient.fSubtractFeeFromAmount)
                    {
                        if (recipient.asset != policyAsset) {
                            strFailReason = strprintf("Wallet does not support more than one type of fee at a time, therefore can not subtract fee from address amount, which is of a different asset id. fee asset: %s recipient asset: %s", policyAsset.GetHex(), recipient.asset.GetHex());
                            return false;
                        }

                        assert(nSubtractFeeFromAmount != 0);
                        txout.nValue = txout.nValue.GetAmount() - nFeeRet / nSubtractFeeFromAmount; // Subtract fee equally from each selected recipient

                        if (fFirst) // first receiver pays the remainder not divisible by output count
                        {
                            fFirst = false;
                            txout.nValue = txout.nValue.GetAmount() - nFeeRet % nSubtractFeeFromAmount;
                        }
                    }
                    // Include the fee cost for outputs. Note this is only used for BnB right now
                    if (!coin_selection_params.m_subtract_fee_outputs) {
                        coin_selection_params.tx_noinputs_size += ::GetSerializeSize(txout, PROTOCOL_VERSION);
                    }

                    // ELEMENTS: Core's logic isn't great here. We should be computing
                    // cost of making output + future spend. We're not as concerned
                    // about dust anyways, so let's focus upstream.
                    if (recipient.asset == policyAsset && IsDust(txout, chain().relayDustFee()))
                    {
                        if (recipient.fSubtractFeeFromAmount && nFeeRet > 0)
                        {
                            if (txout.nValue.GetAmount() < 0)
                                strFailReason = _("The transaction amount is too small to pay the fee").translated;
                            else
                                strFailReason = _("The transaction amount is too small to send after the fee has been deducted").translated;
                        }
                        else
                            strFailReason = _("Transaction amount too small").translated;
                        return false;
                    }
                    txNew.vout.push_back(txout);
                    if (blind_details) {
                        blind_details->o_pubkeys.push_back(recipient.confidentiality_key);
                        if (blind_details->o_pubkeys.back().IsFullyValid()) {
                            blind_details->num_to_blind++;
                            blind_details->only_recipient_blind_index = txNew.vout.size()-1;
                        }
                    }
                }

                // Choose coins to use
                bool bnb_used = false;
                if (pick_new_inputs) {
                    mapValueIn.clear();
                    setCoins.clear();
                    int change_spend_size = CalculateMaximumSignedInputSize(change_prototype_txout, this);
                    // If the wallet doesn't know how to sign change output, assume p2sh-p2wpkh
                    // as lower-bound to allow BnB to do it's thing
                    if (change_spend_size == -1) {
                        coin_selection_params.change_spend_size = DUMMY_NESTED_P2WPKH_INPUT_SIZE;
                    } else {
                        coin_selection_params.change_spend_size = (size_t)change_spend_size;
                    }
                    coin_selection_params.effective_fee = nFeeRateNeeded;
                    if (!SelectCoins(vAvailableCoins, mapValueToSelect, setCoins, mapValueIn, coin_control, coin_selection_params, bnb_used))
                    {
                        // If BnB was used, it was the first pass. No longer the first pass and continue loop with knapsack.
                        if (bnb_used) {
                            coin_selection_params.use_bnb = false;
                            continue;
                        }
                        else {
                            strFailReason = _("Insufficient funds").translated;
                            return false;
                        }
                    }
                } else {
                    bnb_used = false;
                }

                const CAmountMap mapChange = mapValueIn - mapValueToSelect;

                for(const auto& assetChange : mapChange) {
                    if (assetChange.second == 0) {
                        vChangePosInOut.erase(assetChange.first);
                        continue;
                    }

                    // Fill a vout to ourself
                    const std::map<CAsset, std::pair<int, CScript>>::const_iterator itScript = mapScriptChange.find(assetChange.first);
                    if (itScript == mapScriptChange.end()) {
                        strFailReason = strprintf("No change destination provided for asset %s", assetChange.first.GetHex());
                        return false;
                    }

                    CTxOut newTxOut(assetChange.first, assetChange.second, itScript->second.second);

                    // Never create dust outputs; if we would, just
                    // add the dust to the fee.
                    // The nChange when BnB is used is always going to go to fees.
                    if (assetChange.first == policyAsset && (IsDust(newTxOut, discard_rate) || bnb_used))
                    {
                        vChangePosInOut.erase(assetChange.first);
                        nFeeRet += assetChange.second;
                    }
                    else
                    {
                        std::map<CAsset, int>::const_iterator itPos = vChangePosInOut.find(assetChange.first);
                        if (itPos == vChangePosInOut.end())
                        {
                            // Insert change txn at random position:
                            int newPos = GetRandInt(txNew.vout.size()+1);

                            // Update existing entries in vChangePos that have been moved.
                            for (std::map<CAsset, int>::iterator it = vChangePosInOut.begin(); it != vChangePosInOut.end(); ++it) {
                                if (it->second >= newPos) {
                                    it->second++;
                                }
                            }

                            vChangePosInOut[assetChange.first] = newPos;
                        }
                        else if ((unsigned int)itPos->second > txNew.vout.size())
                        {
                            strFailReason = _("Change index out of range").translated;
                            return false;
                        }

                        std::vector<CTxOut>::iterator position = txNew.vout.begin()+vChangePosInOut[assetChange.first];
                        if (blind_details) {
                            CPubKey blind_pub = GetBlindingPubKey(itScript->second.second);
                            blind_details->o_pubkeys.insert(blind_details->o_pubkeys.begin() + vChangePosInOut[assetChange.first], blind_pub);
                            assert(blind_pub.IsFullyValid());
                            blind_details->num_to_blind++;
                            blind_details->change_to_blind++;
                            blind_details->only_change_pos = vChangePosInOut[assetChange.first];
                            // Place the blinding pubkey here in case of fundraw calls
                            newTxOut.nNonce.vchCommitment = std::vector<unsigned char>(blind_pub.begin(), blind_pub.end());
                        }
                        txNew.vout.insert(position, newTxOut);
                    }
                }
                // Set the correct nChangePosInOut for output.  Should be policyAsset's position.
                std::map<CAsset, int>::const_iterator itPos = vChangePosInOut.find(::policyAsset);
                if (itPos != vChangePosInOut.end()) {
                    nChangePosInOut = itPos->second;
                } else {
                    // no policy change inserted; others assets may have been
                    nChangePosInOut = -1;
                }

                // Add fee output.
                if (g_con_elementsmode) {
                    CTxOut fee(::policyAsset, nFeeRet, CScript());
                    assert(fee.IsFee());
                    txNew.vout.push_back(fee);
                    if (blind_details) {
                        blind_details->o_pubkeys.push_back(CPubKey());
                    }
                }

                // Set token input if reissuing
                int reissuance_index = -1;
                uint256 token_blinding;

                // Elements: Shuffle here to preserve random ordering for surjection proofs
                selected_coins = std::vector<CInputCoin>(setCoins.begin(), setCoins.end());
                Shuffle(selected_coins.begin(), selected_coins.end(), FastRandomContext());

                // Dummy fill vin for maximum size estimation
                //
                for (const CInputCoin& coin : selected_coins) {
                    txNew.vin.push_back(CTxIn(coin.outpoint, CScript()));

                    if (issuance_details && coin.asset == issuance_details->reissuance_token) {
                        reissuance_index = txNew.vin.size() - 1;
                        token_blinding = coin.bf_asset;
                    }
                }

                std::vector<CKey> issuance_asset_keys;
                std::vector<CKey> issuance_token_keys;
                if (issuance_details) {
                    // Fill in issuances now that inputs are set
                    assert(txNew.vin.size() > 0);
                    int asset_index = -1;
                    int token_index = -1;
                    for (unsigned int i = 0; i < txNew.vout.size(); i++) {
                        if (txNew.vout[i].nAsset.IsExplicit() && txNew.vout[i].nAsset.GetAsset()  == CAsset(uint256S("1"))) {
                            asset_index = i;
                        } else if (txNew.vout[i].nAsset.IsExplicit() && txNew.vout[i].nAsset.GetAsset() == CAsset(uint256S("2"))) {
                            token_index = i;
                        }
                    }
                    // Initial issuance request
                    if (issuance_details->reissuance_asset.IsNull() && issuance_details->reissuance_token.IsNull() && (asset_index != -1 || token_index != -1)) {
                        uint256 entropy;
                        CAsset asset;
                        CAsset token;
                        //TODO take optional contract hash
                        // Initial issuance always uses vin[0]
                        GenerateAssetEntropy(entropy, txNew.vin[0].prevout, uint256());
                        CalculateAsset(asset, entropy);
                        CalculateReissuanceToken(token, entropy, issuance_details->blind_issuance);
                        CScript blindingScript(CScript() << OP_RETURN << std::vector<unsigned char>(txNew.vin[0].prevout.hash.begin(), txNew.vin[0].prevout.hash.end()) << txNew.vin[0].prevout.n);
                        // We're making asset outputs, fill out asset type and issuance input
                        if (asset_index != -1) {
                            txNew.vin[0].assetIssuance.nAmount = txNew.vout[asset_index].nValue;

                            txNew.vout[asset_index].nAsset = asset;
                            if (issuance_details->blind_issuance && blind_details) {
                                issuance_asset_keys.push_back(GetBlindingKey(&blindingScript));
                                blind_details->num_to_blind++;
                            }
                        }
                        // We're making reissuance token outputs
                        if (token_index != -1) {
                            txNew.vin[0].assetIssuance.nInflationKeys = txNew.vout[token_index].nValue;
                            txNew.vout[token_index].nAsset = token;
                            if (issuance_details->blind_issuance && blind_details) {
                                issuance_token_keys.push_back(GetBlindingKey(&blindingScript));
                                blind_details->num_to_blind++;

                                // If we're blinding a token issuance and no assets, we must make
                                // the asset issuance a blinded commitment to 0
                                if (asset_index == -1) {
                                    txNew.vin[0].assetIssuance.nAmount = 0;
                                    issuance_asset_keys.push_back(GetBlindingKey(&blindingScript));
                                    blind_details->num_to_blind++;
                                }
                            }
                        }
                    // Asset being reissued with explicitly named asset/token
                    } else if (asset_index != -1) {
                        assert(reissuance_index != -1);
                        // Fill in output with issuance
                        txNew.vout[asset_index].nAsset = issuance_details->reissuance_asset;

                        // Fill in issuance
                        // Blinding revealing underlying asset
                        txNew.vin[reissuance_index].assetIssuance.assetBlindingNonce = token_blinding;
                        txNew.vin[reissuance_index].assetIssuance.assetEntropy = issuance_details->entropy;
                        txNew.vin[reissuance_index].assetIssuance.nAmount = txNew.vout[asset_index].nValue;

                        // If blinded token derivation, blind the issuance
                        CAsset temp_token;
                        CalculateReissuanceToken(temp_token, issuance_details->entropy, true);
                        if (temp_token == issuance_details->reissuance_token && blind_details) {
                            CScript blindingScript(CScript() << OP_RETURN << std::vector<unsigned char>(txNew.vin[reissuance_index].prevout.hash.begin(), txNew.vin[reissuance_index].prevout.hash.end()) << txNew.vin[reissuance_index].prevout.n);
                            issuance_asset_keys.resize(reissuance_index);
                            issuance_asset_keys.push_back(GetBlindingKey(&blindingScript));
                            blind_details->num_to_blind++;
                        }
                    }
                }

                if (blind_details) {
                    if (!fillBlindDetails(blind_details, this, txNew, selected_coins, strFailReason)) {
                        return false;
                    }

                    // Keep a backup of transaction in case re-blinding necessary
                    blind_details->tx_unblinded_unsigned = txNew;
                    int ret = BlindTransaction(blind_details->i_amount_blinds, blind_details->i_asset_blinds, blind_details->i_assets, blind_details->i_amounts, blind_details->o_amount_blinds, blind_details->o_asset_blinds,  blind_details->o_pubkeys, issuance_asset_keys, issuance_token_keys, txNew);
                    assert(ret != -1);
                    if (ret != blind_details->num_to_blind) {
                        strFailReason = _("Unable to blind the transaction properly. This should not happen.").translated;
                        return false;
                    }
                }

                nBytes = CalculateMaximumSignedTxSize(CTransaction(txNew), this, &coin_control);
                if (nBytes < 0) {
                    strFailReason = _("Missing solving data for estimating transaction size").translated;
                    return false;
                }

                // Remove blinding if we're not actually signing
                if (blind_details && !sign) {
                    txNew = blind_details->tx_unblinded_unsigned;
                }

                nFeeNeeded = GetMinimumFee(*this, nBytes, coin_control, &feeCalc);
                if (feeCalc.reason == FeeReason::FALLBACK && !m_allow_fallback_fee) {
                    // eventually allow a fallback fee
                    strFailReason = _("Fee estimation failed. Fallbackfee is disabled. Wait a few blocks or enable -fallbackfee.").translated;
                    return false;
                }

                if (nFeeRet >= nFeeNeeded) {
                    // Reduce fee to only the needed amount if possible. This
                    // prevents potential overpayment in fees if the coins
                    // selected to meet nFeeNeeded result in a transaction that
                    // requires less fee than the prior iteration.

                    // If we have no change and a big enough excess fee, then
                    // try to construct transaction again only without picking
                    // new inputs. We now know we only need the smaller fee
                    // (because of reduced tx size) and so we should add a
                    // change output. Only try this once.
                    if (nChangePosInOut == -1 && nSubtractFeeFromAmount == 0 && pick_new_inputs) {
                        unsigned int tx_size_with_change = nBytes + coin_selection_params.change_output_size + 2; // Add 2 as a buffer in case increasing # of outputs changes compact size
                        CAmount fee_needed_with_change = GetMinimumFee(*this, tx_size_with_change, coin_control, nullptr);
                        CAmount minimum_value_for_change = GetDustThreshold(change_prototype_txout, discard_rate);
                        if (nFeeRet >= fee_needed_with_change + minimum_value_for_change) {
                            pick_new_inputs = false;
                            nFeeRet = fee_needed_with_change;
                            continue;
                        }
                    }

                    // If we have change output already, just increase it
                    if (nFeeRet > nFeeNeeded && nChangePosInOut != -1 && nSubtractFeeFromAmount == 0) {
                        CAmount extraFeePaid = nFeeRet - nFeeNeeded;

                        // If blinding we need to edit the unblinded tx and re-blind. Otherwise just edit the tx.
                        if (blind_details) {
                            txNew = blind_details->tx_unblinded_unsigned;
                            std::vector<CTxOut>::iterator change_position = txNew.vout.begin() + nChangePosInOut;
                            change_position->nValue = change_position->nValue.GetAmount() + extraFeePaid;
                            blind_details->o_amounts[nChangePosInOut] = change_position->nValue.GetAmount();

                            nFeeRet -= extraFeePaid;
                            txNew.vout.back().nValue = nFeeRet; // update fee output
                            blind_details->o_amounts.back() = nFeeRet;

                            // Wipe output blinding factors and start over
                            blind_details->o_amount_blinds.clear();

                            blind_details->o_asset_blinds.clear();

                            // Re-blind tx after editing and change.
                            blind_details->tx_unblinded_unsigned = txNew;
                            int ret = BlindTransaction(blind_details->i_amount_blinds, blind_details->i_asset_blinds, blind_details->i_assets, blind_details->i_amounts, blind_details->o_amount_blinds, blind_details->o_asset_blinds,  blind_details->o_pubkeys, issuance_asset_keys, issuance_token_keys, txNew);
                            assert(ret != -1);
                            if (ret != blind_details->num_to_blind) {
                                strFailReason = _("Unable to blind the transaction properly. This should not happen.").translated;
                                return false;
                            }
                        } else {
                            std::vector<CTxOut>::iterator change_position = txNew.vout.begin() + nChangePosInOut;
                            change_position->nValue = change_position->nValue.GetAmount() + extraFeePaid;
                            nFeeRet -= extraFeePaid;
                            if (g_con_elementsmode) {
                                txNew.vout.back().nValue = nFeeRet; // update fee output
                            }
                        }
                    }
                    break; // Done, enough fee included.
                }
                else if (!pick_new_inputs && !one_more_try_20347) {
                    // This shouldn't happen, we should have had enough excess
                    // fee to pay for the new output and still meet nFeeNeeded
                    // Or we should have just subtracted fee from recipients and
                    // nFeeNeeded should not have changed
                    strFailReason = _("Transaction fee and change calculation failed").translated;
                    return false;
                }

                // Try to reduce change to include necessary fee
                if (nChangePosInOut != -1 && nSubtractFeeFromAmount == 0) {
                    CAmount additionalFeeNeeded = nFeeNeeded - nFeeRet;

                    // If blinding we need to edit the unblinded tx and re-blind. Otherwise just edit the tx.
                    if (blind_details) {
                        txNew = blind_details->tx_unblinded_unsigned;
                        std::vector<CTxOut>::iterator change_position = txNew.vout.begin() + nChangePosInOut;
                        // Only reduce change if remaining amount is still a large enough output.
                        if (change_position->nValue.GetAmount() >= MIN_FINAL_CHANGE + additionalFeeNeeded) {
                            change_position->nValue = change_position->nValue.GetAmount() - additionalFeeNeeded;
                            blind_details->o_amounts[nChangePosInOut] = change_position->nValue.GetAmount();

                            nFeeRet += additionalFeeNeeded;
                            txNew.vout.back().nValue = nFeeRet; // update fee output
                            blind_details->o_amounts.back() = nFeeRet; // update change details
                            // Wipe output blinding factors and start over
                            blind_details->o_amount_blinds.clear();

                            blind_details->o_asset_blinds.clear();

                            // Re-blind tx after editing and change.
                            blind_details->tx_unblinded_unsigned = txNew;
                            int ret = BlindTransaction(blind_details->i_amount_blinds, blind_details->i_asset_blinds, blind_details->i_assets, blind_details->i_amounts, blind_details->o_amount_blinds, blind_details->o_asset_blinds,  blind_details->o_pubkeys, issuance_asset_keys, issuance_token_keys, txNew);
                            assert(ret != -1);
                            if (ret != blind_details->num_to_blind) {
                                strFailReason = _("Unable to blind the transaction properly. This should not happen.").translated;
                                return false;
                            }
                            break; // Done, able to increase fee from change
                        }
                    } else {
                        std::vector<CTxOut>::iterator change_position = txNew.vout.begin() + nChangePosInOut;
                        // Only reduce change if remaining amount is still a large enough output.
                        if (change_position->nValue.GetAmount() >= MIN_FINAL_CHANGE + additionalFeeNeeded) {
                            change_position->nValue = change_position->nValue.GetAmount() - additionalFeeNeeded;
                            nFeeRet += additionalFeeNeeded;
                            if (g_con_elementsmode) {
                                txNew.vout.back().nValue = nFeeRet; // update fee output
                            }
                            break; // Done, able to increase fee from change
                        }
                    }
                }

                // If subtracting fee from recipients, we now know what fee we
                // need to subtract, we have no reason to reselect inputs
                // In case we used branch-and-bound, this could result in our transaction
                // since increasing since we force-elided change on this iteration for bnb.
                // In this case we turn on `one_more_try` so that `!pick_new_inputs` doesn't
                // cause the loop to fail. This is a stopgap. See Core #20347.
                one_more_try_20347 = false;
                if (nSubtractFeeFromAmount > 0) {
                    pick_new_inputs = false;
                    one_more_try_20347 = bnb_used;
                }

                // Include more fee and try again.
                nFeeRet = nFeeNeeded;
                coin_selection_params.use_bnb = false;
                continue;
            }
        }

        // Release any change keys that we didn't use.
        for (const auto& it : mapScriptChange) {
            int index = it.second.first;
            if (index < 0) {
                continue;
            }

            if (vChangePosInOut.find(it.first) == vChangePosInOut.end()) {
                reservedest[index]->ReturnDestination();
            }
        }

        // Note how the sequence number is set to non-maxint so that
        // the nLockTime set above actually works.
        //
        // BIP125 defines opt-in RBF as any nSequence < maxint-1, so
        // we use the highest possible value in that range (maxint-2)
        // to avoid conflicting with other possible uses of nSequence,
        // and in the spirit of "smallest possible change from prior
        // behavior."
        const uint32_t nSequence = coin_control.m_signal_bip125_rbf.get_value_or(m_signal_rbf) ? MAX_BIP125_RBF_SEQUENCE : (CTxIn::SEQUENCE_FINAL - 1);
        for (auto& input : txNew.vin) {
            // Remove sigs and then set sequence
            input.scriptSig = CScript();
            input.nSequence = nSequence;
        }
        // Also remove witness data for scripts
        for (auto& inwit : txNew.witness.vtxinwit) {
            inwit.scriptWitness.SetNull();
        }

        // Do the same things for unblinded version of tx when applicable
        if (blind_details) {
            for (auto& input : blind_details->tx_unblinded_unsigned.vin) {
                input.nSequence = nSequence;
            }
        }

        // Print blinded transaction info before we possibly blow it away when !sign.
        if (blind_details) {
            std::string summary = "CreateTransaction created blinded transaction:\nIN: ";
            for (unsigned int i = 0; i < selected_coins.size(); ++i) {
                if (i > 0) {
                    summary += "    ";
                }
                summary += strprintf("#%d: %s [%s] (%s [%s])\n", i,
                    selected_coins[i].value,
                    selected_coins[i].txout.nValue.IsExplicit() ? "explicit" : "blinded",
                    selected_coins[i].asset.GetHex(),
                    selected_coins[i].txout.nAsset.IsExplicit() ? "explicit" : "blinded"
                );
            }
            summary += "OUT: ";
            for (unsigned int i = 0; i < txNew.vout.size(); ++i) {
                if (i > 0) {
                    summary += "     ";
                }
                CTxOut unblinded = blind_details->tx_unblinded_unsigned.vout[i];
                summary += strprintf("#%d: %s%s [%s] (%s [%s])\n", i,
                    txNew.vout[i].IsFee() ? "[fee] " : "",
                    unblinded.nValue.GetAmount(),
                    txNew.vout[i].nValue.IsExplicit() ? "explicit" : "blinded",
                    unblinded.nAsset.GetAsset().GetHex(),
                    txNew.vout[i].nAsset.IsExplicit() ? "explicit" : "blinded"
                );
            }
            WalletLogPrintf(summary+"\n");
        }

        if (sign)
        {
            int nIn = 0;
            for (const auto& coin : selected_coins)
            {
                const CScript& scriptPubKey = coin.txout.scriptPubKey;
                SignatureData sigdata;

                std::unique_ptr<SigningProvider> provider = GetSigningProvider(scriptPubKey);
                if (!provider || !ProduceSignature(*provider, MutableTransactionSignatureCreator(&txNew, nIn, coin.txout.nValue, SIGHASH_ALL), scriptPubKey, sigdata))
                {
                    strFailReason = _("Signing transaction failed").translated;
                    return false;
                } else {
                    UpdateTransaction(txNew, nIn, sigdata);
                }

                nIn++;
            }
        } else if (blind_details) {
            // "sign" also means blind for the purposes of making a complete tx
            // or just funding one properly
            txNew = blind_details->tx_unblinded_unsigned;
        }

        // Normalize the witness in case it is not serialized before mempool
        if (!txNew.HasWitness()) {
            txNew.witness.SetNull();
        }

        // Return the constructed transaction data.
        tx = MakeTransactionRef(std::move(txNew));

        // Limit size
        if (GetTransactionWeight(*tx) > MAX_STANDARD_TX_WEIGHT)
        {
            strFailReason = _("Transaction too large").translated;
            return false;
        }
    }

    if (nFeeRet > m_default_max_tx_fee) {
        strFailReason = TransactionErrorString(TransactionError::MAX_FEE_EXCEEDED);
        return false;
    }

    if (gArgs.GetBoolArg("-walletrejectlongchains", DEFAULT_WALLET_REJECT_LONG_CHAINS)) {
        // Lastly, ensure this tx will pass the mempool's chain limits
        if (!chain().checkChainLimits(tx)) {
            strFailReason = _("Transaction has too long of a mempool chain").translated;
            return false;
        }
    }

    // Before we return success, we assume any change key will be used to prevent
    // accidental re-use.
    for (auto& reservedest_ : reservedest) {
        reservedest_->KeepDestination();
    }

    WalletLogPrintf("Fee Calculation: Fee:%d Bytes:%u Needed:%d Tgt:%d (requested %d) Reason:\"%s\" Decay %.5f: Estimation: (%g - %g) %.2f%% %.1f/(%.1f %d mem %.1f out) Fail: (%g - %g) %.2f%% %.1f/(%.1f %d mem %.1f out)\n",
              nFeeRet, nBytes, nFeeNeeded, feeCalc.returnedTarget, feeCalc.desiredTarget, StringForFeeReason(feeCalc.reason), feeCalc.est.decay,
              feeCalc.est.pass.start, feeCalc.est.pass.end,
              100 * feeCalc.est.pass.withinTarget / (feeCalc.est.pass.totalConfirmed + feeCalc.est.pass.inMempool + feeCalc.est.pass.leftMempool),
              feeCalc.est.pass.withinTarget, feeCalc.est.pass.totalConfirmed, feeCalc.est.pass.inMempool, feeCalc.est.pass.leftMempool,
              feeCalc.est.fail.start, feeCalc.est.fail.end,
              100 * feeCalc.est.fail.withinTarget / (feeCalc.est.fail.totalConfirmed + feeCalc.est.fail.inMempool + feeCalc.est.fail.leftMempool),
              feeCalc.est.fail.withinTarget, feeCalc.est.fail.totalConfirmed, feeCalc.est.fail.inMempool, feeCalc.est.fail.leftMempool);
    return true;
}

void CWallet::CommitTransaction(CTransactionRef tx, mapValue_t mapValue, std::vector<std::pair<std::string, std::string>> orderForm, const BlindDetails* blind_details)
{
    auto locked_chain = chain().lock();
    LOCK(cs_wallet);

    CWalletTx wtxNew(this, std::move(tx));
    wtxNew.mapValue = std::move(mapValue);
    wtxNew.vOrderForm = std::move(orderForm);
    wtxNew.fTimeReceivedIsTxTime = true;
    wtxNew.fFromMe = true;

    // Write down blinding information
    if (blind_details) {
        assert(blind_details->o_amounts.size() == wtxNew.tx->vout.size());
        assert(blind_details->o_asset_blinds.size() == wtxNew.tx->vout.size());
        assert(blind_details->o_amount_blinds.size() == wtxNew.tx->vout.size());
        for (unsigned int i = 0; i < blind_details->o_amounts.size(); i++) {
            wtxNew.SetBlindingData(i, blind_details->o_pubkeys[i], blind_details->o_amounts[i], blind_details->o_amount_blinds[i], blind_details->o_assets[i], blind_details->o_asset_blinds[i]);
        }
    }

    WalletLogPrintf("CommitTransaction:\n%s", wtxNew.tx->ToString()); /* Continued */

    // Add tx to wallet, because if it has change it's also ours,
    // otherwise just for transaction history.
    AddToWallet(wtxNew);

    // Notify that old coins are spent
    for (const CTxIn& txin : wtxNew.tx->vin)
    {
        // Pegins are not in our UTXO set.
        if (txin.m_is_pegin)
            continue;

        CWalletTx &coin = mapWallet.at(txin.prevout.hash);
        coin.BindWallet(this);
        NotifyTransactionChanged(this, coin.GetHash(), CT_UPDATED);
    }

    // Get the inserted-CWalletTx from mapWallet so that the
    // fInMempool flag is cached properly
    CWalletTx& wtx = mapWallet.at(wtxNew.GetHash());

    if (!fBroadcastTransactions) {
        // Don't submit tx to the mempool
        return;
    }

    std::string err_string;
    if (!wtx.SubmitMemoryPoolAndRelay(err_string, true)) {
        WalletLogPrintf("CommitTransaction(): Transaction cannot be broadcast immediately, %s\n", err_string);
        // TODO: if we expect the failure to be long term or permanent, instead delete wtx from the wallet and return failure.
    }
}

DBErrors CWallet::LoadWallet(bool& fFirstRunRet)
{
    // Even if we don't use this lock in this function, we want to preserve
    // lock order in LoadToWallet if query of chain state is needed to know
    // tx status. If lock can't be taken (e.g bitcoin-wallet), tx confirmation
    // status may be not reliable.
    auto locked_chain = LockChain();
    LOCK(cs_wallet);

    fFirstRunRet = false;
    DBErrors nLoadWalletRet = WalletBatch(*database,"cr+").LoadWallet(this);
    if (nLoadWalletRet == DBErrors::NEED_REWRITE)
    {
        if (database->Rewrite("\x04pool"))
        {
            for (const auto& spk_man_pair : m_spk_managers) {
                spk_man_pair.second->RewriteDB();
            }
        }
    }

    // This wallet is in its first run if there are no ScriptPubKeyMans and it isn't blank or no privkeys
    fFirstRunRet = m_spk_managers.empty() && !IsWalletFlagSet(WALLET_FLAG_DISABLE_PRIVATE_KEYS) && !IsWalletFlagSet(WALLET_FLAG_BLANK_WALLET);
    if (fFirstRunRet) {
        assert(m_external_spk_managers.empty());
        assert(m_internal_spk_managers.empty());
    }

    if (nLoadWalletRet != DBErrors::LOAD_OK)
        return nLoadWalletRet;

    return DBErrors::LOAD_OK;
}

DBErrors CWallet::ZapSelectTx(std::vector<uint256>& vHashIn, std::vector<uint256>& vHashOut)
{
    AssertLockHeld(cs_wallet);
    DBErrors nZapSelectTxRet = WalletBatch(*database, "cr+").ZapSelectTx(vHashIn, vHashOut);
    for (uint256 hash : vHashOut) {
        const auto& it = mapWallet.find(hash);
        wtxOrdered.erase(it->second.m_it_wtxOrdered);
        mapWallet.erase(it);
        NotifyTransactionChanged(this, hash, CT_DELETED);
    }

    if (nZapSelectTxRet == DBErrors::NEED_REWRITE)
    {
        if (database->Rewrite("\x04pool"))
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

DBErrors CWallet::ZapWalletTx(std::vector<CWalletTx>& vWtx)
{
    DBErrors nZapWalletTxRet = WalletBatch(*database,"cr+").ZapWalletTx(vWtx);
    if (nZapWalletTxRet == DBErrors::NEED_REWRITE)
    {
        if (database->Rewrite("\x04pool"))
        {
            for (const auto& spk_man_pair : m_spk_managers) {
                spk_man_pair.second->RewriteDB();
            }
        }
    }

    if (nZapWalletTxRet != DBErrors::LOAD_OK)
        return nZapWalletTxRet;

    return DBErrors::LOAD_OK;
}

bool CWallet::SetAddressBookWithDB(WalletBatch& batch, const CTxDestination& address, const std::string& strName, const std::string& strPurpose)
{
    bool fUpdated = false;
    {
        LOCK(cs_wallet);
        std::map<CTxDestination, CAddressBookData>::iterator mi = mapAddressBook.find(address);
        fUpdated = mi != mapAddressBook.end();
        mapAddressBook[address].name = strName;
        if (!strPurpose.empty()) /* update purpose only if requested */
            mapAddressBook[address].purpose = strPurpose;
    }
    NotifyAddressBookChanged(this, address, strName, IsMine(address) != ISMINE_NO,
                             strPurpose, (fUpdated ? CT_UPDATED : CT_NEW) );
    if (!strPurpose.empty() && !batch.WritePurpose(EncodeDestination(address), strPurpose))
        return false;
    return batch.WriteName(EncodeDestination(address), strName);
}

bool CWallet::SetAddressBook(const CTxDestination& address, const std::string& strName, const std::string& strPurpose)
{
    WalletBatch batch(*database);
    return SetAddressBookWithDB(batch, address, strName, strPurpose);
}

bool CWallet::DelAddressBook(const CTxDestination& address)
{
    {
        LOCK(cs_wallet);

        // Delete destdata tuples associated with address
        std::string strAddress = EncodeDestination(address);
        for (const std::pair<const std::string, std::string> &item : mapAddressBook[address].destdata)
        {
            WalletBatch(*database).EraseDestData(strAddress, item.first);
        }
        mapAddressBook.erase(address);
    }

    NotifyAddressBookChanged(this, address, "", IsMine(address) != ISMINE_NO, "", CT_DELETED);

    WalletBatch(*database).ErasePurpose(EncodeDestination(address));
    return WalletBatch(*database).EraseName(EncodeDestination(address));
}

size_t CWallet::KeypoolCountExternalKeys()
{
    AssertLockHeld(cs_wallet);

    unsigned int count = 0;
    for (auto spk_man : GetActiveScriptPubKeyMans()) {
        count += spk_man->KeypoolCountExternalKeys();
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

bool CWallet::GetNewDestination(const OutputType type, const std::string label, CTxDestination& dest, std::string& error, bool add_blinding_key)
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
            boost::apply_visitor(SetBlindingPubKeyVisitor(blinding_pubkey), dest);
        }
    }
    if (result) {
        SetAddressBook(dest, label, "receive");
    }

    return result;
}

bool CWallet::GetNewChangeDestination(const OutputType type, CTxDestination& dest, std::string& error, bool add_blinding_key)
{
    LOCK(cs_wallet);
    error.clear();

    ReserveDestination reservedest(this, type);
    if (!reservedest.GetReservedDestination(dest, true)) {
        error = "Error: Keypool ran out, please call keypoolrefill first";
        return false;
    }
    if (add_blinding_key) {
        CPubKey blinding_pubkey = GetBlindingPubKey(GetScriptForDestination(dest));
        reservedest.SetBlindingPubKey(blinding_pubkey, dest);
    }

    reservedest.KeepDestination();
    return true;
}

int64_t CWallet::GetOldestKeyPoolTime()
{
    LOCK(cs_wallet);
    int64_t oldestKey = std::numeric_limits<int64_t>::max();
    for (const auto& spk_man_pair : m_spk_managers) {
        oldestKey = std::min(oldestKey, spk_man_pair.second->GetOldestKeyPoolTime());
    }
    return oldestKey;
}

void CWallet::MarkDestinationsDirty(const std::set<CTxDestination>& destinations) {
    for (auto& entry : mapWallet) {
        CWalletTx& wtx = entry.second;
        if (wtx.m_is_cache_empty) continue;
        for (unsigned int i = 0; i < wtx.tx->vout.size(); i++) {
            CTxDestination dst;
            if (ExtractDestination(wtx.tx->vout[i].scriptPubKey, dst) && destinations.count(dst)) {
                wtx.MarkDirty();
                break;
            }
        }
    }
}

std::map<CTxDestination, CAmount> CWallet::GetAddressBalances(interfaces::Chain::Lock& locked_chain)
{
    std::map<CTxDestination, CAmount> balances;

    {
        LOCK(cs_wallet);
        std::set<uint256> trusted_parents;
        for (const auto& walletEntry : mapWallet)
        {
            const CWalletTx& wtx = walletEntry.second;

            if (!wtx.IsTrusted(locked_chain, trusted_parents))
                continue;

            if (wtx.IsImmatureCoinBase())
                continue;

            int nDepth = wtx.GetDepthInMainChain();
            if (nDepth < (wtx.IsFromMe(ISMINE_ALL) ? 0 : 1))
                continue;

            for (unsigned int i = 0; i < wtx.tx->vout.size(); i++)
            {
                CTxDestination addr;
                if (!IsMine(wtx.tx->vout[i]))
                    continue;
                if(!ExtractDestination(wtx.tx->vout[i].scriptPubKey, addr))
                    continue;

                CAmount n = IsSpent(walletEntry.first, i) ? 0 : wtx.GetOutputValueOut(i);

                if (!balances.count(addr))
                    balances[addr] = 0;

                if (n < 0) {
                    continue;
                }
                balances[addr] += n;
            }
        }
    }

    return balances;
}

std::set< std::set<CTxDestination> > CWallet::GetAddressGroupings()
{
    AssertLockHeld(cs_wallet);
    std::set< std::set<CTxDestination> > groupings;
    std::set<CTxDestination> grouping;

    for (const auto& walletEntry : mapWallet)
    {
        const CWalletTx& wtx = walletEntry.second;

        if (wtx.tx->vin.size() > 0)
        {
            bool any_mine = false;
            // group all input addresses with each other
            for (const CTxIn& txin : wtx.tx->vin)
            {
                CTxDestination address;
                if(!IsMine(txin)) /* If this input isn't mine, ignore it */
                    continue;
                if(!ExtractDestination(mapWallet.at(txin.prevout.hash).tx->vout[txin.prevout.n].scriptPubKey, address))
                    continue;
                grouping.insert(address);
                any_mine = true;
            }

            // group change with input addresses
            if (any_mine)
            {
               for (const CTxOut& txout : wtx.tx->vout)
                   if (IsChange(txout))
                   {
                       CTxDestination txoutAddr;
                       if(!ExtractDestination(txout.scriptPubKey, txoutAddr))
                           continue;
                       grouping.insert(txoutAddr);
                   }
            }
            if (grouping.size() > 0)
            {
                groupings.insert(grouping);
                grouping.clear();
            }
        }

        // group lone addrs by themselves
        for (const auto& txout : wtx.tx->vout)
            if (IsMine(txout))
            {
                CTxDestination address;
                if(!ExtractDestination(txout.scriptPubKey, address))
                    continue;
                grouping.insert(address);
                groupings.insert(grouping);
                grouping.clear();
            }
    }

    std::set< std::set<CTxDestination>* > uniqueGroupings; // a set of pointers to groups of addresses
    std::map< CTxDestination, std::set<CTxDestination>* > setmap;  // map addresses to the unique group containing it
    for (std::set<CTxDestination> _grouping : groupings)
    {
        // make a set of all the groups hit by this new group
        std::set< std::set<CTxDestination>* > hits;
        std::map< CTxDestination, std::set<CTxDestination>* >::iterator it;
        for (const CTxDestination& address : _grouping)
            if ((it = setmap.find(address)) != setmap.end())
                hits.insert((*it).second);

        // merge all hit groups into a new single group and delete old groups
        std::set<CTxDestination>* merged = new std::set<CTxDestination>(_grouping);
        for (std::set<CTxDestination>* hit : hits)
        {
            merged->insert(hit->begin(), hit->end());
            uniqueGroupings.erase(hit);
            delete hit;
        }
        uniqueGroupings.insert(merged);

        // update setmap
        for (const CTxDestination& element : *merged)
            setmap[element] = merged;
    }

    std::set< std::set<CTxDestination> > ret;
    for (const std::set<CTxDestination>* uniqueGrouping : uniqueGroupings)
    {
        ret.insert(*uniqueGrouping);
        delete uniqueGrouping;
    }

    return ret;
}

std::set<CTxDestination> CWallet::GetLabelAddresses(const std::string& label) const
{
    LOCK(cs_wallet);
    std::set<CTxDestination> result;
    for (const std::pair<const CTxDestination, CAddressBookData>& item : mapAddressBook)
    {
        const CTxDestination& address = item.first;
        const std::string& strName = item.second.name;
        if (strName == label)
            result.insert(address);
    }
    return result;
}

bool ReserveDestination::GetReservedDestination(CTxDestination& dest, bool internal)
{
    m_spk_man = pwallet->GetScriptPubKeyMan(type, internal);
    if (!m_spk_man) {
        return false;
    }


    if (nIndex == -1)
    {
        m_spk_man->TopUp();

        CKeyPool keypool;
        if (!m_spk_man->GetReservedDestination(type, internal, address, nIndex, keypool)) {
            return false;
        }
        fInternal = keypool.fInternal;
    }
    dest = address;
    return true;
}

void ReserveDestination::SetBlindingPubKey(const CPubKey& blinding_pubkey, CTxDestination& dest)
{
    boost::apply_visitor(SetBlindingPubKeyVisitor(blinding_pubkey), address);
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

void CWallet::LockCoin(const COutPoint& output)
{
    AssertLockHeld(cs_wallet);
    setLockedCoins.insert(output);
}

void CWallet::UnlockCoin(const COutPoint& output)
{
    AssertLockHeld(cs_wallet);
    setLockedCoins.erase(output);
}

void CWallet::UnlockAllCoins()
{
    AssertLockHeld(cs_wallet);
    setLockedCoins.clear();
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

void CWallet::GetKeyBirthTimes(interfaces::Chain::Lock& locked_chain, std::map<CKeyID, int64_t>& mapKeyBirth) const {
    AssertLockHeld(cs_wallet);
    mapKeyBirth.clear();

    LegacyScriptPubKeyMan* spk_man = GetLegacyScriptPubKeyMan();
    assert(spk_man != nullptr);
    LOCK(spk_man->cs_KeyStore);

    // get birth times for keys with metadata
    for (const auto& entry : spk_man->mapKeyMetadata) {
        if (entry.second.nCreateTime) {
            mapKeyBirth[entry.first] = entry.second.nCreateTime;
        }
    }

    // map in which we'll infer heights of other keys
    const Optional<int> tip_height = locked_chain.getHeight();
    const int max_height = tip_height && *tip_height > 144 ? *tip_height - 144 : 0; // the tip can be reorganized; use a 144-block safety margin
    std::map<CKeyID, int> mapKeyFirstBlock;
    for (const CKeyID &keyid : spk_man->GetKeys()) {
        if (mapKeyBirth.count(keyid) == 0)
            mapKeyFirstBlock[keyid] = max_height;
    }

    // if there are no such keys, we're done
    if (mapKeyFirstBlock.empty())
        return;

    // find first block that affects those keys, if there are any left
    for (const auto& entry : mapWallet) {
        // iterate over all wallet transactions...
        const CWalletTx &wtx = entry.second;
        if (Optional<int> height = locked_chain.getBlockHeight(wtx.m_confirm.hashBlock)) {
            // ... which are already in a block
            for (const CTxOut &txout : wtx.tx->vout) {
                // iterate over all their outputs
                for (const auto &keyid : GetAffectedKeys(txout.scriptPubKey, *spk_man)) {
                    // ... and all their affected keys
                    std::map<CKeyID, int>::iterator rit = mapKeyFirstBlock.find(keyid);
                    if (rit != mapKeyFirstBlock.end() && *height < rit->second)
                        rit->second = *height;
                }
            }
        }
    }

    // Extract block timestamps for those keys
    for (const auto& entry : mapKeyFirstBlock)
        mapKeyBirth[entry.first] = locked_chain.getBlockTime(entry.second) - TIMESTAMP_WINDOW; // block times can be 2h off
}

/**
 * Compute smart timestamp for a transaction being added to the wallet.
 *
 * Logic:
 * - If sending a transaction, assign its timestamp to the current time.
 * - If receiving a transaction outside a block, assign its timestamp to the
 *   current time.
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
unsigned int CWallet::ComputeTimeSmart(const CWalletTx& wtx) const
{
    unsigned int nTimeSmart = wtx.nTimeReceived;
    if (!wtx.isUnconfirmed() && !wtx.isAbandoned()) {
        int64_t blocktime;
        if (chain().findBlock(wtx.m_confirm.hashBlock, nullptr /* block */, &blocktime)) {
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
        } else {
            WalletLogPrintf("%s: found %s in block %s not in index\n", __func__, wtx.GetHash().ToString(), wtx.m_confirm.hashBlock.ToString());
        }
    }
    return nTimeSmart;
}

bool CWallet::AddDestData(WalletBatch& batch, const CTxDestination &dest, const std::string &key, const std::string &value)
{
    if (boost::get<CNoDestination>(&dest))
        return false;

    mapAddressBook[dest].destdata.insert(std::make_pair(key, value));
    return batch.WriteDestData(EncodeDestination(dest), key, value);
}

bool CWallet::EraseDestData(WalletBatch& batch, const CTxDestination &dest, const std::string &key)
{
    if (!mapAddressBook[dest].destdata.erase(key))
        return false;
    return batch.EraseDestData(EncodeDestination(dest), key);
}

void CWallet::LoadDestData(const CTxDestination &dest, const std::string &key, const std::string &value)
{
    mapAddressBook[dest].destdata.insert(std::make_pair(key, value));
}

bool CWallet::GetDestData(const CTxDestination &dest, const std::string &key, std::string *value) const
{
    std::map<CTxDestination, CAddressBookData>::const_iterator i = mapAddressBook.find(dest);
    if(i != mapAddressBook.end())
    {
        CAddressBookData::StringMap::const_iterator j = i->second.destdata.find(key);
        if(j != i->second.destdata.end())
        {
            if(value)
                *value = j->second;
            return true;
        }
    }
    return false;
}

std::vector<std::string> CWallet::GetDestValues(const std::string& prefix) const
{
    std::vector<std::string> values;
    for (const auto& address : mapAddressBook) {
        for (const auto& data : address.second.destdata) {
            if (!data.first.compare(0, prefix.size(), prefix)) {
                values.emplace_back(data.second);
            }
        }
    }
    return values;
}

bool CWallet::Verify(interfaces::Chain& chain, const WalletLocation& location, bool salvage_wallet, std::string& error_string, std::vector<std::string>& warnings)
{
    // Do some checking on wallet path. It should be either a:
    //
    // 1. Path where a directory can be created.
    // 2. Path to an existing directory.
    // 3. Path to a symlink to a directory.
    // 4. For backwards compatibility, the name of a data file in -walletdir.
    LOCK(cs_wallets);
    const fs::path& wallet_path = location.GetPath();
    fs::file_type path_type = fs::symlink_status(wallet_path).type();
    if (!(path_type == fs::file_not_found || path_type == fs::directory_file ||
          (path_type == fs::symlink_file && fs::is_directory(wallet_path)) ||
          (path_type == fs::regular_file && fs::path(location.GetName()).filename() == location.GetName()))) {
        error_string = strprintf(
              "Invalid -wallet path '%s'. -wallet path should point to a directory where wallet.dat and "
              "database/log.?????????? files can be stored, a location where such a directory could be created, "
              "or (for backwards compatibility) the name of an existing data file in -walletdir (%s)",
              location.GetName(), GetWalletDir());
        return false;
    }

    // Make sure that the wallet path doesn't clash with an existing wallet path
    if (IsWalletLoaded(wallet_path)) {
        error_string = strprintf("Error loading wallet %s. Duplicate -wallet filename specified.", location.GetName());
        return false;
    }

    // Keep same database environment instance across Verify/Recover calls below.
    std::unique_ptr<WalletDatabase> database = WalletDatabase::Create(wallet_path);

    try {
        if (!WalletBatch::VerifyEnvironment(wallet_path, error_string)) {
            return false;
        }
    } catch (const fs::filesystem_error& e) {
        error_string = strprintf("Error loading wallet %s. %s", location.GetName(), fsbridge::get_filesystem_error_message(e));
        return false;
    }

    if (salvage_wallet) {
        // Recover readable keypairs:
        CWallet dummyWallet(&chain, WalletLocation(), WalletDatabase::CreateDummy());
        std::string backup_filename;
        // Even if we don't use this lock in this function, we want to preserve
        // lock order in LoadToWallet if query of chain state is needed to know
        // tx status. If lock can't be taken, tx confirmation status may be not
        // reliable.
        auto locked_chain = dummyWallet.LockChain();
        if (!WalletBatch::Recover(wallet_path, (void *)&dummyWallet, WalletBatch::RecoverKeysOnlyFilter, backup_filename)) {
            return false;
        }
    }

    return WalletBatch::VerifyDatabaseFile(wallet_path, warnings, error_string);
}

std::shared_ptr<CWallet> CWallet::CreateWalletFromFile(interfaces::Chain& chain, const WalletLocation& location, std::string& error, std::vector<std::string>& warnings, uint64_t wallet_creation_flags)
{
    const std::string walletFile = WalletDataFilePath(location.GetPath()).string();

    // needed to restore wallet transaction meta data after -zapwallettxes
    std::vector<CWalletTx> vWtx;

    if (gArgs.GetBoolArg("-zapwallettxes", false)) {
        chain.initMessage(_("Zapping all transactions from wallet...").translated);

        std::unique_ptr<CWallet> tempWallet = MakeUnique<CWallet>(&chain, location, WalletDatabase::Create(location.GetPath()));
        DBErrors nZapWalletRet = tempWallet->ZapWalletTx(vWtx);
        if (nZapWalletRet != DBErrors::LOAD_OK) {
            error = strprintf(_("Error loading %s: Wallet corrupted").translated, walletFile);
            return nullptr;
        }
    }

    chain.initMessage(_("Loading wallet...").translated);

    int64_t nStart = GetTimeMillis();
    bool fFirstRun = true;
    // TODO: Can't use std::make_shared because we need a custom deleter but
    // should be possible to use std::allocate_shared.
    std::shared_ptr<CWallet> walletInstance(new CWallet(&chain, location, WalletDatabase::Create(location.GetPath())), ReleaseWallet);
    DBErrors nLoadWalletRet = walletInstance->LoadWallet(fFirstRun);
    if (nLoadWalletRet != DBErrors::LOAD_OK) {
        if (nLoadWalletRet == DBErrors::CORRUPT) {
            error = strprintf(_("Error loading %s: Wallet corrupted").translated, walletFile);
            return nullptr;
        }
        else if (nLoadWalletRet == DBErrors::NONCRITICAL_ERROR)
        {
            warnings.push_back(strprintf(_("Error reading %s! All keys read correctly, but transaction data"
                                          " or address book entries might be missing or incorrect.").translated,
                walletFile));
        }
        else if (nLoadWalletRet == DBErrors::TOO_NEW) {
            error = strprintf(_("Error loading %s: Wallet requires newer version of %s").translated, walletFile, PACKAGE_NAME);
            return nullptr;
        }
        else if (nLoadWalletRet == DBErrors::NEED_REWRITE)
        {
            error = strprintf(_("Wallet needed to be rewritten: restart %s to complete").translated, PACKAGE_NAME);
            return nullptr;
        }
        else {
            error = strprintf(_("Error loading %s").translated, walletFile);
            return nullptr;
        }
    }

    int prev_version = walletInstance->GetVersion();
    if (gArgs.GetBoolArg("-upgradewallet", fFirstRun))
    {
        int nMaxVersion = gArgs.GetArg("-upgradewallet", 0);
        if (nMaxVersion == 0) // the -upgradewallet without argument case
        {
            walletInstance->WalletLogPrintf("Performing wallet upgrade to %i\n", FEATURE_LATEST);
            nMaxVersion = FEATURE_LATEST;
            walletInstance->SetMinVersion(FEATURE_LATEST); // permanently upgrade the wallet immediately
        }
        else
            walletInstance->WalletLogPrintf("Allowing wallet upgrade up to %i\n", nMaxVersion);
        if (nMaxVersion < walletInstance->GetVersion())
        {
            error = _("Cannot downgrade wallet").translated;
            return nullptr;
        }
        walletInstance->SetMaxVersion(nMaxVersion);
    }

    // Upgrade to HD if explicit upgrade
    if (gArgs.GetBoolArg("-upgradewallet", false)) {
        LOCK(walletInstance->cs_wallet);

        // Do not upgrade versions to any version between HD_SPLIT and FEATURE_PRE_SPLIT_KEYPOOL unless already supporting HD_SPLIT
        int max_version = walletInstance->GetVersion();
        if (!walletInstance->CanSupportFeature(FEATURE_HD_SPLIT) && max_version >= FEATURE_HD_SPLIT && max_version < FEATURE_PRE_SPLIT_KEYPOOL) {
            error = _("Cannot upgrade a non HD split wallet without upgrading to support pre split keypool. Please use -upgradewallet=169900 or -upgradewallet with no version specified.").translated;
            return nullptr;
        }

        for (auto spk_man : walletInstance->GetActiveScriptPubKeyMans()) {
            if (!spk_man->Upgrade(prev_version, error)) {
                return nullptr;
            }
        }
    }

    if (fFirstRun)
    {
        // ensure this wallet.dat can only be opened by clients supporting HD with chain split and expects no default key
        walletInstance->SetMinVersion(FEATURE_LATEST);

        walletInstance->SetWalletFlags(wallet_creation_flags, false);

        // Always create LegacyScriptPubKeyMan for now
        walletInstance->SetupLegacyScriptPubKeyMan();

        if (!(wallet_creation_flags & (WALLET_FLAG_DISABLE_PRIVATE_KEYS | WALLET_FLAG_BLANK_WALLET))) {
            LOCK(walletInstance->cs_wallet);
            for (auto spk_man : walletInstance->GetActiveScriptPubKeyMans()) {
                if (!spk_man->SetupGeneration()) {
                    error = _("Unable to generate initial keys").translated;
                    return nullptr;
                }
            }
        }

        auto locked_chain = chain.lock();
        walletInstance->ChainStateFlushed(locked_chain->getTipLocator());
    } else if (wallet_creation_flags & WALLET_FLAG_DISABLE_PRIVATE_KEYS) {
        // Make it impossible to disable private keys after creation
        error = strprintf(_("Error loading %s: Private keys can only be disabled during creation").translated, walletFile);
        return NULL;
    } else if (walletInstance->IsWalletFlagSet(WALLET_FLAG_DISABLE_PRIVATE_KEYS)) {
        for (auto spk_man : walletInstance->GetActiveScriptPubKeyMans()) {
            if (spk_man->HavePrivateKeys()) {
                warnings.push_back(strprintf(_("Warning: Private keys detected in wallet {%s} with disabled private keys").translated, walletFile));
                break;
            }
        }
    }

    if (!gArgs.GetArg("-addresstype", "").empty() && !ParseOutputType(gArgs.GetArg("-addresstype", ""), walletInstance->m_default_address_type)) {
        error = strprintf(_("Unknown address type '%s'").translated, gArgs.GetArg("-addresstype", ""));
        return nullptr;
    }

    if (!gArgs.GetArg("-changetype", "").empty() && !ParseOutputType(gArgs.GetArg("-changetype", ""), walletInstance->m_default_change_type)) {
        error = strprintf(_("Unknown change type '%s'").translated, gArgs.GetArg("-changetype", ""));
        return nullptr;
    }

    if (gArgs.IsArgSet("-mintxfee")) {
        CAmount n = 0;
        if (!ParseMoney(gArgs.GetArg("-mintxfee", ""), n) || 0 == n) {
            error = AmountErrMsg("mintxfee", gArgs.GetArg("-mintxfee", "")).translated;
            return nullptr;
        }
        if (n > HIGH_TX_FEE_PER_KB) {
            warnings.push_back(AmountHighWarn("-mintxfee").translated + " " +
                              _("This is the minimum transaction fee you pay on every transaction.").translated);
        }
        walletInstance->m_min_fee = CFeeRate(n);
    }

    if (gArgs.IsArgSet("-fallbackfee")) {
        CAmount nFeePerK = 0;
        if (!ParseMoney(gArgs.GetArg("-fallbackfee", ""), nFeePerK)) {
            error = strprintf(_("Invalid amount for -fallbackfee=<amount>: '%s'").translated, gArgs.GetArg("-fallbackfee", ""));
            return nullptr;
        }
        if (nFeePerK > HIGH_TX_FEE_PER_KB) {
            warnings.push_back(AmountHighWarn("-fallbackfee").translated + " " +
                              _("This is the transaction fee you may pay when fee estimates are not available.").translated);
        }
        walletInstance->m_fallback_fee = CFeeRate(nFeePerK);
    }
    // Disable fallback fee in case value was set to 0, enable if non-null value
    walletInstance->m_allow_fallback_fee = walletInstance->m_fallback_fee.GetFeePerK() != 0;

    if (gArgs.IsArgSet("-discardfee")) {
        CAmount nFeePerK = 0;
        if (!ParseMoney(gArgs.GetArg("-discardfee", ""), nFeePerK)) {
            error = strprintf(_("Invalid amount for -discardfee=<amount>: '%s'").translated, gArgs.GetArg("-discardfee", ""));
            return nullptr;
        }
        if (nFeePerK > HIGH_TX_FEE_PER_KB) {
            warnings.push_back(AmountHighWarn("-discardfee").translated + " " +
                              _("This is the transaction fee you may discard if change is smaller than dust at this level").translated);
        }
        walletInstance->m_discard_rate = CFeeRate(nFeePerK);
    }
    if (gArgs.IsArgSet("-paytxfee")) {
        CAmount nFeePerK = 0;
        if (!ParseMoney(gArgs.GetArg("-paytxfee", ""), nFeePerK)) {
            error = AmountErrMsg("paytxfee", gArgs.GetArg("-paytxfee", "")).translated;
            return nullptr;
        }
        if (nFeePerK > HIGH_TX_FEE_PER_KB) {
            warnings.push_back(AmountHighWarn("-paytxfee").translated + " " +
                              _("This is the transaction fee you will pay if you send a transaction.").translated);
        }
        walletInstance->m_pay_tx_fee = CFeeRate(nFeePerK, 1000);
        if (walletInstance->m_pay_tx_fee < chain.relayMinFee()) {
            error = strprintf(_("Invalid amount for -paytxfee=<amount>: '%s' (must be at least %s)").translated,
                gArgs.GetArg("-paytxfee", ""), chain.relayMinFee().ToString());
            return nullptr;
        }
    }

    if (gArgs.IsArgSet("-maxtxfee")) {
        CAmount nMaxFee = 0;
        if (!ParseMoney(gArgs.GetArg("-maxtxfee", ""), nMaxFee)) {
            error = AmountErrMsg("maxtxfee", gArgs.GetArg("-maxtxfee", "")).translated;
            return nullptr;
        }
        if (nMaxFee > HIGH_MAX_TX_FEE) {
            warnings.push_back(_("-maxtxfee is set very high! Fees this large could be paid on a single transaction.").translated);
        }
        if (CFeeRate(nMaxFee, 1000) < chain.relayMinFee()) {
            error = strprintf(_("Invalid amount for -maxtxfee=<amount>: '%s' (must be at least the minrelay fee of %s to prevent stuck transactions)").translated,
                                       gArgs.GetArg("-maxtxfee", ""), chain.relayMinFee().ToString());
            return nullptr;
        }
        walletInstance->m_default_max_tx_fee = nMaxFee;
    }

    if (chain.relayMinFee().GetFeePerK() > HIGH_TX_FEE_PER_KB) {
        warnings.push_back(AmountHighWarn("-minrelaytxfee").translated + " " +
                    _("The wallet will avoid paying less than the minimum relay fee.").translated);
    }

    walletInstance->m_confirm_target = gArgs.GetArg("-txconfirmtarget", DEFAULT_TX_CONFIRM_TARGET);
    walletInstance->m_spend_zero_conf_change = gArgs.GetBoolArg("-spendzeroconfchange", DEFAULT_SPEND_ZEROCONF_CHANGE);
    walletInstance->m_signal_rbf = gArgs.GetBoolArg("-walletrbf", DEFAULT_WALLET_RBF);

    walletInstance->WalletLogPrintf("Wallet completed loading in %15dms\n", GetTimeMillis() - nStart);

    // Try to top up keypool. No-op if the wallet is locked.
    walletInstance->TopUpKeyPool();

    auto locked_chain = chain.lock();
    LOCK(walletInstance->cs_wallet);

    int rescan_height = 0;
    if (!gArgs.GetBoolArg("-rescan", false))
    {
        WalletBatch batch(*walletInstance->database);
        CBlockLocator locator;
        if (batch.ReadBestBlock(locator)) {
            if (const Optional<int> fork_height = locked_chain->findLocatorFork(locator)) {
                rescan_height = *fork_height;
            }
        }
    }

    const Optional<int> tip_height = locked_chain->getHeight();
    if (tip_height) {
        walletInstance->m_last_block_processed = locked_chain->getBlockHash(*tip_height);
        walletInstance->m_last_block_processed_height = *tip_height;
    } else {
        walletInstance->m_last_block_processed.SetNull();
        walletInstance->m_last_block_processed_height = -1;
    }

    if (tip_height && *tip_height != rescan_height)
    {
        // We can't rescan beyond non-pruned blocks, stop and throw an error.
        // This might happen if a user uses an old wallet within a pruned node
        // or if they ran -disablewallet for a longer time, then decided to re-enable
        if (chain.havePruned()) {
            // Exit early and print an error.
            // If a block is pruned after this check, we will load the wallet,
            // but fail the rescan with a generic error.
            int block_height = *tip_height;
            while (block_height > 0 && locked_chain->haveBlockOnDisk(block_height - 1) && rescan_height != block_height) {
                --block_height;
            }

            if (rescan_height != block_height) {
                error = _("Prune: last wallet synchronisation goes beyond pruned data. You need to -reindex (download the whole blockchain again in case of pruned node)").translated;
                return nullptr;
            }
        }

        chain.initMessage(_("Rescanning...").translated);
        walletInstance->WalletLogPrintf("Rescanning last %i blocks (from block %i)...\n", *tip_height - rescan_height, rescan_height);

        // No need to read and scan block if block was created before
        // our wallet birthday (as adjusted for block time variability)
        // The way the 'time_first_key' is initialized is just a workaround for the gcc bug #47679 since version 4.6.0.
        Optional<int64_t> time_first_key = MakeOptional(false, int64_t());;
        for (auto spk_man : walletInstance->GetAllScriptPubKeyMans()) {
            int64_t time = spk_man->GetTimeFirstKey();
            if (!time_first_key || time < *time_first_key) time_first_key = time;
        }
        if (time_first_key) {
            if (Optional<int> first_block = locked_chain->findFirstBlockWithTimeAndHeight(*time_first_key - TIMESTAMP_WINDOW, rescan_height, nullptr)) {
                rescan_height = *first_block;
            }
        }

        {
            WalletRescanReserver reserver(walletInstance.get());
            if (!reserver.reserve() || (ScanResult::SUCCESS != walletInstance->ScanForWalletTransactions(locked_chain->getBlockHash(rescan_height), {} /* stop block */, reserver, true /* update */).status)) {
                error = _("Failed to rescan the wallet during initialization").translated;
                return nullptr;
            }
        }
        walletInstance->ChainStateFlushed(locked_chain->getTipLocator());
        walletInstance->database->IncrementUpdateCounter();

        // Restore wallet transaction metadata after -zapwallettxes=1
        if (gArgs.GetBoolArg("-zapwallettxes", false) && gArgs.GetArg("-zapwallettxes", "1") != "2")
        {
            WalletBatch batch(*walletInstance->database);

            for (const CWalletTx& wtxOld : vWtx)
            {
                uint256 hash = wtxOld.GetHash();
                std::map<uint256, CWalletTx>::iterator mi = walletInstance->mapWallet.find(hash);
                if (mi != walletInstance->mapWallet.end())
                {
                    const CWalletTx* copyFrom = &wtxOld;
                    CWalletTx* copyTo = &mi->second;
                    copyTo->mapValue = copyFrom->mapValue;
                    copyTo->vOrderForm = copyFrom->vOrderForm;
                    copyTo->nTimeReceived = copyFrom->nTimeReceived;
                    copyTo->nTimeSmart = copyFrom->nTimeSmart;
                    copyTo->fFromMe = copyFrom->fFromMe;
                    copyTo->nOrderPos = copyFrom->nOrderPos;
                    batch.WriteTx(*copyTo);
                }
            }
        }
    }

    {
        LOCK(cs_wallets);
        for (auto& load_wallet : g_load_wallet_fns) {
            load_wallet(interfaces::MakeWallet(walletInstance));
        }
    }

    // Register with the validation interface. It's ok to do this after rescan since we're still holding locked_chain.
    walletInstance->handleNotifications();

    walletInstance->SetBroadcastTransactions(gArgs.GetBoolArg("-walletbroadcast", DEFAULT_WALLETBROADCAST));

    {
        walletInstance->WalletLogPrintf("setKeyPool.size() = %u\n",      walletInstance->GetKeyPoolSize());
        walletInstance->WalletLogPrintf("mapWallet.size() = %u\n",       walletInstance->mapWallet.size());
        walletInstance->WalletLogPrintf("mapAddressBook.size() = %u\n",  walletInstance->mapAddressBook.size());
    }

    return walletInstance;
}

void CWallet::handleNotifications()
{
    m_chain_notifications_handler = m_chain->handleNotifications(*this);
}

void CWallet::postInitProcess()
{
    auto locked_chain = chain().lock();
    LOCK(cs_wallet);

    // Add wallet transactions that aren't already in a block to mempool
    // Do this here as mempool requires genesis block to be loaded
    ReacceptWalletTransactions();

    // Update wallet transactions with current mempool transactions.
    chain().requestMempoolTransactions(*this);
}

bool CWallet::BackupWallet(const std::string& strDest)
{
    return database->Backup(strDest);
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

int CWalletTx::GetDepthInMainChain() const
{
    assert(pwallet != nullptr);
    AssertLockHeld(pwallet->cs_wallet);
    if (isUnconfirmed() || isAbandoned()) return 0;

    return (pwallet->GetLastBlockHeight() - m_confirm.block_height + 1) * (isConflicted() ? -1 : 1);
}

int CWalletTx::GetBlocksToMaturity() const
{
    if (!IsCoinBase())
        return 0;
    int chain_depth = GetDepthInMainChain();
    assert(chain_depth >= 0); // coinbase tx should not be conflicted
    return std::max(0, (COINBASE_MATURITY+1) - chain_depth);
}

bool CWalletTx::IsImmatureCoinBase() const
{
    // note GetBlocksToMaturity is 0 for non-coinbase tx
    return GetBlocksToMaturity() > 0;
}

std::vector<OutputGroup> CWallet::GroupOutputs(const std::vector<COutput>& outputs, bool single_coin) const {
    std::vector<OutputGroup> groups;
    std::map<std::pair<CAsset, CTxDestination>, OutputGroup> gmap;
    std::pair<CAsset, CTxDestination> dst;
    for (const auto& output : outputs) {
        if (output.fSpendable) {
            CInputCoin input_coin = output.GetInputCoin();
            dst.first = input_coin.asset;

            size_t ancestors, descendants;
            chain().getTransactionAncestry(output.tx->GetHash(), ancestors, descendants);
            if (!single_coin && ExtractDestination(output.tx->tx->vout[output.i].scriptPubKey, dst.second)) {
                // Limit output groups to no more than 10 entries, to protect
                // against inadvertently creating a too-large transaction
                // when using -avoidpartialspends
                if (gmap[dst].m_outputs.size() >= OUTPUT_GROUP_MAX_ENTRIES) {
                    groups.push_back(gmap[dst]);
                    gmap.erase(dst);
                }
                gmap[dst].Insert(input_coin, output.nDepth, output.tx->IsFromMe(ISMINE_ALL), ancestors, descendants);
            } else {
                groups.emplace_back(input_coin, output.nDepth, output.tx->IsFromMe(ISMINE_ALL), ancestors, descendants);
            }
        }
    }
    if (!single_coin) {
        for (const auto& it : gmap) groups.push_back(it.second);
    }
    return groups;
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
        WalletLogPrintf("%s scriptPubKey Manager for output type %d does not exist\n", internal ? "Internal" : "External", static_cast<int>(type));
        return nullptr;
    }
    return it->second;
}

ScriptPubKeyMan* CWallet::GetScriptPubKeyMan(const CScript& script) const
{
    SignatureData sigdata;
    for (const auto& spk_man_pair : m_spk_managers) {
        if (spk_man_pair.second->CanProvide(script, sigdata)) {
            return spk_man_pair.second.get();
        }
    }
    return nullptr;
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

std::unique_ptr<SigningProvider> CWallet::GetSigningProvider(const CScript& script) const
{
    SignatureData sigdata;
    return GetSigningProvider(script, sigdata);
}

std::unique_ptr<SigningProvider> CWallet::GetSigningProvider(const CScript& script, SignatureData& sigdata) const
{
    for (const auto& spk_man_pair : m_spk_managers) {
        if (spk_man_pair.second->CanProvide(script, sigdata)) {
            return spk_man_pair.second->GetSigningProvider(script);
        }
    }
    return nullptr;
}

LegacyScriptPubKeyMan* CWallet::GetLegacyScriptPubKeyMan() const
{
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
    if (!m_internal_spk_managers.empty() || !m_external_spk_managers.empty() || !m_spk_managers.empty()) {
        return;
    }

    auto spk_manager = std::unique_ptr<ScriptPubKeyMan>(new LegacyScriptPubKeyMan(*this));
    for (const auto& type : OUTPUT_TYPES) {
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
    if (!WalletBatch(*database).WriteOnlineKey(online_key_in)) {
        return false;
    }
    online_key = online_key_in;
    return true;
}

bool CWallet::SetOfflineXPubKey(const CExtPubKey& offline_xpub_in)
{
    LOCK(cs_wallet);
    if (!WalletBatch(*database).WriteOfflineXPubKey(offline_xpub_in)) {
        return false;
    }
    offline_xpub = offline_xpub_in;
    return true;
}

bool CWallet::SetOfflineDescriptor(const std::string& offline_desc_in)
{
    LOCK(cs_wallet);
    if (!WalletBatch(*database).WriteOfflineDescriptor(offline_desc_in)) {
        return false;
    }
    offline_desc = offline_desc_in;
    return true;
}

bool CWallet::SetOfflineCounter(int counter) {
    LOCK(cs_wallet);
    if (!WalletBatch(*database).WriteOfflineCounter(counter)) {
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

void CWalletTx::GetBlindingData(const unsigned int map_index, const std::vector<unsigned char>& vchRangeproof, const CConfidentialValue& conf_value, const CConfidentialAsset& conf_asset, const CConfidentialNonce nonce, const CScript& scriptPubKey, CPubKey* blinding_pubkey_out, CAmount* value_out, uint256* value_factor_out, CAsset* asset_out, uint256* asset_factor_out) const
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

        if (conf_value.IsExplicit()) {
            assert(conf_value.GetAmount() == amount);
        }
    } else {
        pwallet->ComputeBlindingData(conf_value, conf_asset, nonce, scriptPubKey, vchRangeproof, amount, pubkey, value_factor, asset_tag, asset_factor);
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

void CWalletTx::GetNonIssuanceBlindingData(const unsigned int output_index, CPubKey* blinding_pubkey_out, CAmount* value_out, uint256* value_factor_out, CAsset* asset_out, uint256* asset_factor_out) const {
    assert(output_index < tx->vout.size());
    const CTxOut& out = tx->vout[output_index];
    const CTxWitness& wit = tx->witness;
    GetBlindingData(output_index, wit.vtxoutwit.size() <= output_index ? std::vector<unsigned char>() : wit.vtxoutwit[output_index].vchRangeproof, out.nValue, out.nAsset, out.nNonce, out.scriptPubKey,
        blinding_pubkey_out, value_out, value_factor_out, asset_out, asset_factor_out);
}

void CWallet::ConnectScriptPubKeyManNotifiers()
{
    for (const auto& spk_man : GetActiveScriptPubKeyMans()) {
        spk_man->NotifyWatchonlyChanged.connect(NotifyWatchonlyChanged);
        spk_man->NotifyCanGetAddressesChanged.connect(NotifyCanGetAddressesChanged);
    }
}

CAmount CWalletTx::GetOutputValueOut(unsigned int output_index) const {
    CAmount ret;
    GetNonIssuanceBlindingData(output_index, nullptr, &ret, nullptr, nullptr, nullptr);
    return ret;
}

uint256 CWalletTx::GetOutputAmountBlindingFactor(unsigned int output_index) const {
    uint256 ret;
    GetNonIssuanceBlindingData(output_index, nullptr, nullptr, &ret, nullptr, nullptr);
    return ret;
}

uint256 CWalletTx::GetOutputAssetBlindingFactor(unsigned int output_index) const {
    uint256 ret;
    GetNonIssuanceBlindingData(output_index, nullptr, nullptr, nullptr, nullptr, &ret);
    return ret;
}

CAsset CWalletTx::GetOutputAsset(unsigned int output_index) const {
    CAsset ret;
    GetNonIssuanceBlindingData(output_index, nullptr, nullptr, nullptr, &ret, nullptr);
    return ret;
}

CPubKey CWalletTx::GetOutputBlindingPubKey(unsigned int output_index) const {
    CPubKey ret;
    GetNonIssuanceBlindingData(output_index, &ret, nullptr, nullptr, nullptr, nullptr);
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

uint256 CWalletTx::GetIssuanceBlindingFactor(unsigned int input_index, bool reissuance_token) const {
    assert(input_index < tx->vin.size());
    CAsset asset;
    const CAssetIssuance& issuance = tx->vin[input_index].assetIssuance;
    const CTxWitness& wit = tx->witness;
    GetIssuanceAssets(input_index, reissuance_token ? nullptr : &asset, reissuance_token ? &asset : nullptr);
    if (asset.IsNull()) {
        return uint256();
    }
    const std::vector<unsigned char>& rangeproof = wit.vtxinwit.size() <= input_index ? std::vector<unsigned char>() : (reissuance_token ? wit.vtxinwit[input_index].vchInflationKeysRangeproof : wit.vtxinwit[input_index].vchIssuanceAmountRangeproof);
    unsigned int mapValueInd = GetPseudoInputOffset(input_index, reissuance_token)+tx->vout.size();

    uint256 ret;
    CScript blindingScript(CScript() << OP_RETURN << std::vector<unsigned char>(tx->vin[input_index].prevout.hash.begin(), tx->vin[input_index].prevout.hash.end()) << tx->vin[input_index].prevout.n);
    GetBlindingData(mapValueInd, rangeproof, reissuance_token ? issuance.nInflationKeys : issuance.nAmount, CConfidentialAsset(asset), CConfidentialNonce(), blindingScript, nullptr, nullptr, &ret, nullptr, nullptr);
    return ret;
}

CAmount CWalletTx::GetIssuanceAmount(unsigned int input_index, bool reissuance_token) const {
    assert(input_index < tx->vin.size());
    CAsset asset;
    const CAssetIssuance& issuance = tx->vin[input_index].assetIssuance;
    const CTxWitness& wit = tx->witness;
    GetIssuanceAssets(input_index, reissuance_token ? nullptr : &asset, reissuance_token ? &asset : nullptr);
    if (asset.IsNull()) {
        return -1;
    }
    unsigned int mapValueInd = GetPseudoInputOffset(input_index, reissuance_token)+tx->vout.size();
    const std::vector<unsigned char>& rangeproof = wit.vtxinwit.size() <= input_index ? std::vector<unsigned char>() : (reissuance_token ? wit.vtxinwit[input_index].vchInflationKeysRangeproof : wit.vtxinwit[input_index].vchIssuanceAmountRangeproof);

    CAmount ret;
    CScript blindingScript(CScript() << OP_RETURN << std::vector<unsigned char>(tx->vin[input_index].prevout.hash.begin(), tx->vin[input_index].prevout.hash.end()) << tx->vin[input_index].prevout.n);
    GetBlindingData(mapValueInd, rangeproof, reissuance_token ? issuance.nInflationKeys : issuance.nAmount, CConfidentialAsset(asset), CConfidentialNonce(), blindingScript, nullptr, &ret, nullptr, nullptr, nullptr);
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

void CWalletTx::WipeUnknownBlindingData()
{
    for (unsigned int n = 0; n < tx->vout.size(); n++) {
        if (GetOutputValueOut(n) == -1) {
            mapValue["blindingdata"][138 * n] = 0;
        }
    }
    for (unsigned int n = 0; n < tx->vin.size(); n++) {
        if (!tx->vin[n].assetIssuance.nAmount.IsNull()) {
            if (GetIssuanceAmount(n, false) == -1) {
                mapValue["blindingdata"][138 * (tx->vout.size() + GetPseudoInputOffset(n, false))] = 0;
            }
        }
        if (!tx->vin[n].assetIssuance.nInflationKeys.IsNull()) {
            if (GetIssuanceAmount(n, true) == -1) {
                mapValue["blindingdata"][138 * (tx->vout.size() + GetPseudoInputOffset(n, true))] = 0;
            }
        }
    }
}

std::map<uint256, std::pair<CAsset, CAsset> > CWallet::GetReissuanceTokenTypes() const {
    std::map<uint256, std::pair<CAsset, CAsset> > tokenMap;
    {
        auto locked_chain = chain().lock();
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

CKey CWallet::GetBlindingKey(const CScript* script) const
{
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

    return WalletBatch(*database).WriteSpecificBlindingKey(scriptid, key);
}

bool CWallet::SetMasterBlindingKey(const uint256& key)
{
    AssertLockHeld(cs_wallet);
    if (!WalletBatch(*database).WriteBlindingDerivationKey(key)) {
        return false;
    }
    blinding_derivation_key = key;
    return true;
}

// END ELEMENTS
//

