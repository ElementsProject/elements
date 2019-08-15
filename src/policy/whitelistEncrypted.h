// Copyright (c) 2019 The CommerceBlock Developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#pragma once

#include "whitelist.h"
#include <map>
#include "univalue/include/univalue.h"
#ifdef ENABLE_WALLET
#include "wallet/wallet.h"
#endif
#include <queue>

class CWhiteListEncrypted : public CWhiteList{
public:
	CWhiteListEncrypted();
	virtual ~CWhiteListEncrypted();

	enum status {
  		white,
  		black
  	};

	virtual bool Load(CCoinsView *view);
	
	virtual void add_destination(const CTxDestination& dest);

	virtual void add_derived(const CBitcoinAddress& address,  const CPubKey& pubKey, 
	  const std::unique_ptr<CPubKey>& kycPubKey);

	virtual void add_derived(const CBitcoinAddress& address, const CPubKey& pubKey);

	virtual void add_derived(const std::string& sAddress, const std::string& sPubKey, 
		const std::string& sKYCPubKey);

	virtual void add_derived(const std::string& sAddress, const std::string& sKey);

	//Multisig whitelisting below
	virtual void add_multisig_whitelist(const std::string& sAddress, const UniValue& sPubKeys, 
  		const std::string& sKYCAddress, const uint8_t nMultisig);

	virtual void add_multisig_whitelist(const std::string& addressIn, const UniValue& keys, 
		const uint8_t nMultisig);

	virtual void add_multisig_whitelist(const CBitcoinAddress& address, const std::vector<CPubKey>& pubKeys, 
  		const std::unique_ptr<CPubKey>& kycPubKey, const uint8_t nMultisig);

	virtual void add_multisig_whitelist(const CBitcoinAddress& address, const std::vector<CPubKey>& pubKeys,
		const uint8_t nMultisig);

  	bool RegisterDecryptedAddresses(const std::vector<unsigned char>& data, const std::unique_ptr<CPubKey>& kycPubKey, const bool bOnboard);

  	virtual bool IsRegisterAddressMulti(const std::vector<unsigned char>::const_iterator start,const std::vector<unsigned char>::const_iterator vend);

  	virtual bool RegisterAddress(const CTransaction& tx, const CBlockIndex* pindex);
  	
	virtual bool RegisterAddress(const CTransaction& tx, const CCoinsViewCache& mapInputs);
	
  	//Update from transaction
  	virtual bool Update(const CTransaction& tx, const CCoinsViewCache& mapInputs);

  	virtual void clear();

  	virtual bool is_whitelisted(const CTxDestination keyId);

  	//Get a kyc key from the _kycUnassignedQueue. Removes the element from the queue.
  	virtual bool get_unassigned_kyc(CPubKey& pubKey);
  	//Get the next key without removing it
  	virtual bool peek_unassigned_kyc(CPubKey& pubKey);

  	virtual bool LookupKYCKey(const CTxDestination& keyId, CKeyID& kycKeyIdFound);

  	virtual bool LookupKYCKey(const CTxDestination& keyId, CPubKey& pubKeyFound);

  	virtual bool LookupKYCKey(const CTxDestination& keyId, CKeyID& kycKeyIdFound, CPubKey& kycPubKeyFound);

	virtual bool find_kyc_whitelisted(const CKeyID& keyId);

	virtual void whitelist_kyc(const CPubKey& pubKey, const COutPoint* outPoint=nullptr);

	// My ending addresses - added to whitelist by me in a add to whitelist transaction waiting to be included in a block
	virtual void add_my_pending(const CTxDestination keyId);

	virtual void remove_my_pending(const CTxDestination keyId);

	virtual bool is_my_pending(const CTxDestination keyId);

	virtual unsigned int n_my_pending();

  	virtual void add_unassigned_kyc(const CPubKey& pubKey);

	virtual bool get_kycpubkey_outpoint(const CKeyID& kycPubKeyId, COutPoint& outPoint);

	virtual bool get_kycpubkey_outpoint(const CPubKey& kycPubKey, COutPoint& outPoint);


private:
	bool LookupTweakedPubKeys(const CTxDestination& address, 
		std::vector<CPubKey>& pubKeyFound);

	std::queue<CPubKey> _kycUnassignedQueue;

	//A map of address to kycPubKey
	std::map<CTxDestination, CKeyID> _kycMap;
	//A map of address to tweaked public key
	std::map<CTxDestination, std::vector<CPubKey>> _tweakedPubKeysMap;
	//Whitelisted KYC keys
	std::map<CKeyID, CWhiteListEncrypted::status> _kycStatusMap;

	//Map KYC key ID to public key
	std::map<CKeyID, CPubKey> _kycPubkeyMap;

	//Map KYC key ID to its latest policy transaction (required for blacklisting)
	std::map<CKeyID, COutPoint> _kycPubkeyOutPointMap;

	std::stringstream _datastream;


	bool set_kyc_status(const CKeyID& keyId, const CWhiteListEncrypted::status& status);

	bool find_kyc_status(const CKeyID& keyId, const CWhiteListEncrypted::status& status);

	// Returns true if if is whitelisted OR blackliosted
	bool find_kyc(const CKeyID& keyId);

	bool find_kyc_blacklisted(const CKeyID& keyId);

	void blacklist_kyc(const CPubKey& pubKey);

};
