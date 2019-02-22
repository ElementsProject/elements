// Copyright (c) 2018 The CommerceBlock Developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#pragma once

#include "policylist.h"
#include "wallet/wallet.h"
#include <map>
#include <queue>

class CWhiteList : public CPolicyList{
public:
	CWhiteList();
	virtual ~CWhiteList();

	enum status {
  		white,
  		black
  	};

	// Onboards a new user with addresses and kyc public key
	void onboard_new(const std::map<CBitcoinAddress, CPubKey>& addressMap, const CPubKey& kycPubKey);

	void add_derived(const CBitcoinAddress& address, const CPubKey& pubKey, 
		const CBitcoinAddress* kycAddress);
	void add_derived(const CBitcoinAddress& address, const CPubKey& pubKey);

	void add_derived(const std::string& sAddress, const std::string& sPubKey, 
		const std::string& sKYCAddress);
	void add_derived(const std::string& sAddress, const std::string& sKey);

	void blacklist_kyc(const CKeyID& keyId);

	void whitelist_kyc(const CKeyID& keyId);

	bool set_kyc_status(const CKeyID& keyId, const CWhiteList::status& status);

	bool find_kyc_status(const CKeyID& keyId, const CWhiteList::status& status);

	// Returns true if if is whitelisted OR blackliosted
	bool find_kyc(const CKeyID& keyId);

	bool find_kyc_whitelisted(const CKeyID& keyId);

	bool find_kyc_blacklisted(const CKeyID& keyId);

	void synchronise(CWhiteList* wl_new);

  	bool RegisterAddress(const CTransaction& tx, const CCoinsViewCache& mapInputs);

  	//Get a kyc key from the _kycUnassignedQueue. Removes the element from the queue.
  	bool get_unassigned_kyc(CKeyID& keyId);
  	void add_unassigned_kyc(const CKeyID& keyId);

  	//Lookup owner (idpubkey) of address
  	bool LookupKYCKey(const CKeyID& keyId, CKeyID& kycKeyIdFound);
  	bool LookupTweakedPubKey(const CKeyID& keyId, CPubKey& pubKeyFound);

  	//Update from transaction
  	virtual bool Update(const CTransaction& tx, const CCoinsViewCache& mapInputs);

  	virtual void clear();

  
private:
	//Make add_sorted private because we only want verified derived keys 
	//to be added to the CWhiteList.
	using CPolicyList::add_sorted;

	//A map of address to idPubKey
	std::map<CKeyID, CKeyID> _kycMap;
	//A map of address to tweaked public key
	std::map<CKeyID, CPubKey> _tweakedPubKeyMap;
	//Whitelisted KYC keys
	std::map<CKeyID, CWhiteList::status> _kycStatusMap;
	//KYC pub keys not yet assigned to any user
	std::queue<CKeyID> _kycUnassignedQueue;

	std::stringstream _datastream;
};
