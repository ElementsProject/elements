// Copyright (c) 2018 The CommerceBlock Developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#pragma once

#include "policylist.h"
#include <map>
#ifdef ENABLE_WALLET
#include "wallet/wallet.h"
#endif
#include <queue>

class CWhiteList : public CPolicyList{
public:
	CWhiteList();
	virtual ~CWhiteList();

	enum status {
  		white,
  		black
  	};

	bool Load(CCoinsView *view);

	void add_derived(const CBitcoinAddress& address, const CPubKey& pubKey, 
		const CBitcoinAddress* kycAddress);
	void add_derived(const CBitcoinAddress& address, const CPubKey& pubKey);

	void add_derived(const std::string& sAddress, const std::string& sPubKey, 
		const std::string& sKYCAddress);
	void add_derived(const std::string& sAddress, const std::string& sKey);


  	bool RegisterAddress(const CTransaction& tx, const CCoinsViewCache& mapInputs);

#ifdef ENABLE_WALLET
  	bool RegisterAddress(const CTransaction& tx, const CBlockIndex* pindex);
#endif //#ifdef ENABLE_WALLET
	
  	//Update from transaction
  	virtual bool Update(const CTransaction& tx, const CCoinsViewCache& mapInputs);

  	virtual void clear();

  	bool is_whitelisted(const CKeyID& keyId);

  	//Get a kyc key from the _kycUnassignedQueue. Removes the element from the queue.
  	bool get_unassigned_kyc(CPubKey& pubKey);
  	//Get the next key without removing it
  	bool peek_unassigned_kyc(CPubKey& pubKey);
  	void add_unassigned_kyc(const CPubKey& pubKey);

  	bool LookupKYCKey(const CKeyID& keyId, CKeyID& kycKeyIdFound);

	bool find_kyc_whitelisted(const CKeyID& keyId);

	void blacklist_kyc(const CKeyID& keyId);

	void whitelist_kyc(const CKeyID& keyId);

	// My ending addresses - added to whitelist by me in a add to whitelist transaction waiting to be included in a block
	void add_my_pending(const CKeyID& keyId);

	void remove_my_pending(const CKeyID& keyId);

	bool is_my_pending(const CKeyID& keyId);

	unsigned int n_my_pending();

	bool kycFromUserOnboard(const CPubKey& userOnboard, CPubKey& kyc);
  
private:
	//Make add_sorted private because we only want verified derived keys 
	//to be added to the CWhiteList.
	using CPolicyList::add_sorted;

	using CPolicyList::find;
	//A map of address to idPubKey
	std::map<CKeyID, CKeyID> _kycMap;
	//A map of address to tweaked public key
	std::map<CKeyID, CPubKey> _tweakedPubKeyMap;
	//Whitelisted KYC keys
	std::map<CKeyID, CWhiteList::status> _kycStatusMap;
	//Map user onboard key to KYC pub key
	std::map<CKeyID, CPubKey> _onboardMap;

	//KYC pub keys not yet assigned to any user
	std::queue<CPubKey> _kycUnassignedQueue;

	std::stringstream _datastream;

	std::set<CKeyID> _myPending;

	bool set_kyc_status(const CKeyID& keyId, const CWhiteList::status& status);

	bool find_kyc_status(const CKeyID& keyId, const CWhiteList::status& status);

	// Returns true if if is whitelisted OR blackliosted
	bool find_kyc(const CKeyID& keyId);

	bool find_kyc_blacklisted(const CKeyID& keyId);

	void synchronise(CWhiteList* wl_new);



  	//Lookup owner (idpubkey) of address
  	bool LookupTweakedPubKey(const CKeyID& keyId, CPubKey& pubKeyFound);
};
