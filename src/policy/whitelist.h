// Copyright (c) 2018 The CommerceBlock Developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#pragma once

#include "policylist.h"
#include <map>
#include "univalue/include/univalue.h"
#ifdef ENABLE_WALLET
#include "wallet/wallet.h"
#endif
#include <queue>

class CWhiteList : public CPolicyList{
public:
	CWhiteList();
	virtual ~CWhiteList();

	static const int64_t MAX_UNASSIGNED_KYCPUBKEYS=10000;

	enum status {
  		white,
  		black
  	};

	bool Load(CCoinsView *view);

	void add_destination(const CTxDestination& dest);

	void add_derived(const CBitcoinAddress& address, const CPubKey& pubKey, 
		const std::unique_ptr<CPubKey>& kycPubKey);

	void add_derived(const CBitcoinAddress& address, const CPubKey& pubKey);

	void add_derived(const std::string& sAddress, const std::string& sPubKey, 
		const std::string& sKYCPubKey);

	void add_derived(const std::string& sAddress, const std::string& sKey);

	//Multisig whitelisting below
	void add_multisig_whitelist(const std::string& sAddress, const UniValue& sPubKeys, 
  		const std::string& sKYCAddress, const uint8_t nMultisig);

	void add_multisig_whitelist(const std::string& addressIn, const UniValue& keys, 
		const uint8_t nMultisig);

	void add_multisig_whitelist(const CBitcoinAddress& address, const std::vector<CPubKey>& pubKeys, 
  		const std::unique_ptr<CPubKey>& kycPubKey, const uint8_t nMultisig);

	void add_multisig_whitelist(const CBitcoinAddress& address, const std::vector<CPubKey>& pubKeys,
		const uint8_t nMultisig);

  	bool RegisterDecryptedAddresses(const std::vector<unsigned char>& data, const std::unique_ptr<CPubKey>& kycPubKey);

  	bool IsRegisterAddressMulti(const std::vector<unsigned char>::const_iterator start,const std::vector<unsigned char>::const_iterator vend);

  	bool RegisterAddress(const CTransaction& tx, const CBlockIndex* pindex);
  	
	bool RegisterAddress(const CTransaction& tx, const CCoinsViewCache& mapInputs);
	
  	//Update from transaction
  	virtual bool Update(const CTransaction& tx, const CCoinsViewCache& mapInputs);

  	virtual void clear();

  	bool is_whitelisted(const CTxDestination keyId);

  	//Get a kyc key from the _kycUnassignedQueue. Removes the element from the queue.
  	bool get_unassigned_kyc(CPubKey& pubKey);
  	//Get the next key without removing it
  	bool peek_unassigned_kyc(CPubKey& pubKey);
  	//Query the set of unassigned kyc pub keys for the presence of pubKey
  	bool is_unassigned_kyc(const CKeyID& kycKeyID);

  	void add_unassigned_kyc(const CPubKey& pubKey);

  	bool LookupKYCKey(const CTxDestination keyId, CKeyID& kycKeyIdFound);

  	bool LookupKYCKey(const CKeyID& keyId, CPubKey& kycPubkeyFound);

  	bool LookupKYCKey(const CKeyID& keyId, CKeyID& kycKeyIdFound, CPubKey& kycPubKeyFound);

	bool find_kyc_whitelisted(const CKeyID& keyId);

	void blacklist_kyc(const CKeyID& keyId);

	void whitelist_kyc(const CKeyID& keyId, const COutPoint* outPoint=nullptr);

	bool get_kycpubkey_outpoint(const CKeyID& kycPubKeyId, COutPoint& outPoint);

	bool get_kycpubkey_outpoint(const CPubKey& kycPubKey, COutPoint& outPoint);

	// My ending addresses - added to whitelist by me in a add to whitelist transaction waiting to be included in a block
	void add_my_pending(const CTxDestination keyId);

	void remove_my_pending(const CTxDestination keyId);

	bool is_my_pending(const CTxDestination keyId);

	unsigned int n_my_pending();

	bool kycFromUserOnboard(const CPubKey& userOnboard, CPubKey& kyc);

	int64_t n_kyc_pubkeys() const{
        return _kycStatusMap.size();
    }

    int64_t n_unassigned_kyc_pubkeys() const{
        return _kycUnassignedSet.size();
    }
  
private:

	//Make add_sorted private because we only want verified derived keys 
	//to be added to the CWhiteList.
	using CPolicyList::add_sorted;

	using CPolicyList::find;
	//A map of address to kycPubKey
	std::map<CTxDestination, CKeyID> _kycMap;
	//A map of address to tweaked public key
	std::map<CKeyID, CPubKey> _tweakedPubKeyMap;
	//Whitelisted KYC keys
	std::map<CKeyID, CWhiteList::status> _kycStatusMap;
	//Map user onboard key to KYC pub key
	std::map<CKeyID, CPubKey> _onboardMap;

	//Map KYC key ID to public key
	std::map<CKeyID, CPubKey> _kycPubkeyMap;

	//Map KYC key ID to its latest policy transaction (required for blacklisting)
	std::map<CKeyID, COutPoint> _kycPubkeyOutPointMap;

	//KYC pub keys not yet assigned to any user
	std::queue<CPubKey> _kycUnassignedQueue;
	std::set<CKeyID> _kycUnassignedSet;

	std::stringstream _datastream;

	std::set<CTxDestination> _myPending;

	bool set_kyc_status(const CKeyID& keyId, const CWhiteList::status& status);

	bool find_kyc_status(const CKeyID& keyId, const CWhiteList::status& status);

	// Returns true if if is whitelisted OR blackliosted
	bool find_kyc(const CKeyID& keyId);

	bool find_kyc_blacklisted(const CKeyID& keyId);

	void synchronise(CWhiteList* wl_new);

  	const unsigned int addrSize=20;
  	//The written code behaviour expects nMultisigSize to be of length 1 at the moment. If it is changed in the future the code needs to be adjusted accordingly.
  	const unsigned int nMultisigSize=1;
  	const unsigned int minPayloadSize=2;

  	//Lookup owner (idpubkey) of address
  	bool LookupTweakedPubKey(const CKeyID& keyId, CPubKey& pubKeyFound);
};
