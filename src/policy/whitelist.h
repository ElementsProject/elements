// Copyright (c) 2018 The CommerceBlock Developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#pragma once

#include "policylist.h"
#include "wallet/wallet.h"
#include <map>

class CWhiteList : public CPolicyList{
public:
	CWhiteList();
	virtual ~CWhiteList();

	void add_derived(const CBitcoinAddress& address, const CPubKey& pubKey, 
		const CBitcoinAddress* kycAddress);
	void add_derived(const CBitcoinAddress& address, const CPubKey& pubKey);

	void add_derived(const std::string& sAddress, const std::string& sPubKey, 
		const std::string& sKYCAddress);
	void add_derived(const std::string& sAddress, const std::string& sKey);



	void synchronise(CWhiteList* wl_new);

  	bool RegisterAddress(const CTransaction& tx, const CCoinsViewCache& mapInputs);


  	//Lookup owner (idpubkey) of address
  	bool LookupKYCKey(const CKeyID& keyId, CKeyID& kycKeyIdFound);
  	bool LookupTweakedPubKey(const CKeyID& keyId, CPubKey& pubKeyFound);

private:
	//Make add_sorted private because we only want verified derived keys 
	//to be added to the CWhiteList.
	using CPolicyList::add_sorted;

	//A map of address to idPubKey
	std::map<CKeyID, CKeyID> _kycMap;
	std::map<CKeyID, CPubKey> _tweakedPubKeyMap;
};
