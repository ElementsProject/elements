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

	static const int64_t MAX_UNASSIGNED_KYCPUBKEYS=1000;
	static const int64_t MAX_KYCPUBKEY_GAP=MAX_UNASSIGNED_KYCPUBKEYS;


    void init_defaults();
  
	virtual bool Load(CCoinsView *view);

	virtual void add_destination(const CTxDestination& dest);

	virtual void add_derived(const CBitcoinAddress& address, const CPubKey& pubKey, 
		const std::unique_ptr<CPubKey>& kycPubKey);

	virtual void add_derived(const CBitcoinAddress& address, const CPubKey& pubKey);

	virtual void add_derived(const std::string& sAddress, const std::string& sPubKey, 
		const std::string& sKYCPubKey);

	virtual void add_derived(const std::string& sAddress, const std::string& sKey);


	//Multisig whitelisting below
	virtual void add_multisig_whitelist(const std::string& sAddress, const UniValue& sPubKeys, 
  		const std::string& sKYCAddress, const uint8_t nMultisig);

	virtual void add_multisig_whitelist(const std::string& addressIn, const UniValue& sPubKeys, 
		const uint8_t nMultisig);

	virtual void add_multisig_whitelist(const CBitcoinAddress& address, const std::vector<CPubKey>& pubKeys, 
  		const std::unique_ptr<CPubKey>& kycPubKey, const uint8_t nMultisig);

	virtual void add_multisig_whitelist(const CBitcoinAddress& address, const std::vector<CPubKey>& pubKeys,
		const uint8_t nMultisig);

  	bool RegisterDecryptedAddresses(const std::vector<unsigned char>& data, const bool bBlacklist=false);

  	virtual bool IsRegisterAddressMulti(const std::vector<unsigned char>::const_iterator start,const std::vector<unsigned char>::const_iterator vend);

  	virtual bool RegisterAddress(const CTransaction& tx, const CBlockIndex* pindex);
  	
	virtual bool RegisterAddress(const CTransaction& tx, const CCoinsViewCache& mapInputs);
	
	virtual bool RegisterAddress(const std::vector<CTxOut>& vout);

	bool ParseRegisterAddressOutput(const CTxOut& txout, bool fBlacklist);
  

  	//Update from transaction
  	virtual bool Update(const CTransaction& tx, const CCoinsViewCache& mapInputs);

  	virtual void clear();

  	virtual bool is_whitelisted(const CTxDestination keyId);

  	virtual bool get_unassigned_kyc(CPubKey& pubKey);

  	virtual bool peek_unassigned_kyc(CPubKey& pubKey);

  	void dump_unassigned_kyc(std::ofstream& fStream);

	virtual bool LookupKYCKey(const CTxDestination& keyId, CKeyID& kycKeyIdFound){return false;}
  	virtual bool LookupKYCKey(const CTxDestination& keyId, CPubKey& pubKeyFound){return false;}
  	virtual bool LookupKYCKey(const CTxDestination& keyId, CKeyID& kycKeyIdFound, CPubKey& kycPubKeyFound){return false;}


  	virtual bool find_kyc_whitelisted(const CKeyID& keyId){
  		return false;
  	}

	// My ending addresses - added to whitelist by me in a add to whitelist transaction waiting to be included in a block
	virtual void add_my_pending(const CTxDestination keyId);

	virtual void remove_my_pending(const CTxDestination keyId);

	virtual bool is_my_pending(const CTxDestination keyId);

	virtual unsigned int n_my_pending();

    int64_t n_unassigned_kyc_pubkeys() const{
        return _kycUnassignedSet.size();
    }

    //Does nothing for unencrypted whitelist.
    virtual void whitelist_kyc(const CPubKey& pubKey, const COutPoint* outPoint=nullptr){;}

    bool get_kycpubkey_outpoint(const CKeyID& kycPubKeyId, COutPoint& outPoint);

	bool get_kycpubkey_outpoint(const CPubKey& kycPubKey, COutPoint& outPoint);

 	virtual void add_unassigned_kyc(const CPubKey& pubKey){
 		;
 	}

	void sync_whitelist_wallet(std::vector<CPubKey>& keysNotFound);

	void sync_whitelist_wallet();


protected:
	std::set<CTxDestination> _myPending;

	//KYC pub keys not yet assigned to any user
	std::set<CPubKey> _kycUnassignedSet;
	virtual bool remove_unassigned_kyc(const CPubKey& pubKey);
  	virtual bool is_unassigned_kyc(const CPubKey& pubKey);
	//Make add_sorted private because we only want verified derived keys 
	//to be added to the CWhiteList.
	using CPolicyList::add_sorted;

	using CPolicyList::find;

  	const unsigned int addrSize=20;
  	//The written code behaviour expects nMultisigSize to be of length 1 at the moment. If it is changed in the future the code needs to be adjusted accordingly.
  	const unsigned int nMultisigSize=1;
  	const unsigned int minPayloadSize=2;

    std::map<CKeyID, COutPoint> _kycPubkeyOutPointMap;



private:
	void add_unassigned_kyc(const CPubKey& pubKey, const COutPoint& outPoint);
};
