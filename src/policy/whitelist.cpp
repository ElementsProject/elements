// Copyright (c) 2018 The CommerceBlock Developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "whitelist.h"
#include "validation.h"

CWhiteList::CWhiteList(){;}
CWhiteList::~CWhiteList(){;}

void CWhiteList::add_derived(std::string addressIn, std::string key){
   boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  CBitcoinAddress address;
  if (!address.SetString(addressIn))
    throw std::system_error(
			    std::error_code(CPolicyList::Errc::INVALID_ADDRESS_OR_KEY,
					    std::system_category()),
			    std::string(std::string(__func__) + ": invalid Bitcoin address: ") + addressIn);

  std::vector<unsigned char> pubKeyData(ParseHex(key));
  CPubKey pubKey = CPubKey(pubKeyData.begin(), pubKeyData.end());
  if (!pubKey.IsFullyValid())
    throw std::system_error(
			    std::error_code(CPolicyList::Errc::INVALID_ADDRESS_OR_KEY, std::system_category())
			    ,std::string(std::string(__func__) +  ": invalid public key: ") + key);

  uint256 contract = chainActive.Tip() ? chainActive.Tip()->hashContract : GetContractHash();
  if (!contract.IsNull())
    pubKey.AddTweakToPubKey((unsigned char*)contract.begin());
  CKeyID keyId;
  if (!address.GetKeyID(keyId))
    throw std::system_error(
			    std::error_code(CPolicyList::Errc::INVALID_ADDRESS_OR_KEY, std::system_category()),
			    std::string(__func__) + ": invalid key id");

  if (pubKey.GetID() != keyId)
    throw std::system_error(
			    std::error_code(CPolicyList::Errc::INVALID_ADDRESS_OR_KEY,std::system_category()),
			    std::string(__func__) + std::string(": invalid key derivation when tweaking key with contract hash for tweaked address: ")
			    + addressIn + std::string(", public key ") + key );

  //insert new address into sorted CWhiteList vector
  add_sorted(&keyId);
}

