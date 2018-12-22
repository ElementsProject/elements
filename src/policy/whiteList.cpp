// Copyright (c) 2018 The CommerceBlock Developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "whiteList.hpp"
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
  //      throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, string("Invalid Bitcoin address: ") +vstr[0]) ;
  
  std::vector<unsigned char> pubKeyData(ParseHex(key));
  CPubKey pubKey = CPubKey(pubKeyData.begin(), pubKeyData.end());
  if (!pubKey.IsFullyValid())
    throw std::system_error(
			    std::error_code(CPolicyList::Errc::INVALID_ADDRESS_OR_KEY, std::system_category())
			    ,std::string(std::string(__func__) +  ": invalid public key: ") + key);
  //      throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, string("Invalid public key: ") + vstr[1]);
  
  uint256 contract = chainActive.Tip() ? chainActive.Tip()->hashContract : GetContractHash();
  if (!contract.IsNull())
    pubKey.AddTweakToPubKey((unsigned char*)contract.begin());
  CKeyID keyId;
  if (!address.GetKeyID(keyId))
    throw std::system_error(
			    std::error_code(CPolicyList::Errc::INVALID_ADDRESS_OR_KEY, std::system_category()),
			    std::string(__func__) + ": invalid key id");
  //      throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid key id");
  
  if (pubKey.GetID() != keyId)
    throw std::system_error(
			    std::error_code(CPolicyList::Errc::INVALID_ADDRESS_OR_KEY,std::system_category()), 
			    std::string(__func__) + std::string(": invalid key derivation when tweaking key with contract hash for tweaked address: ") 
			    + addressIn + std::string(", public key ") + key );
  //      throw JSONRPCError(RPC_INVALID_KEY_DERIVATION, string("Invalid key derivation when tweaking key with contract hash for tweaked address: ") 
  //		 + vstr[0] + string(", public key ") + vstr[1] );
  

  //insert new address into sorted CWhiteList vector 
  add_sorted(&keyId);
}