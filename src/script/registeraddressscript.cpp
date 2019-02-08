// Copyright (c) 2018 The CommerceBlock Developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

// An ecrypted "register address" transaction script.

#include "registeraddressscript.h"
#include "util.h"
#include "validation.h"

CRegisterAddressScript::CRegisterAddressScript(){
}

CRegisterAddressScript::~CRegisterAddressScript(){
	delete _encryptor;
}

//Encrypt the payload using the public, private key and build the script.
bool CRegisterAddressScript::SetKeys(const CKey* privKey, const CPubKey* pubKey){
	delete _encryptor;
    _encryptor = new CECIES(*privKey, *pubKey);
}

//Encrypt the payload, buid the script and return it.
bool CRegisterAddressScript::Finalize(){
    _encryptor->Encrypt(_encrypted, _payload);
    //Prepend the initialization vector used in the encryption
    ucvec sendData = _encryptor->get_iv();
    sendData.insert(sendData.end(), _encrypted.begin(), _encrypted.end()); 
    CScript script;
    //Assemble the script and return
    (*this)  << OP_REGISTERADDRESS << sendData; 
    return true;
}

bool CRegisterAddressScript::Append(const CPubKey& pubKey){
	uint256 contract = chainActive.Tip() ? chainActive.Tip()->hashContract : GetContractHash();

  	CPubKey tweakedPubKey(pubKey);
    if (!contract.IsNull())
    	
    tweakedPubKey.AddTweakToPubKey((unsigned char*)contract.begin());
    CKeyID keyID=tweakedPubKey.GetID();
    assert(Consensus::CheckValidTweakedAddress(keyID, pubKey));
    
    std::vector<unsigned char> vKeyIDNew = ToByteVector(keyID);
    _payload.insert(_payload.end(), 
                    vKeyIDNew.begin(), 
                    vKeyIDNew.end());

    std::vector<unsigned char> vPubKeyNew = ToByteVector(pubKey);
    _payload.insert(_payload.end(), 
                    vPubKeyNew.begin(), 
                    vPubKeyNew.end());
    return true;
}

bool CRegisterAddressScript::Append(const std::vector<CPubKey>& keys){
    for(CPubKey pubKey : keys){
      Append(pubKey);
    }
    return true;
}

//Get the initialization vector (randomly generated) used in the encryption
ucvec CRegisterAddressScript::GetInitVec(){
	ucvec result;
	if(_encryptor){
		result=_encryptor->get_iv();
	}
	return result;
}

