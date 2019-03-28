// Copyright (c) 2018 The CommerceBlock Developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

// An ecrypted "register address" transaction script.

#include "registeraddressscript.h"
#include "util.h"

CRegisterAddressScript::CRegisterAddressScript(){
}

CRegisterAddressScript::CRegisterAddressScript(const CRegisterAddressScript* script){
    _payload = script->_payload;
    _encrypted = script->_encrypted;
}

CRegisterAddressScript::~CRegisterAddressScript(){
}

//Encrypt the payload, buid the script and return it.
bool CRegisterAddressScript::Finalize(CScript& script, const CPubKey& ePubKey, const CKey& ePrivKey){
    _encrypted.clear();
    CECIES encryptor;
    encryptor.Encrypt(_encrypted, _payload, ePubKey, ePrivKey);
//    _encrypted.insert(_encrypted.begin(),_payload.begin(), _payload.end());
    //Prepend the initialization vector used in the encryption
    ucvec sendData;
    sendData.insert(sendData.end(), _encrypted.begin(), _encrypted.end()); 
    //Assemble the script and return
    script.clear();
    script << OP_REGISTERADDRESS << sendData; 
    return true;
}

bool CRegisterAddressScript::FinalizeUnencrypted(CScript& script){
    ucvec sendData;
    sendData.resize(AES_BLOCKSIZE);
    sendData.insert(sendData.end(), _payload.begin(), _payload.end()); 
    script.clear();
    script << OP_REGISTERADDRESS << sendData; 
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

