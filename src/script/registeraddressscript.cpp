// Copyright (c) 2018 The CommerceBlock Developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

// An ecrypted "register address" transaction script.

#include "registeraddressscript.h"
#include "util.h"

CRegisterAddressScript::CRegisterAddressScript(RegisterAddressType type){
    whitelistType = type;
}

CRegisterAddressScript::CRegisterAddressScript(const CRegisterAddressScript* script, RegisterAddressType type){
    _payload = script->_payload;
    _encrypted = script->_encrypted;
    whitelistType = type;
}

CRegisterAddressScript::~CRegisterAddressScript(){
}

//Encrypt the payload, buid the script and return it.
bool CRegisterAddressScript::Finalize(CScript& script, const CPubKey& ePubKey, const CKey& ePrivKey){
    _encrypted.clear();
    CECIES_hex encryptor;
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
    if(whitelistType != RA_PUBLICKEY && whitelistType != RA_ONBOARDING)
        return false;

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
    if(whitelistType != RA_PUBLICKEY && whitelistType != RA_ONBOARDING)
        return false;

    for(CPubKey pubKey : keys){
      Append(pubKey);
    }
    return true;
}

bool CRegisterAddressScript::Append(const int nMultisig, const CTxDestination keyID, const std::vector<CPubKey>& keys){
    if(whitelistType != RA_MULTISIG)
        return false;

    if (!(Consensus::CheckValidTweakedAddress(keyID, keys, nMultisig)))
        return false;

    CScriptID scriptKey = boost::get<CScriptID>(keyID);
    
    std::string strNMultisig = itostr(nMultisig);
    std::vector<unsigned char> vnMultisigNew(strNMultisig.begin(), strNMultisig.end());
    _payload.insert(_payload.end(), 
                    vnMultisigNew.begin(), 
                    vnMultisigNew.end());

    std::vector<unsigned char> vKeyIDNew = ToByteVector(scriptKey);
    _payload.insert(_payload.end(), 
                    vKeyIDNew.begin(), 
                    vKeyIDNew.end());

    for(int i = 0; i < keys.size(); ++i){
        std::vector<unsigned char> vPubKeyNew = ToByteVector(keys[i]);
        _payload.insert(_payload.end(), 
                vPubKeyNew.begin(), 
                vPubKeyNew.end());
    }
    return true;
}

