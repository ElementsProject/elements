// Copyright (c) 2018 The CommerceBlock Developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

// An ecrypted user onboarding transaction script.
// For registering initial addresses to the user.

#include "onboardingscript.h"


COnboardingScript::COnboardingScript(){

}

COnboardingScript::COnboardingScript(const COnboardingScript* script) : 
	CRegisterAddressScript((CRegisterAddressScript*)script){
	_kycPubKey=script->_kycPubKey;
	_userPubKey=script->_userPubKey;
}

COnboardingScript::~COnboardingScript(){

}

//bool COnboardingScript::SetKeys(const CKey* privKey, const CPubKey* pubKey){
//    CRegisterAddressScript::SetKeys(privKey, pubKey);
//    _kycPubKey=privKey->GetPubKey();
//    _userPubKey=*pubKey;
//    return true;
//}

bool COnboardingScript::Finalize(CScript& script, 
                    const CPubKey& onboardPubKey, 
                    const CKey& kycPrivKey){

   	_encrypted.clear();
    CECIES encryptor;
    encryptor.Encrypt(_encrypted, _payload, onboardPubKey, kycPrivKey);

    //Onboarding keys    	
    ucvec vPubKeyKYC = ToByteVector(kycPrivKey.GetPubKey());
    _payload.insert(_payload.end(), 
                    vPubKeyKYC.begin(), 
                    vPubKeyKYC.end());

    ucvec vPubKeyUser = ToByteVector(onboardPubKey);
    _payload.insert(_payload.end(), 
                    vPubKeyUser.begin(), 
                    vPubKeyUser.end());

    //Append the keys
	ucvec sendData = vPubKeyKYC;
	sendData.insert(sendData.end(), vPubKeyUser.begin(), vPubKeyUser.end());

	//Append the encrypted addresses
    sendData.insert(sendData.end(), _encrypted.begin(), _encrypted.end()); 

    //Assemble the script and return
    script.clear();
    script << OP_REGISTERADDRESS << sendData; 
    return true;
}

bool COnboardingScript::FinalizeUnencrypted(CScript& script){
  	 //Onboarding keys    	
    ucvec vPubKeyKYC = ToByteVector(_kycPubKey);
    _payload.insert(_payload.end(), 
                    vPubKeyKYC.begin(), 
                    vPubKeyKYC.end());

    ucvec vPubKeyUser = ToByteVector(_userPubKey);
    _payload.insert(_payload.end(), 
                    vPubKeyUser.begin(), 
                    vPubKeyUser.end());

    //Append the keys
	ucvec sendData = vPubKeyKYC;
	sendData.insert(sendData.end(), vPubKeyUser.begin(), vPubKeyUser.end());

	//Append dummy IV
	ucvec dummy_iv;
	dummy_iv.resize(AES_BLOCKSIZE);
	sendData.insert(sendData.end(), dummy_iv.begin(), dummy_iv.end());

	//Append the addresses (unencrypted)
    sendData.insert(sendData.end(), _payload.begin(), _payload.end()); 
    script.clear();
    script << OP_REGISTERADDRESS << sendData; 
    return true;
}

	


