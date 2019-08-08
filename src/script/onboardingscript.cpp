// Copyright (c) 2018 The CommerceBlock Developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

// An ecrypted user onboarding transaction script.
// For registering initial addresses to the user.

#include "onboardingscript.h"


COnboardingScript::COnboardingScript(): 
    CRegisterAddressScript(RA_ONBOARDING){
}

COnboardingScript::COnboardingScript(const COnboardingScript* script) : 
	CRegisterAddressScript((CRegisterAddressScript*)script, RA_ONBOARDING){
}

COnboardingScript::~COnboardingScript(){

}

bool COnboardingScript::Finalize(CScript& script, 
                    const CPubKey& onboardPubKey, 
                    const CKey& kycPrivKey){

    if(whitelistType != RA_ONBOARDING)
        return false;
   	_encrypted.clear();
    CECIES_hex encryptor;
    encryptor.Encrypt(_encrypted, _payload, onboardPubKey, kycPrivKey);

    //Onboarding keys    	
    ucvec vPubKeyKYC = ToByteVector(kycPrivKey.GetPubKey());
    ucvec vPubKeyUser = ToByteVector(onboardPubKey);

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

bool COnboardingScript::FinalizeUnencrypted(CScript& script, const CPubKey& kycPubKey){
    if(whitelistType != RA_ONBOARDING)
        return false;

    //Append the key
	ucvec sendData = ToByteVector(kycPubKey);

	//Append the addresses (unencrypted)
    sendData.insert(sendData.end(), _payload.begin(), _payload.end()); 
    script.clear();
    script << OP_REGISTERADDRESS << sendData; 
    return true;
}

	


