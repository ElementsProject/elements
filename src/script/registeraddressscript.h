// Copyright (c) 2018 The CommerceBlock Developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

// An ecrypted "register address" transaction script.

#pragma once
#include "script.h"
#include "ecies.h"
#include "validation.h"

using ucvec=std::vector<unsigned char>;

class CRegisterAddressScript {
public:
	CRegisterAddressScript();
	CRegisterAddressScript(const CRegisterAddressScript* script);
	virtual ~CRegisterAddressScript();

	//Encrypt the payload using the public, private key and build the script.
	virtual bool SetKeys(const CKey* privKey, const CPubKey* pubKey);
	virtual bool Finalize(CScript& script);
	virtual bool FinalizeUnencrypted(CScript& script);
	bool Append(const CPubKey& key);
	bool Append(const std::vector<CPubKey>& keys);
	//Get the initialization vector (randomly generated) used in the encryption
	ucvec GetInitVec();
	virtual void clear(){_payload.clear(); _encrypted.clear(); ((CScript*)this)->clear();}

protected:
	CECIES* _encryptor = nullptr;
	ucvec _payload;
	ucvec _encrypted;
};