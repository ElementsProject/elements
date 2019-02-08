// Copyright (c) 2018 The CommerceBlock Developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

// An ecrypted "register address" transaction script.

#pragma once
#include "script.h"
#include "ecies.h"

using ucvec=std::vector<unsigned char>;

class CRegisterAddressScript : public CScript{
public:
	CRegisterAddressScript();
	virtual ~CRegisterAddressScript();

	//Encrypt the payload using the public, private key and build the script.
	bool SetKeys(const CKey* privKey, const CPubKey* pubKey);
	bool Finalize();
	bool Append(const CPubKey& key);
	bool Append(const std::vector<CPubKey>& keys);
	//Get the initialization vector (randomly generated) used in the encryption
	ucvec GetInitVec();
	void Clear(){_payload.clear(); _encrypted.clear();}

private:
	CECIES* _encryptor = nullptr;
	CKey* _privKey;
	CPubKey* _pubKey;
	ucvec _payload;
	ucvec _encrypted;
};