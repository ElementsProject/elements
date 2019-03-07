// Copyright (c) 2018 The CommerceBlock Developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

//A wrapper class for AES256CBCEncryption

#pragma once

#include "key.h"
#include "crypto/aes.h"

typedef std::vector<unsigned char> uCharVec;

class CECIES{
public:
	CECIES();
	CECIES(const CKey& privKey, const CPubKey& pubKey,  const uCharVec iv);
	CECIES(const CKey& privKey, const CPubKey& pubKey);

	~CECIES();
	
	/**
    * Encrypt/decrypt a message string.
    */

    bool Encrypt(uCharVec& em, 
    	const uCharVec& m) const;
    bool Decrypt(uCharVec& m, 
    	const uCharVec& em) const;
    bool Encrypt(std::string& em, 
    	const std::string& m) const;
    bool Decrypt(std::string& m, 
    	const std::string& em) const;

    bool Test1();

	uCharVec get_iv();
	bool set_iv(uCharVec iv);

	bool OK(){return _bOK;}

private:
	unsigned char _iv[AES_BLOCKSIZE];
	unsigned char _k[AES256_KEYSIZE];

	unsigned char _padChar=0;

	AES256CBCEncrypt* _encryptor;
	AES256CBCDecrypt* _decryptor;

	bool Initialize();

	bool _bOK = false;

	void check(const CKey& privKey, const CPubKey& pubKey);
	void check(const CKey& privKey, const CPubKey& pubKey, const uCharVec iv);

};
