//This class is a wrapper for the Crypto++ ECIES class for
//ECIES encryption/decryption

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
    	uCharVec& m) const;
    bool Decrypt(uCharVec& m, 
    	uCharVec& em) const;
    bool Encrypt(std::string& em, 
    	std::string& m) const;
    bool Decrypt(std::string& m, 
    	std::string& em) const;

    bool Test1();

	uCharVec get_iv();
	bool set_iv(uCharVec iv);

private:
	unsigned char _iv[AES_BLOCKSIZE];
	unsigned char _k[AES256_KEYSIZE];

	AES256CBCEncrypt* _encryptor;
	AES256CBCDecrypt* _decryptor;

	bool Initialize();

};