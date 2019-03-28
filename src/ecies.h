// Copyright (c) 2018 The CommerceBlock Developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

//An implementation of ECIES AES256CBC Encryption

#ifndef OCEAN_ECIES_H
#define OCEAN_ECIES_H

#include "key.h"
#include "crypto/aes.h"

typedef std::vector<unsigned char> uCharVec;

class CECIES{
public:
	CECIES();
	~CECIES();
	
	/**
    * Encrypt/decrypt a message string.
    */

	bool Encrypt(uCharVec& em, 
   	const uCharVec& m, const CPubKey& pubKey);
   	//Use a defined priv key instead of an ephemeral one.
   	bool Encrypt(uCharVec& em, 
   	const uCharVec& m, const CPubKey& pubKey, const CKey& privKey);
    bool Decrypt(uCharVec& m, 
    	const uCharVec& em, const CKey& privKey, const CPubKey& pubKey);
    bool Decrypt(uCharVec& m, 
    	const uCharVec& em, const CKey& privKey);
    bool Encrypt(std::string& em, 
    	const std::string& m, const CPubKey& pubKey);
    bool Decrypt(std::string& m, 
    	const std::string& em, const CKey& privKey);

	bool OK(){return _bOK;}

private:

	unsigned char _k_mac_encrypt[AES256_KEYSIZE];
	unsigned char _k_mac_decrypt[AES256_KEYSIZE];


	bool CheckMagic(const uCharVec& encryptedMessage) const;

	bool _bOK = false;

	void check(const CKey& privKey, const CPubKey& pubKey);

	//Use the electrum wallet default "magic" string
	const uCharVec _magic{'B','I','E','1'};
};

#endif //#ifndef OCEAN_ECIES_H
