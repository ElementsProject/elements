// Copyright (c) 2018 The CommerceBlock Developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

//A wrapper class for AES256CBCEncryption

#include "ecies.h"
#include "crypto/aes.h"
#include "random.h"
#include <sstream>
#include <iostream>


//This sets up an encryption scheme based on a private key from one key pair
//and public key from another key pair. A shared secret _k is generated which is
//used to enrypt/decrypt messages.
CECIES::CECIES(const CKey& privKey, const CPubKey& pubKey, const uCharVec& iv){
	//Generate the ECDH exchange shared secret from the private key and the public key
	_bOK=true;
	if(!privKey.GetPubKey().IsFullyValid()) _bOK=false;
	if(!pubKey.IsFullyValid()) _bOK=false;
	if(!_bOK) return;

	uint256 k = privKey.ECDH(pubKey);
	unsigned char kArr[AES256_KEYSIZE];
	memcpy(kArr, &k, AES256_KEYSIZE);
	_k=uCharVec(kArr, std::end(kArr));
	_iv=uCharVec(iv.begin(), iv.end());
	_decryptor = new AES256CBCDecrypt(&_k[0], &_iv[0], true);
	_encryptor = new AES256CBCEncrypt(&_k[0], &_iv[0], true);
}

CECIES::CECIES(const CKey& privKey, const CPubKey& pubKey){
	_bOK=true;
	//Randomly generate a initialization vector.
	unsigned char iv[AES_BLOCKSIZE];
    GetStrongRandBytes(iv, AES_BLOCKSIZE);
    uCharVec viv(iv, iv + AES_BLOCKSIZE);
	CECIES(privKey, pubKey, viv);
}

CECIES::~CECIES(){
	delete _encryptor;
	delete _decryptor;
}

bool CECIES::OK() const{
	return _bOK;
}

bool CECIES::Encrypt(uCharVec& em, 
 	uCharVec& m) const{
	//Add padding if needed.
	unsigned int size = m.size();
	if (size % AES_BLOCKSIZE) {
		m.resize(AES_BLOCKSIZE*(size/AES_BLOCKSIZE +1), _padChar);
	}
	em.resize(m.size(), _padChar);
	_encryptor->Encrypt(m.data(), m.size(), em.data());
    return true;
}

bool CECIES::Decrypt(uCharVec& m, 
 	uCharVec& em) const{
		//Add padding if needed.
	unsigned int size = em.size();
	if (size % AES_BLOCKSIZE) {
		em.resize(AES_BLOCKSIZE*(size/AES_BLOCKSIZE +1), _padChar);
	}
	m.resize(em.size(), _padChar);
	_decryptor->Decrypt(em.data(), em.size(), m.data());
	//Remove the padding.
	m.resize(size);
    return true;
}

bool CECIES::Encrypt(std::string& em, 
 	std::string& m) const{
	uCharVec vm(m.begin(), m.end());
	uCharVec vem;
	bool bResult=Encrypt(vem, vm);
	if(bResult) em=std::string(vem.begin(), vem.end());
    return bResult;
}

bool CECIES::Decrypt(std::string& m, 
 	std::string& em) const{
	uCharVec vem(em.begin(), em.end());
	uCharVec vm;
	bool bResult=Decrypt(vm, vem);
	if (bResult) m=std::string(vm.begin(), vm.end());
    return bResult;
}


bool CECIES::Test1(){
	std::string spm = "Test message for ECIES.";
	std::vector<unsigned char> pm(spm.begin(), spm.end());
	std::vector<unsigned char> em;
	std::vector<unsigned char> dm;
	std::cout << spm << std::endl;
	//EncryptMessage(em, pm);
	std::cout << std::string(em.begin(), em.end()) << std::endl;
//	DecryptMessage(dm, em);
	std::cout << std::string(dm.begin(), dm.end()) << std::endl;
	return true;
}


