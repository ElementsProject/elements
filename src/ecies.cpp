// Copyright (c) 2018 The CommerceBlock Developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

//A wrapper class for AES256CBCEncryption

#include "ecies.h"
#include "crypto/aes.h"
#include "random.h"
#include <sstream>
#include <iostream>


CECIES::CECIES(){
	//Generate a random initialization vector.
    GetStrongRandBytes(_iv, AES_BLOCKSIZE);
    //Generate a random key.
    GetStrongRandBytes(_k, AES256_KEYSIZE);
    Initialize();
}

//This sets up an encryption scheme based on a private key from one key pair
//and public key from another key pair. A shared secret _k is generated which is
//used to enrypt/decrypt messages.
CECIES::CECIES(const CKey& privKey, const CPubKey& pubKey, const uCharVec iv){
	//Generate the ECDH exchange shared secret from the private key and the public key
  check(privKey,pubKey, iv);
	uint256 k = privKey.ECDH(pubKey);
	memcpy(_k, &k, 32);
	set_iv(iv);
	unsigned char tmp[AES_BLOCKSIZE];
	GetStrongRandBytes(tmp, AES_BLOCKSIZE);
	//std::stringstream ss;
	//	ss << 
	//" Shared secret: " << _k << 
	//" iv: " << _iv << std::endl;
	Initialize();
}

CECIES::CECIES(const CKey& privKey, const CPubKey& pubKey){
  //Generate the ECDH exchange shared secret from the private key and the public key
  check(privKey,pubKey);
  uint256 k = privKey.ECDH(pubKey);
  memcpy(_k, &k, 32);
  //Randomly generate a initialization vector.
  GetStrongRandBytes(_iv, AES_BLOCKSIZE);
  //  std::stringstream ss;
  //  ss << 
//	"Priv key: " << privKey.GetPrivKey().ToString() <<
//	" Pub key: " << pubKey << 
//  " Shared secret: " << _k << 
//  " iv: " << _iv << std::endl;
  Initialize();
}

void CECIES::check(const CKey& privKey, const CPubKey& pubKey){
  _bOK=false;
  if(!privKey.GetPubKey().IsFullyValid()) return;
  if(!pubKey.IsFullyValid()) return;
  _bOK=true;
}

void CECIES::check(const CKey& privKey, const CPubKey& pubKey, const uCharVec iv){
 check(privKey, pubKey);
 if(_bOK){
 	_bOK=false;
	 if(iv.size()==AES_BLOCKSIZE) _bOK=true;
	}
}

CECIES::~CECIES(){
	delete _encryptor;
	delete _decryptor;
}

bool CECIES::set_iv(uCharVec iv){
	std::copy(iv.begin(), iv.begin() + AES_BLOCKSIZE, _iv);
	return true;
}

//Initialize from serialized private key 
bool CECIES::Initialize(){
	_decryptor=new AES256CBCDecrypt(_k, _iv, true);
	_encryptor=new AES256CBCEncrypt(_k, _iv, true);
	return true;
}

bool CECIES::Encrypt(uCharVec& em, 
 	const uCharVec& m) const{
	//Add padding if needed.
	//unsigned int size = m.size();
	//if (size % AES_BLOCKSIZE) {
	//	m.resize(AES_BLOCKSIZE*(size/AES_BLOCKSIZE +1), _padChar);
//	}
//	em.resize(m.size(), _padChar);
	int size=m.size();
	em.resize(size+AES_BLOCKSIZE);
	int paddedSize=_encryptor->Encrypt(m.data(), size, em.data());
	em.resize(paddedSize);
    return true;
}

bool CECIES::Decrypt(uCharVec& m, 
 	const uCharVec& em) const{
	//Add padding if needed.
//	unsigned int size = em.size();
//	if (size % AES_BLOCKSIZE) {
//		em.resize(AES_BLOCKSIZE*(size/AES_BLOCKSIZE +1), _padChar);
//	}
//	m.resize(em.size(), _padChar);
	int paddedSize = em.size();
	m.resize(paddedSize);
	int size=_decryptor->Decrypt(em.data(), paddedSize, m.data());
	//Remove the padding.
	m.resize(size);
    return true;
}

bool CECIES::Encrypt(std::string& em, 
 	const std::string& m) const{
	uCharVec vm(m.begin(), m.end());
	uCharVec vem;
	bool bResult=Encrypt(vem, vm);
	if(bResult) em=std::string(vem.begin(), vem.end());
    return bResult;
}

bool CECIES::Decrypt(std::string& m, 
 	const std::string& em) const{
	uCharVec vem(em.begin(), em.end());
	uCharVec vm;
	bool bResult=Decrypt(vm, vem);
	if (bResult) m=std::string(vm.begin(), vm.end());
    return bResult;
}

uCharVec CECIES::get_iv(){
	uCharVec retval(_iv, _iv+AES_BLOCKSIZE);
	return retval;
}

bool CECIES::Test1(){
	Initialize();
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


