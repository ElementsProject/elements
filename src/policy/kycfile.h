// Copyright (c) 2018 The CommerceBlock Developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

// A class for read/write for an encrypted KYC file used in the user onboarding process

#pragma once

#include "policy/whitelist.h"
#include "validation.h"
#include "ecies.h"
#include <fstream>
#include "script/onboardingscript.h"

using uc_vec=std::vector<unsigned char>;

class CKYCFile{
	public:
		CKYCFile();
		virtual ~CKYCFile();

		void clear();

		bool read();
		bool read(std::string filename);
		bool write();
		bool write(std::string filename);

		bool close();
		bool open(std::string filename);

		bool initEncryptor(CKey* privKey, CPubKey* pubKey, uc_vec* initVec=nullptr);

		std::vector<CPubKey> getAddressKeys() const {return _addressKeys;}
		const CPubKey* getOnboardPubKey() const {return _onboardPubKey;}
		const CPubKey* getOnboardUserPubKey() const {return _onboardUserPubKey;}
		const uc_vec* getInitVec() const {return _initVec;}

		const std::stringstream& getStream() const {return _decryptedStream;}

		 enum Errc{
   		 	FILE_IO_ERROR,
   		 	INVALID_ADDRESS_OR_KEY,
   		 	WALLET_KEY_ACCESS_ERROR,
   		 	WHITELIST_KEY_ACCESS_ERROR,
   		 	INVALID_PARAMETER,
   		 	ENCRYPTION_ERROR
  		};

	 	bool getOnboardingScript(CScript& script);

	private:
		std::ifstream _file;
		CECIES* _encryptor = nullptr;
		CPubKey* _onboardPubKey = nullptr;
		CPubKey* _onboardUserPubKey = nullptr;
    	uc_vec* _initVec = nullptr;

    	CWhiteList* _whitelist=nullptr;

    	// The user address keys to be whitelisted
    	std::vector<CPubKey> _addressKeys; 

    	std::stringstream _decryptedStream;

    	std::string _filename;
};

std::ostream& operator<<(std::ostream& os, const CKYCFile& fl); 
