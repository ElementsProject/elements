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

		bool initEncryptor();

		std::vector<CPubKey> getAddressKeys() const {return _addressKeys;}
		const CPubKey* getOnboardPubKey() const {return _onboardPubKey;}
		const CPubKey* getOnboardUserPubKey() const {return _onboardUserPubKey;}

		bool parsePubkeyPair(const std::vector<std::string> vstr, const std::string line);
		bool parseContractHash(const std::vector<std::string> vstr, const std::string line);
		void parseMultisig(const std::vector<std::string> vstr, const std::string line);

		const std::stringstream& getStream() const {return _decryptedStream;}

	 	bool getOnboardingScript(CScript& script, bool fBlacklist=false);

	private:
		std::ifstream _file;
		CECIES* _encryptor = nullptr;
		CPubKey* _onboardPubKey = nullptr;
		CPubKey* _onboardUserPubKey = nullptr;
    	
    	CWhiteList* _whitelist=nullptr;

    	// The user address keys to be whitelisted
    	std::vector<CPubKey> _addressKeys; 

    	std::vector<OnboardMultisig> _multisigData;

    	std::stringstream _decryptedStream;

    	std::string _filename;

    	unsigned char _mac_calc[CECIES::MACSIZE];

    	bool _fContractHash = false;
    	bool _fContractHash_parsed = false;
};

std::ostream& operator<<(std::ostream& os, const CKYCFile& fl); 
