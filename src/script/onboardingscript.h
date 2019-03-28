// Copyright (c) 2018 The CommerceBlock Developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

// An ecrypted user onboarding transaction script.
// For registering initial addresses to the user.

#pragma once

#include "registeraddressscript.h"


class COnboardingScript : public CRegisterAddressScript{
public:
	COnboardingScript();
	COnboardingScript(const COnboardingScript* script);
 
	virtual ~COnboardingScript();

	virtual bool Finalize(CScript& script, const CPubKey& onboardPubKey,
		const CKey& kycPrivKey);
	virtual bool FinalizeUnencrypted(CScript& script);

	bool SetOnboardingKeyKYC(const CPubKey& key);
	bool SetOnboardingKeyUser(const CPubKey& key);

private:
	CPubKey _kycPubKey;
	CPubKey _userPubKey;
};