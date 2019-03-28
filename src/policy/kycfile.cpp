// Copyright (c) 2018 The CommerceBlock Developers
// Distributed under the MIT software license, see the accompanying                                                                             
// file COPYING or http://www.opensource.org/licenses/mit-license.php.  

#include "kycfile.h"
#include <boost/algorithm/string.hpp>

CKYCFile::CKYCFile(){

}

CKYCFile::~CKYCFile(){
    clear();
}

void CKYCFile::clear(){
    _addressKeys.clear();
    _decryptedStream.clear();
    delete _onboardPubKey;
    delete _onboardUserPubKey;
}

bool CKYCFile::close(){
    _file.close();
    return (_file.is_open() == false);
}

bool CKYCFile::open(std::string filename){
    close();
    _file.open(filename, std::ios::in | std::ios::ate);
    if (!_file.is_open())
        throw std::system_error(
          std::error_code(CKYCFile::Errc::FILE_IO_ERROR, std::system_category()),
          std::string(std::string(__func__) +  ": cannot open kyc file"));

    _file.seekg(0, _file.beg);
    return true;
}

bool CKYCFile::read(std::string filename){
    open(filename);
    return read();
}

bool CKYCFile::read(){
    clear();

    // parse file to extract bitcoin address - untweaked pubkey pairs and validate derivation

    std::stringstream ss;
    ss.str("");
    unsigned long nBytesToRead=0;
    std::string encryptedData("");
    std::string data("");

    clear();

    CKey onboardPrivKey;   

    CECIES encryptor;

    while (_file.good()){
        //Skip the header, footer
        std::string line;
        std::getline(_file, line);
        if(ss.str().size() >= nBytesToRead){
           if (line.empty() || line[0] == '#'){
                _decryptedStream << line << "\n";
                continue;
            }
        }

        //Read the metadata and initialize the decryptor
        if(!_onboardUserPubKey){
            _decryptedStream << line << "\n";
            std::vector<std::string> vstr;
            boost::split(vstr, line, boost::is_any_of(" "));
            if (vstr.size() != 3)
                throw std::system_error(
                    std::error_code(CKYCFile::Errc::FILE_IO_ERROR, std::system_category()),
                    std::string(std::string(__func__) +  ": invalid KYC file"));

            std::vector<unsigned char> pubKeyData(ParseHex(vstr[0]));      
            _onboardPubKey = new CPubKey(pubKeyData.begin(), pubKeyData.end());

            if(!_onboardPubKey->IsFullyValid())
                        throw std::system_error(
                        std::error_code(CKYCFile::Errc::INVALID_ADDRESS_OR_KEY, std::system_category()),
                        std::string(std::string(__func__) +  ": invalid kyc pub key in KYC file"));

            if(!pwalletMain->GetKey(_onboardPubKey->GetID(), onboardPrivKey))
                throw std::system_error(
                        std::error_code(CKYCFile::Errc::WALLET_KEY_ACCESS_ERROR, std::system_category()),
                        std::string(std::string(__func__) +  ": cannot get onboard private key"));
  
            std::vector<unsigned char> userPubKeyData(ParseHex(vstr[1]));    
            _onboardUserPubKey = new CPubKey(userPubKeyData.begin(), userPubKeyData.end());
            if(!_onboardUserPubKey->IsFullyValid())
                 throw std::system_error(
                        std::error_code(CKYCFile::Errc::INVALID_ADDRESS_OR_KEY, std::system_category()),
                        std::string(std::string(__func__) +  ": invalid onboard user pub key in kyc file"));

            std::stringstream ssNBytes;
            ssNBytes << vstr[2];
            ssNBytes >> nBytesToRead;
            continue;
        }

        //Read in encrypted data, decrypt and output to file
        ss << line;        
        unsigned long size = ss.str().size();
        if(size > nBytesToRead){
            throw std::system_error(
            std::error_code(CKYCFile::Errc::FILE_IO_ERROR, std::system_category()),
            std::string(std::string(__func__) +  ": invalid KYC file: encrypted data stream too long"));
        }
        if(size == nBytesToRead){
            if(data.size()==0){
                std::string str=ss.str();
                std::vector<unsigned char> vch(str.begin(), str.end());
                std::vector<unsigned char> vdata;
                if(!encryptor.Decrypt(vdata, vch, onboardPrivKey))
                    throw std::system_error(
                        std::error_code(CKYCFile::Errc::ENCRYPTION_ERROR, std::system_category()),
                        std::string(std::string(__func__) +  ": KYC file decryption failed"));
        
                std::string data(vdata.begin(), vdata.end());
                std::stringstream ss_data;
                ss_data << data;
                //Get the addresses
                for(std::string line; std::getline(ss_data, line);){
                    std::vector<std::string> vstr;
                    if (line.empty() || line[0] == '#'){
                        _decryptedStream << line << "\n";
                        continue;
                    }
                    boost::split(vstr, line, boost::is_any_of(" "));
                    if (vstr.size() != 2){
                        continue;
                    }

                    CBitcoinAddress address;
                    if (!address.SetString(vstr[0])) {
                        continue;
                    }

                    std::vector<unsigned char> pubKeyData(ParseHex(vstr[1]));
                    CPubKey pubKey = CPubKey(pubKeyData.begin(), pubKeyData.end());
                    if(!pubKey.IsFullyValid()){
                        _decryptedStream << line << ": invalid public key\n";
                        //throw
                        // std::system_error(
                        //std::error_code(CKYCFile::Errc::INVALID_ADDRESS_OR_KEY, std::system_category()),
                        //std::string(std::string(__func__) +  ": invalid pub key in KYC file"));
                       continue;
                    }

                    //Addresses valid, write to map
                    _addressKeys.push_back(pubKey);
                    _decryptedStream << line << "\n";
                }
            }
        }
    }
    if(ss.str().size() < nBytesToRead){
         throw std::system_error(
                        std::error_code(CKYCFile::Errc::FILE_IO_ERROR, std::system_category()),
                        std::string(std::string(__func__) +  ": invalid KYC file: encrypted data stream too short"));
    }
    return true;
}

 bool CKYCFile::getOnboardingScript(CScript& script){
    COnboardingScript obScript;

    // Lookup the KYC public key assigned to the user from the whitelist
    //addressWhiteList.

    if (!pwalletMain->IsLocked())
        pwalletMain->TopUpKeyPool();

    // Get an unassigned KYC key from the addressWhitelist
    CPubKey kycPubKey;
    if(!addressWhitelist.get_unassigned_kyc(kycPubKey))
        throw std::system_error(
        std::error_code(CKYCFile::Errc::WHITELIST_KEY_ACCESS_ERROR, std::system_category()),
        std::string(std::string(__func__) +  ": no unassigned whitelist KYC keys available"));

    CKeyID kycKeyID(kycPubKey.GetID());
    // Look up the public key
    CKey kycKey;
    if(!pwalletMain->GetKey(kycKeyID, kycKey)){
        addressWhitelist.add_unassigned_kyc(kycPubKey);
        throw std::system_error(
        std::error_code(CKYCFile::Errc::WALLET_KEY_ACCESS_ERROR, std::system_category()),
        std::string(std::string(__func__) +  ": cannot get KYC private key from wallet"));
    }

    if(!obScript.Append(_addressKeys)) return false;
    if(!obScript.Finalize(script, *_onboardUserPubKey, kycKey)) return false;
    return true;
}

std::ostream& operator<<(std::ostream& os, const CKYCFile& fl){
    os << fl.getStream().str();
    return os; 
}


