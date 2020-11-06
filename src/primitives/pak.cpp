// Copyright (c) 2018-2018 The Elements developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <primitives/pak.h>
#include <pubkey.h>

// ELEMENTS

// PAK entries loaded by config file entries
// These will be embedded into coinbase transaction
//  during block creation and tested against during
//  testproposedblock
boost::optional<CPAKList> g_paklist_config;
// PAK entries loaded from latest coinbase pak commitment
CPAKList g_paklist_blockchain;

 ///////////

namespace {

static secp256k1_context *secp256k1_ctx_pak;

class CSecp256k1Init {
public:
    CSecp256k1Init() {
        secp256k1_ctx_pak = secp256k1_context_create(SECP256K1_CONTEXT_VERIFY);
    }
    ~CSecp256k1Init() {
        secp256k1_context_destroy(secp256k1_ctx_pak);
    }
};
static CSecp256k1Init instance_of_csecp256k1;
}

CScript CPAKList::Magic()
{
    CScript scriptPubKey;
    scriptPubKey.resize(6);
    scriptPubKey[0] = OP_RETURN;
    scriptPubKey[1] = 0x04;
    scriptPubKey[2] = 0xab;
    scriptPubKey[3] = 0x22;
    scriptPubKey[4] = 0xaa;
    scriptPubKey[5] = 0xee;
    return scriptPubKey;
}

std::vector<CScript> CPAKList::GenerateCoinbasePAKCommitments() const
{
    std::vector<CScript> commitments;
    CScript scriptPubKey = CPAKList::Magic();

    for (unsigned int i = 0; i < m_offline_keys.size(); i++) {
        CScript scriptCommitment(scriptPubKey);
        unsigned char pubkey[33];
        size_t outputlen = 33;
        secp256k1_ec_pubkey_serialize(secp256k1_ctx_pak, pubkey, &outputlen, &m_offline_keys[i], SECP256K1_EC_COMPRESSED);
        assert(outputlen == 33);
        scriptCommitment << std::vector<unsigned char>(pubkey, pubkey+outputlen);
        secp256k1_ec_pubkey_serialize(secp256k1_ctx_pak, pubkey, &outputlen, &m_online_keys[i], SECP256K1_EC_COMPRESSED);
        assert(outputlen == 33);
        scriptCommitment << std::vector<unsigned char>(pubkey, pubkey+outputlen);
        commitments.push_back(scriptCommitment);
    }

    return commitments;
}

std::vector<CScript> CPAKList::GenerateCoinbasePAKReject() const
{
    CScript scriptPubKey = CPAKList::Magic();

    std::vector<unsigned char> reject;
    reject.push_back('R');
    reject.push_back('E');
    reject.push_back('J');
    reject.push_back('E');
    reject.push_back('C');
    reject.push_back('T');

    scriptPubKey << reject;

    std::vector<CScript> commitment;
    commitment.push_back(scriptPubKey);
    return commitment;
}

void CPAKList::CreateCommitments(std::vector<CScript> &commitments) const
{
    if(reject) {
        commitments = GenerateCoinbasePAKReject();
    } else {
        commitments = GenerateCoinbasePAKCommitments();
    }
}

bool CPAKList::operator==(const CPAKList &other) const
{
    if (this->reject != other.reject) {
        return false;
    } else if (this->m_offline_keys.size() != other.m_offline_keys.size()) {
        return false;
    } else {
        for (unsigned int i = 0; i < this->m_offline_keys.size(); i++) {
            if (memcmp(&this->m_offline_keys[i], &other.m_offline_keys[i], sizeof(secp256k1_pubkey)) != 0 ||
                    memcmp(&this->m_online_keys[i], &other.m_online_keys[i], sizeof(secp256k1_pubkey)) != 0) {
                return false;
            }
        }
    }
    return true;
}

bool CPAKList::FromBytes(CPAKList &paklist, std::vector<std::vector<unsigned char> >& offline_keys_bytes, std::vector<std::vector<unsigned char> >& online_keys_bytes, bool is_reject)
{
    if(offline_keys_bytes.size() != online_keys_bytes.size()
        || offline_keys_bytes.size() > SECP256K1_WHITELIST_MAX_N_KEYS) {
        return false;
    }

    std::vector<secp256k1_pubkey> offline_keys;
    std::vector<secp256k1_pubkey> online_keys;
    for (unsigned int i = 0; i < offline_keys_bytes.size(); i++) {
        secp256k1_pubkey pubkey1;
        secp256k1_pubkey pubkey2;
        int ret1 = secp256k1_ec_pubkey_parse(secp256k1_ctx_pak, &pubkey1, &offline_keys_bytes[i][0], offline_keys_bytes[i].size());
        int ret2 = secp256k1_ec_pubkey_parse(secp256k1_ctx_pak, &pubkey2, &online_keys_bytes[i][0], online_keys_bytes[i].size());

        if (ret1 != 1 || ret2 != 1) {
            return false;
        }
        offline_keys.push_back(pubkey1);
        online_keys.push_back(pubkey2);
    }

    paklist = CPAKList(offline_keys, online_keys, is_reject);
    return true;
}

void CPAKList::ToBytes(std::vector<std::vector<unsigned char> >& offline_keys, std::vector<std::vector<unsigned char> >& online_keys, bool &is_reject) const
{
    offline_keys.resize(0);
    online_keys.resize(0);

    for (unsigned int i = 0; i < m_offline_keys.size(); i++) {
        unsigned char pubkey[33];
        size_t outputlen = 33;
        secp256k1_ec_pubkey_serialize(secp256k1_ctx_pak, pubkey, &outputlen, &m_offline_keys[i], SECP256K1_EC_COMPRESSED);
        offline_keys.push_back(std::vector<unsigned char>(pubkey, pubkey+outputlen));
        secp256k1_ec_pubkey_serialize(secp256k1_ctx_pak, pubkey, &outputlen, &m_online_keys[i], SECP256K1_EC_COMPRESSED);
        online_keys.push_back(std::vector<unsigned char>(pubkey, pubkey+outputlen));
    }
    is_reject = reject;
}

// Proof follows the OP_RETURN <genesis_block_hash> <destination_scriptpubkey>
// in multiple pushes: <full_pubkey> <proof>
bool ScriptHasValidPAKProof(const CScript& script, const uint256& genesis_hash)
{
    assert(script.IsPegoutScript(genesis_hash));

    CPAKList paklist;
    if (g_paklist_config) {
        paklist = *g_paklist_config;
    } else {
        paklist = g_paklist_blockchain;
    }

    if (paklist.IsReject() || paklist.IsEmpty()) {
        return false;
    }

    CScript::const_iterator pc = script.begin();
    std::vector<unsigned char> data;
    opcodetype opcode;

    script.GetOp(pc, opcode, data);
    script.GetOp(pc, opcode, data);
    script.GetOp(pc, opcode, data);

    CScript chain_dest(data.begin(), data.end());

    // Grab pubkey hash within the extracted sub-script
    std::vector<unsigned char> extracted_pubkey_hash;

    // Get full pubkey
    if (!script.GetOp(pc, opcode, data) || data.size() != 33 || opcode > OP_PUSHDATA4) {
        return false;
    }
    CPubKey full_pubkey(data.begin(), data.end());

    // Accept any standard single-key type
    if (chain_dest.IsPayToPubkeyHash()) {
        extracted_pubkey_hash = std::vector<unsigned char>(chain_dest.begin()+3, chain_dest.begin()+23);
        if (full_pubkey.GetID() != uint160(extracted_pubkey_hash)) {
            return false;
        }
    } else if (chain_dest.IsPayToWitnessPubkeyHash()) {
        extracted_pubkey_hash = std::vector<unsigned char>(chain_dest.begin()+2, chain_dest.begin()+22);
        if (full_pubkey.GetID() != uint160(extracted_pubkey_hash)) {
            return false;
        }
    } else if (chain_dest.IsPayToScriptHash()) {
        // Take full_pubkey, and hash it to match against chain_dest
        CScript p2wpkh(CScript() << OP_0 << ToByteVector(full_pubkey.GetID()));
        unsigned char h160[20];
        CHash160().Write(p2wpkh.data(), p2wpkh.size()).Finalize(h160);
        if (memcmp(h160, chain_dest.data()+2, sizeof(h160))) {
            return false;
        }
    } else {
        return false;
    }

    // Parse pubkey
    secp256k1_pubkey pubkey;
    if (secp256k1_ec_pubkey_parse(secp256k1_ctx_pak, &pubkey, &data[0], data.size()) != 1) {
        return false;
    }

    if (!script.GetOp(pc, opcode, data) || opcode > OP_PUSHDATA4 || data.size() == 0) {
        return false;
    }

    // Parse whitelist proof
    secp256k1_whitelist_signature sig;
    if (secp256k1_whitelist_signature_parse(secp256k1_ctx_pak, &sig, &data[0], data.size()) != 1)
        return false;

    if (secp256k1_whitelist_signature_n_keys(&sig) != paklist.size()) {
        return false;
    }

    if (secp256k1_whitelist_verify(secp256k1_ctx_pak, &sig, &paklist.OnlineKeys()[0], &paklist.OfflineKeys()[0], paklist.size(), &pubkey) != 1) {
        return false;
    }

    //No more pushes allowed
    if (script.GetOp(pc, opcode, data)) {
        return false;
    }

    return true;
}
