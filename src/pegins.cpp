// Copyright (c) 2017-2017 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <pegins.h>

#include <arith_uint256.h>
#include <block_proof.h>
#include <chainparams.h>
#include <crypto/hmac_sha256.h>
#include <consensus/consensus.h>
#include <consensus/validation.h>
#include <mainchainrpc.h>
#include <merkleblock.h>
#include <pow.h>
#include <primitives/transaction.h>
#include <primitives/bitcoin/merkleblock.h>
#include <secp256k1.h>
#include <script/interpreter.h>
#include <script/standard.h>
#include <streams.h>
#include <util/system.h>
#include <dynafed.h>

//
// ELEMENTS
//

namespace {
static secp256k1_context* secp256k1_ctx_validation;

class Secp256k1Ctx
{
public:
    Secp256k1Ctx() {
        assert(secp256k1_ctx_validation == NULL);
        secp256k1_ctx_validation = secp256k1_context_create(SECP256K1_CONTEXT_VERIFY | SECP256K1_CONTEXT_SIGN);
        assert(secp256k1_ctx_validation != NULL);
    }

    ~Secp256k1Ctx() {
        assert(secp256k1_ctx_validation != NULL);
        secp256k1_context_destroy(secp256k1_ctx_validation);
        secp256k1_ctx_validation = NULL;
    }
};
static Secp256k1Ctx instance_of_secp256k1ctx;
}

bool GetAmountFromParentChainPegin(CAmount& amount, const Sidechain::Bitcoin::CTransaction& txBTC, unsigned int nOut)
{
    amount = txBTC.vout[nOut].nValue;
    return true;
}

bool GetAmountFromParentChainPegin(CAmount& amount, const CTransaction& txBTC, unsigned int nOut)
{
    if (!txBTC.vout[nOut].nValue.IsExplicit()) {
        return false;
    }
    if (!txBTC.vout[nOut].nAsset.IsExplicit()) {
        return false;
    }
    if (txBTC.vout[nOut].nAsset.GetAsset() != Params().GetConsensus().parent_pegged_asset) {
        return false;
    }
    amount = txBTC.vout[nOut].nValue.GetAmount();
    return true;
}

// Takes federation redeem script and adds HMAC_SHA256(pubkey, scriptPubKey) as a tweak to each pubkey
CScript calculate_contract(const CScript& federation_script, const CScript& scriptPubKey) {
    CScript scriptDestination;

    bool is_liquidv1_watchman = MatchLiquidWatchman(federation_script);

    CScript::const_iterator sdpc = federation_script.begin();
    std::vector<unsigned char> vch;
    opcodetype opcodeTmp;
    bool liquid_op_else_found = false;
    while (federation_script.GetOp(sdpc, opcodeTmp, vch))
    {

        // For liquidv1 initial watchman template, don't tweak emergency keys
        if (is_liquidv1_watchman && opcodeTmp == OP_ELSE) {
            liquid_op_else_found = true;
        }

        size_t pub_len = 33;
        if (vch.size() == pub_len && !liquid_op_else_found)
        {
            unsigned char tweak[32];
            CHMAC_SHA256(vch.data(), pub_len).Write(scriptPubKey.data(), scriptPubKey.size()).Finalize(tweak);
            int ret;
            secp256k1_pubkey watchman;
            secp256k1_pubkey tweaked;
            ret = secp256k1_ec_pubkey_parse(secp256k1_ctx_validation, &watchman, vch.data(), pub_len);
            assert(ret == 1);
            ret = secp256k1_ec_pubkey_parse(secp256k1_ctx_validation, &tweaked, vch.data(), pub_len);
            assert(ret == 1);
            // If someone creates a tweak that makes this fail, they broke SHA256
            ret = secp256k1_ec_pubkey_tweak_add(secp256k1_ctx_validation, &tweaked, tweak);
            assert(ret == 1);
            unsigned char new_pub[33];
            ret = secp256k1_ec_pubkey_serialize(secp256k1_ctx_validation, new_pub, &pub_len, &tweaked, SECP256K1_EC_COMPRESSED);
            assert(ret == 1);
            assert(pub_len == 33);

            // push tweaked pubkey
            std::vector<unsigned char> pub_vec(new_pub, new_pub + pub_len);
            scriptDestination << pub_vec;

            // Sanity checks to reduce pegin risk. If the tweaked
            // value flips a bit, we may lose pegin funds irretrievably.
            // We take the tweak, derive its pubkey and check that
            // `tweaked - watchman = tweak` to check the computation
            // two different ways
            secp256k1_pubkey tweaked2;
            ret = secp256k1_ec_pubkey_create(secp256k1_ctx_validation, &tweaked2, tweak);
            assert(ret);
            ret = secp256k1_ec_pubkey_negate(secp256k1_ctx_validation, &watchman);
            assert(ret);
            secp256k1_pubkey* pubkey_combined[2];
            pubkey_combined[0] = &watchman;
            pubkey_combined[1] = &tweaked;
            secp256k1_pubkey maybe_tweaked2;
            ret = secp256k1_ec_pubkey_combine(secp256k1_ctx_validation, &maybe_tweaked2, pubkey_combined, 2);
            assert(ret);
            assert(!memcmp(&maybe_tweaked2, &tweaked2, 64));
        } else {
            // add to script untouched
            if (vch.size() > 0) {
                scriptDestination << vch;
            } else {
                scriptDestination << opcodeTmp;
            }
        }
    }

    return scriptDestination;
}

template<typename T>
static bool CheckPeginTx(const std::vector<unsigned char>& tx_data, T& pegtx, const COutPoint& prevout, const CAmount claim_amount, const CScript& claim_script, const std::vector<std::pair<CScript, CScript>>& fedpegscripts)
{
    try {
        CDataStream pegtx_stream(tx_data, SER_NETWORK, PROTOCOL_VERSION);
        pegtx_stream >> pegtx;
        if (!pegtx_stream.empty()) {
            return false;
        }
    } catch (std::exception& e) {
        // Invalid encoding of transaction
        return false;
    }

    // Check that transaction matches txid
    if (pegtx->GetHash() != prevout.hash) {
        return false;
    }

    if (prevout.n >= pegtx->vout.size()) {
        return false;
    }
    CAmount amount = 0;
    if (!GetAmountFromParentChainPegin(amount, *pegtx, prevout.n)) {
        return false;
    }
    // Check the transaction nout/value matches
    if (claim_amount != amount) {
        return false;
    }

    // Check that the witness program matches the p2ch on the (p2sh-)p2wsh
    // transaction output. We support multiple scripts as a grace period for peg-in users
    for (const auto& scripts : fedpegscripts) {
        int fedpeg_version = 0;
        std::vector<unsigned char> fedpeg_program;
        scripts.first.IsWitnessProgram(fedpeg_version, fedpeg_program);
        // We immediately return true if any fedpegscripts are unencumbered
        // by currently-known parent chain segwit versions.
        // TODO: Refactor for future versionbits deployment of parent-segwit version
        if (fedpeg_version > 0) {
            return true;
        }
        CScript tweaked_fedpegscript = calculate_contract(scripts.second, claim_script);
        // TODO: Remove script/standard.h dep for GetScriptFor*
        CScript expected_script(GetScriptForDestination(WitnessV0ScriptHash(tweaked_fedpegscript)));
        if (scripts.first.IsPayToScriptHash()) {
            expected_script = GetScriptForDestination(ScriptHash(expected_script));
        }
        if (pegtx->vout[prevout.n].scriptPubKey == expected_script) {
            return true;
        }
    }
    return false;
}

template<typename T>
static bool GetBlockAndTxFromMerkleBlock(uint256& block_hash, uint256& tx_hash, unsigned int& tx_index, T& merkle_block, const std::vector<unsigned char>& merkle_block_raw)
{
    try {
        std::vector<uint256> tx_hashes;
        std::vector<unsigned int> tx_indices;
        CDataStream merkle_block_stream(merkle_block_raw, SER_NETWORK, PROTOCOL_VERSION | SERIALIZE_TRANSACTION_NO_WITNESS);
        merkle_block_stream >> merkle_block;
        block_hash = merkle_block.header.GetHash();

        if (!merkle_block_stream.empty()) {
           return false;
        }
        if (merkle_block.txn.ExtractMatches(tx_hashes, tx_indices) != merkle_block.header.hashMerkleRoot || tx_hashes.size() != 1) {
            return false;
        }
        tx_hash = tx_hashes[0];
        tx_index = tx_indices[0];
    } catch (std::exception& e) {
        // Invalid encoding of merkle block
        return false;
    }
    return true;
}

bool CheckParentProofOfWork(uint256 hash, unsigned int nBits, const Consensus::Params& params)
{
    bool fNegative;
    bool fOverflow;
    arith_uint256 bnTarget;

    bnTarget.SetCompact(nBits, &fNegative, &fOverflow);

    // Check range
    if (fNegative || bnTarget == 0 || fOverflow || bnTarget > UintToArith256(params.parentChainPowLimit))
        return false;

    // Check proof of work matches claimed amount
    if (UintToArith256(hash) > bnTarget)
        return false;

    return true;
}

bool IsValidPeginWitness(const CScriptWitness& pegin_witness, const std::vector<std::pair<CScript, CScript>>& fedpegscripts, const COutPoint& prevout, std::string& err_msg, bool check_depth) {
    // 0) Return false if !consensus.has_parent_chain
    if (!Params().GetConsensus().has_parent_chain) {
        err_msg = "Parent chain is not enabled on this network.";
        return false;
    }

    // Format on stack is as follows:
    // 1) value - the value of the pegin output
    // 2) asset type - the asset type being pegged in
    // 3) genesis blockhash - genesis block of the parent chain
    // 4) claim script - script to be evaluated for spend authorization
    // 5) serialized transaction - serialized bitcoin transaction
    // 6) txout proof - merkle proof connecting transaction to header
    //
    // First 4 values(plus prevout) are enough to validate a peg-in without any internal knowledge
    // of Bitcoin serialization. This is useful for further abstraction by outsourcing
    // the other validity checks to RPC calls.

    const std::vector<std::vector<unsigned char> >& stack = pegin_witness.stack;
    // Must include all elements
    if (stack.size() != 6) {
        err_msg = "Not enough stack items.";
        return false;
    }

    CDataStream stream(stack[0], SER_NETWORK, PROTOCOL_VERSION);
    CAmount value;
    try {
        stream >> value;
    } catch (...) {
        err_msg = "Could not deserialize value.";
        return false;
    }

    if (!MoneyRange(value)) {
        err_msg = "Value was not in valid value range.";
        return false;
    }

    // Get asset type
    if (stack[1].size() != 32) {
        err_msg = "Asset type was not 32 bytes.";
        return false;
    }
    CAsset asset(stack[1]);

    // Get genesis blockhash
    if (stack[2].size() != 32) {
        err_msg = "Parent genesis blockchaash was not 32 bytes.";
        return false;
    }
    uint256 gen_hash(stack[2]);

    // Get claim_script, sanity check size
    CScript claim_script(stack[3].begin(), stack[3].end());
    if (claim_script.size() > 100) {
        err_msg = "Claim script is too large.";
        return false;
    }

    uint256 block_hash;
    uint256 tx_hash;
    int num_txs;
    unsigned int tx_index = 0;
    // Get txout proof
    if (Params().GetConsensus().ParentChainHasPow()) {
        Sidechain::Bitcoin::CMerkleBlock merkle_block_pow;
        if (!GetBlockAndTxFromMerkleBlock(block_hash, tx_hash, tx_index, merkle_block_pow, stack[5])) {
            err_msg = "Could not extract block and tx from merkleblock.";
            return false;
        }
        if (!CheckParentProofOfWork(block_hash, merkle_block_pow.header.nBits, Params().GetConsensus())) {
            err_msg = "Parent proof of work is invalid or insufficient.";
            return false;
        }

        Sidechain::Bitcoin::CTransactionRef pegtx;
        if (!CheckPeginTx(stack[4], pegtx, prevout, value, claim_script, fedpegscripts)) {
            err_msg = "Peg-in tx is invalid.";
            return false;
        }

        num_txs = merkle_block_pow.txn.GetNumTransactions();
    } else {
        CMerkleBlock merkle_block;
        if (!GetBlockAndTxFromMerkleBlock(block_hash, tx_hash, tx_index, merkle_block, stack[5])) {
            err_msg = "Could not extract block and tx from merkleblock.";
            return false;
        }

        if (!CheckProofSignedParent(merkle_block.header, Params().GetConsensus())) {
            err_msg = "Parent signed block is invalid.";
            return false;
        }

        CTransactionRef pegtx;
        if (!CheckPeginTx(stack[4], pegtx, prevout, value, claim_script, fedpegscripts)) {
            err_msg = "Peg-in tx is invalid.";
            return false;
        }

        num_txs = merkle_block.txn.GetNumTransactions();
    }

    // Check that the merkle proof corresponds to the txid
    if (prevout.hash != tx_hash) {
        err_msg = "Merkle proof and txid mismatch.";
        return false;
    }

    // Check the genesis block corresponds to a valid peg (only one for now)
    if (gen_hash != Params().ParentGenesisBlockHash()) {
        err_msg = "Parent genesis block mismatch.";
        return false;
    }

    // Check the asset type corresponds to a valid pegged asset (only one for now)
    if (asset != Params().GetConsensus().pegged_asset) {
        return false;
    }

    // Finally, validate peg-in via rpc call
    if (check_depth && gArgs.GetBoolArg("-validatepegin", Params().GetConsensus().has_parent_chain)) {
        unsigned int required_depth = Params().GetConsensus().pegin_min_depth;
        // Don't allow coinbase output claims before coinbase maturity
        if (tx_index == 0) {
            required_depth = std::max(required_depth, (unsigned int)COINBASE_MATURITY);
        }
        LogPrintf("Required depth: %d\n", required_depth);
        if (!IsConfirmedBitcoinBlock(block_hash, required_depth, num_txs)) {
            err_msg = "Needs more confirmations.";
            return false;
        }
    }
    return true;
}

bool MatchLiquidWatchman(const CScript& script)
{
    CScript::const_iterator it = script.begin();
    std::vector<unsigned char> data;
    opcodetype opcode;

    // Stack depth check for branch choice
    if (!script.GetOp(it, opcode, data) || opcode != OP_DEPTH) {
        return false;
    }
    // Take in value, then check equality
    if (!script.GetOp(it, opcode, data) ||
            !script.GetOp(it, opcode, data) ||
            opcode != OP_EQUAL) {
        return false;
    }
    // IF EQUAL
    if (!script.GetOp(it, opcode, data) || opcode != OP_IF) {
        return false;
    }
    // Take in value k, make sure minimally encoded number from 1 to 16
    if (!script.GetOp(it, opcode, data) ||
            opcode > OP_16 ||
            (opcode < OP_1NEGATE && !CheckMinimalPush(data, opcode))) {
        return false;
    }
    opcodetype opcode2 = opcode;
    std::vector<unsigned char> num = data;
    // Iterate through multisig stuff until ELSE is hit
    while (opcode != OP_ELSE) {
        if (!script.GetOp(it, opcode, data)) {
            return false;
        }
    }
    // Take minimally-encoded CSV push number k'
    if (!script.GetOp(it, opcode, data) ||
            opcode > OP_16 || (opcode < OP_1NEGATE && !CheckMinimalPush(data, opcode))) {
        return false;
    }
    // CSV
    if (!script.GetOp(it, opcode, data) || opcode != OP_CHECKSEQUENCEVERIFY) {
        return false;
    }
    // Drop the CSV number
    if (!script.GetOp(it, opcode, data) || opcode != OP_DROP) {
        return false;
    }
    // Take the minimally-encoded n of k-of-n multisig arg
    if (!script.GetOp(it, opcode, data) ||
            opcode > OP_16 || (opcode < OP_1NEGATE && !CheckMinimalPush(data, opcode)) ) {
        return false;
    }

    // The two multisig k-numbers must not match, otherwise ELSE branch can not be reached
    if (opcode == opcode2 && num == data) {
        return false;
    }

    // Find the ENDIF
    while (opcode != OP_ENDIF) {
        if (!script.GetOp(it, opcode, data)) {
            return false;
        }
    }
    // CHECKMULTISIG
    if (!script.GetOp(it, opcode, data) || opcode != OP_CHECKMULTISIG) {
        return false;
    }
    // No more pushes
    return (it == script.end());
}

std::vector<std::pair<CScript, CScript>> GetValidFedpegScripts(const CBlockIndex* pblockindex, const Consensus::Params& params, bool nextblock_validation)
{
    assert(pblockindex);

    std::vector<std::pair<CScript, CScript>> fedpegscripts;

    const int32_t epoch_length = (int32_t) params.dynamic_epoch_length;
    const int32_t epoch_age = pblockindex->nHeight % epoch_length;
    const int32_t epoch_start_height = pblockindex->nHeight - epoch_age;

    // In mempool and general "enforced next block" RPC we need to look ahead one block
    // to see if we're on a boundary. If so, put that epoch's fedpegscript in place
    if (nextblock_validation && epoch_age == epoch_length - 1) {
        DynaFedParamEntry next_param = ComputeNextBlockFullCurrentParameters(pblockindex, params);
        fedpegscripts.push_back(std::make_pair(next_param.m_fedpeg_program, next_param.m_fedpegscript));
    }

    // Next we walk backwards up to M epoch starts
    for (int32_t i = 0; i < (int32_t) params.total_valid_epochs; i++) {
        // We are within total_valid_epochs of the genesis
        if (i * epoch_length > epoch_start_height) {
            break;
        }

        const CBlockIndex* p_epoch_start = pblockindex->GetAncestor(epoch_start_height-i*epoch_length);

        // We're done here, for whatever reason.
        if (!p_epoch_start) {
            break;
        }

        if (!p_epoch_start->dynafed_params.IsNull()) {
            fedpegscripts.push_back(std::make_pair(p_epoch_start->dynafed_params.m_current.m_fedpeg_program, p_epoch_start->dynafed_params.m_current.m_fedpegscript));
        } else {
            fedpegscripts.push_back(std::make_pair(GetScriptForDestination(ScriptHash(GetScriptForDestination(WitnessV0ScriptHash(params.fedpegScript)))), params.fedpegScript));
        }
    }
    // Only return up to the latest total_valid_epochs fedpegscripts, which are enforced
    fedpegscripts.resize(std::min(fedpegscripts.size(), params.total_valid_epochs));
    return fedpegscripts;
}

template<typename T_tx_ref, typename T_merkle_block>
CScriptWitness CreatePeginWitnessInner(const CAmount& value, const CAsset& asset, const uint256& genesis_hash, const CScript& claim_script, const T_tx_ref& tx_ref, const T_merkle_block& merkle_block)
{
    std::vector<unsigned char> value_bytes;
    CVectorWriter ss_val(0, 0, value_bytes, 0);
    try {
        ss_val << value;
    } catch (...) {
        throw std::ios_base::failure("Amount serialization is invalid.");
    }

    // Strip witness data for proof inclusion since only TXID-covered fields matters
    CDataStream ss_tx(SER_NETWORK, PROTOCOL_VERSION | SERIALIZE_TRANSACTION_NO_WITNESS);
    ss_tx << tx_ref;
    std::vector<unsigned char> tx_data_stripped(ss_tx.begin(), ss_tx.end());

    // Serialize merkle block
    CDataStream ss_txout_proof(SER_NETWORK, PROTOCOL_VERSION | SERIALIZE_TRANSACTION_NO_WITNESS);
    ss_txout_proof << merkle_block;
    std::vector<unsigned char> txout_proof_bytes(ss_txout_proof.begin(), ss_txout_proof.end());

    // Construct pegin proof
    CScriptWitness pegin_witness;
    std::vector<std::vector<unsigned char> >& stack = pegin_witness.stack;
    stack.push_back(value_bytes);
    stack.push_back(std::vector<unsigned char>(asset.begin(), asset.end()));
    stack.push_back(std::vector<unsigned char>(genesis_hash.begin(), genesis_hash.end()));
    stack.push_back(std::vector<unsigned char>(claim_script.begin(), claim_script.end()));
    stack.push_back(tx_data_stripped);
    stack.push_back(txout_proof_bytes);
    return pegin_witness;
}

CScriptWitness CreatePeginWitness(const CAmount& value, const CAsset& asset, const uint256& genesis_hash, const CScript& claim_script, const CTransactionRef& tx_ref, const CMerkleBlock& merkle_block)
{
    return CreatePeginWitnessInner(value, asset, genesis_hash, claim_script, tx_ref, merkle_block);
}
CScriptWitness CreatePeginWitness(const CAmount& value, const CAsset& asset, const uint256& genesis_hash, const CScript& claim_script, const Sidechain::Bitcoin::CTransactionRef& tx_ref, const Sidechain::Bitcoin::CMerkleBlock& merkle_block)
{
    return CreatePeginWitnessInner(value, asset, genesis_hash, claim_script, tx_ref, merkle_block);
}

bool DecomposePeginWitness(const CScriptWitness& witness, CAmount& value, CAsset& asset, uint256& genesis_hash, CScript& claim_script, boost::variant<boost::blank, Sidechain::Bitcoin::CTransactionRef, CTransactionRef>& tx, boost::variant<boost::blank, Sidechain::Bitcoin::CMerkleBlock, CMerkleBlock>& merkle_block)
{
    const auto& stack = witness.stack;

    if (stack.size() < 5) return false;

    CDataStream stream(stack[0], SER_NETWORK, PROTOCOL_VERSION);
    stream >> value;

    CAsset tmp_asset(stack[1]);
    asset = tmp_asset;

    uint256 gh(stack[2]);
    genesis_hash = gh;

    CScript s(stack[3].begin(), stack[3].end());
    claim_script = s;

    CDataStream ss_tx(stack[4], SER_NETWORK, PROTOCOL_VERSION);
    if (Params().GetConsensus().ParentChainHasPow()) {
        Sidechain::Bitcoin::CTransactionRef btc_tx;
        ss_tx >> btc_tx;
        tx = btc_tx;
    } else {
        CTransactionRef elem_tx;
        ss_tx >> elem_tx;
        tx = elem_tx;
    }

    CDataStream ss_proof(stack[5], SER_NETWORK, PROTOCOL_VERSION);
    if (Params().GetConsensus().ParentChainHasPow()) {
        Sidechain::Bitcoin::CMerkleBlock tx_proof;
        ss_proof >> tx_proof;
        merkle_block = tx_proof;
    } else {
        CMerkleBlock tx_proof;
        ss_proof >> tx_proof;
        merkle_block = tx_proof;
    }

    return true;
}
