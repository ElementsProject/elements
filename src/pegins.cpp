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
#include <util.h>

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
    //if (!txBTC.vout[nOut].nValue.IsExplicit()) {
    //    return false;
    //}
    //if (!txBTC.vout[nOut].nAsset.IsExplicit()) {
    //    return false;
    //}
    //if (txBTC.vout[nOut].nAsset.GetAsset() != Params().GetConsensus().parent_pegged_asset) {
    //    return false;
    //}
    //amount = txBTC.vout[nOut].nValue.GetAmount();
    //TODO(rebase) reenable above for CA/CT
    amount = txBTC.vout[nOut].nValue;
    return true;
}

// Takes federation redeem script and adds HMAC_SHA256(pubkey, scriptPubKey) as a tweak to each pubkey
CScript calculate_contract(const CScript& federationRedeemScript, const CScript& scriptPubKey) {
    CScript scriptDestination;
    txnouttype type;
    std::vector<std::vector<unsigned char> > solutions;
    // Sanity check fedRedeemScript
    if (!Solver(federationRedeemScript, type, solutions) || (type != TX_MULTISIG && type != TX_TRUE)) {
       assert(false);
    }

    {
        CScript::const_iterator sdpc = federationRedeemScript.begin();
        std::vector<unsigned char> vch;
        opcodetype opcodeTmp;
        while (federationRedeemScript.GetOp(sdpc, opcodeTmp, vch))
        {
            size_t pub_len = 33;
            if (vch.size() == pub_len)
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
    }

    return scriptDestination;
}

template<typename T>
static bool CheckPeginTx(const std::vector<unsigned char>& tx_data, T& pegtx, const COutPoint& prevout, const CAmount claim_amount, const CScript& claim_script)
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

    // Check that the witness program matches the p2ch on the p2sh-p2wsh transaction output
    CScript tweaked_fedpegscript = calculate_contract(Params().GetConsensus().fedpegScript, claim_script);
    CScript witness_output(GetScriptForWitness(tweaked_fedpegscript));
    CScript expected_script(CScript() << OP_HASH160 << ToByteVector(CScriptID(witness_output)) << OP_EQUAL);
    if (pegtx->vout[prevout.n].scriptPubKey != expected_script) {
        return false;
    }

    return true;
}

template<typename T>
static bool GetBlockAndTxFromMerkleBlock(uint256& block_hash, uint256& tx_hash, T& merkle_block, const std::vector<unsigned char>& merkle_block_raw)
{
    try {
        std::vector<uint256> tx_hashes;
        std::vector<unsigned int> tx_indices;
        CDataStream merkle_block_stream(merkle_block_raw, SER_NETWORK, PROTOCOL_VERSION);
        merkle_block_stream >> merkle_block;
        block_hash = merkle_block.header.GetHash();

        if (!merkle_block_stream.empty()) {
           return false;
        }
        if (merkle_block.txn.ExtractMatches(tx_hashes, tx_indices) != merkle_block.header.hashMerkleRoot || tx_hashes.size() != 1) {
            return false;
        }
        tx_hash = tx_hashes[0];
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

bool IsValidPeginWitness(const CScriptWitness& pegin_witness, const COutPoint& prevout, bool check_depth) {
    // 0) Return false if !consensus.has_parent_chain
    if (!Params().GetConsensus().has_parent_chain) {
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
        return false;
    }

    CDataStream stream(stack[0], SER_NETWORK, PROTOCOL_VERSION);
    CAmount value;
    try {
        stream >> value;
    } catch (...) {
        return false;
    }

    if (!MoneyRange(value)) {
        return false;
    }

    // Get asset type
    if (stack[1].size() != 32) {
        return false;
    }
    //TODO(rebase) CA
    //CAsset asset(stack[1]);

    // Get genesis blockhash
    if (stack[2].size() != 32) {
        return false;
    }
    uint256 gen_hash(stack[2]);

    // Get claim_script, sanity check size
    CScript claim_script(stack[3].begin(), stack[3].end());
    if (claim_script.size() > 100) {
        return false;
    }

    uint256 block_hash;
    uint256 tx_hash;
    int num_txs;
    // Get txout proof
    if (Params().GetConsensus().ParentChainHasPow()) {
        Sidechain::Bitcoin::CMerkleBlock merkle_block_pow;
        if (!GetBlockAndTxFromMerkleBlock(block_hash, tx_hash, merkle_block_pow, stack[5])) {
            return false;
        }
        if (!CheckParentProofOfWork(block_hash, merkle_block_pow.header.nBits, Params().GetConsensus())) {
            return false;
        }

        Sidechain::Bitcoin::CTransactionRef pegtx;
        if (!CheckPeginTx(stack[4], pegtx, prevout, value, claim_script)) {
            return false;
        }

        num_txs = merkle_block_pow.txn.GetNumTransactions();
    } else {
        CMerkleBlock merkle_block;
        if (!GetBlockAndTxFromMerkleBlock(block_hash, tx_hash, merkle_block, stack[5])) {
            return false;
        }

        if (!CheckProofSignedParent(merkle_block.header, Params().GetConsensus())) {
            return false;
        }

        CTransactionRef pegtx;
        if (!CheckPeginTx(stack[4], pegtx, prevout, value, claim_script)) {
            return false;
        }

        num_txs = merkle_block.txn.GetNumTransactions();
    }

    // Check that the merkle proof corresponds to the txid
    if (prevout.hash != tx_hash) {
        return false;
    }

    // Check the genesis block corresponds to a valid peg (only one for now)
    if (gen_hash != Params().ParentGenesisBlockHash()) {
        return false;
    }

    //TODO(rebase) CA
    //// Check the asset type corresponds to a valid pegged asset (only one for now)
    //if (asset != Params().GetConsensus().pegged_asset) {
    //    return false;
    //}

    // Finally, validate peg-in via rpc call
    if (check_depth && gArgs.GetBoolArg("-validatepegin", DEFAULT_VALIDATE_PEGIN)) {
        if (!IsConfirmedBitcoinBlock(block_hash, Params().GetConsensus().pegin_min_depth, num_txs)) {
            return false;
        }
    }
    return true;
}

// Constructs unblinded "bitcoin" output to be used in amount and scriptpubkey checks during pegin validation.
CTxOut GetPeginOutputFromWitness(const CScriptWitness& pegin_witness) {
    CDataStream stream(pegin_witness.stack[0], SER_NETWORK, PROTOCOL_VERSION);
    CAmount value;
    stream >> value;

    //TODO(rebase) CA
    //return CTxOut(CAsset(pegin_witness.stack[1]), value, CScript(pegin_witness.stack[3].begin(), pegin_witness.stack[3].end()));
    return CTxOut(value, CScript(pegin_witness.stack[3].begin(), pegin_witness.stack[3].end()));
}
