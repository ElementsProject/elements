
#include <dynafed.h>
#include <hash.h>

bool NextBlockIsParameterTransition(const CBlockIndex* pindexPrev, const Consensus::Params& consensus, DynaFedParamEntry& winning_entry)
{
    uint32_t next_height = pindexPrev->nHeight + 1;
    assert(consensus.dynamic_epoch_length != 0);
    if (next_height % consensus.dynamic_epoch_length != 0) {
        winning_entry.SetNull();
        return false;
    }
    std::map<uint256, uint32_t> vote_tally;
    assert(next_height >= consensus.dynamic_epoch_length);
    for (int32_t height = next_height - 1; height >= (int32_t)(next_height - consensus.dynamic_epoch_length); --height) {
        const CBlockIndex* p_epoch_walk = pindexPrev->GetAncestor(height);
        assert(p_epoch_walk);
        const DynaFedParamEntry& proposal = p_epoch_walk->dynafed_params.m_proposed;
        const uint256 proposal_root = proposal.CalculateRoot();
        vote_tally[proposal_root]++;
        // Short-circuit once 4/5 threshold is reached
        if (!proposal_root.IsNull() && vote_tally[proposal_root] >=
                (consensus.dynamic_epoch_length*4)/5) {
            winning_entry = proposal;
            return true;
        }
    }
    winning_entry.SetNull();
    return false;
}

DynaFedParamEntry ComputeNextBlockFullCurrentParameters(const CBlockIndex* pindexPrev, const Consensus::Params& consensus)
{
    assert(pindexPrev);

    uint32_t next_height = pindexPrev->nHeight+1;
    const uint32_t epoch_length = consensus.dynamic_epoch_length;
    uint32_t epoch_age = next_height % epoch_length;

    DynaFedParamEntry winning_proposal;
    // Early return when there is a winning proposal
    if (NextBlockIsParameterTransition(pindexPrev, consensus, winning_proposal)) {
        assert(epoch_age == 0);
        return winning_proposal;
    }

    // Since no transition took place, find most recent epoch start

    // If next block is start of new epoch, walk backwards one epoch
    uint32_t epoch_start_height = next_height - epoch_age;
    if (epoch_age == 0) {
        epoch_start_height -= epoch_length;
    }

    // We need to put in place the previous epoch's current which
    // may be pre-dynafed params
    const CBlockIndex* p_epoch_start = pindexPrev->GetAncestor(epoch_start_height);
    assert(p_epoch_start);
    if (p_epoch_start->dynafed_params.IsNull()) {
        // We need to construct the "full" current parameters of pre-dynafed
        // consensus

        // Convert signblockscript to P2WSH
        uint256 signblock_witness_program;
        CSHA256().Write(p_epoch_start->proof.challenge.data(), p_epoch_start->proof.challenge.size()).Finalize(signblock_witness_program.begin());
        CScript p2wsh_signblock_script = CScript() << OP_0 << ToByteVector(signblock_witness_program);

        // Make P2SH-P2WSH-ness of non-dynafed fedpegscript explicit
        uint256 fedpegscript_redeemscript;
        CSHA256().Write(consensus.fedpegScript.data(), consensus.fedpegScript.size()).Finalize(fedpegscript_redeemscript.begin());
        CScript fedpeg_p2sw = CScript() << OP_0 << ToByteVector(fedpegscript_redeemscript);
        uint160 fedpeg_p2sh(Hash160(fedpeg_p2sw));
        CScript sh_wsh_fedpeg_program = CScript() << OP_HASH160 << ToByteVector(fedpeg_p2sh) << OP_EQUAL;

        // Put them in winning proposal
        winning_proposal = DynaFedParamEntry(p2wsh_signblock_script, consensus.max_block_signature_size, sh_wsh_fedpeg_program, consensus.fedpegScript, consensus.first_extension_space);
    } else {
        winning_proposal = p_epoch_start->dynafed_params.m_current;
    }
    return winning_proposal;
}

// TODO cache this in CBlockIndex itself?
DynaFedParamEntry ComputeNextBlockCurrentParameters(const CBlockIndex* pindexPrev, const Consensus::Params& consensus)
{
    assert(pindexPrev);

    DynaFedParamEntry entry = ComputeNextBlockFullCurrentParameters(pindexPrev, consensus);

    uint32_t next_height = pindexPrev->nHeight+1;
    const uint32_t epoch_length = consensus.dynamic_epoch_length;
    uint32_t epoch_age = next_height % epoch_length;

    // Return appropriate format based on epoch age or if we *just* activated
    // dynafed via BIP9
    if (epoch_age == 0 || pindexPrev->dynafed_params.IsNull()) {
        return entry;
    } else {
        return DynaFedParamEntry(entry.m_signblockscript, entry.m_signblock_witness_limit, entry.CalculateExtraRoot());

    }
}

