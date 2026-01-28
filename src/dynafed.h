#ifndef BITCOIN_DYNAFED_H
#define BITCOIN_DYNAFED_H

#include <chain.h>
#include <chainparams.h>
#include <primitives/block.h>

/* Returns true if the next block would be the first block of an epoch with new
 * parameters. It also returns the parameter set that is being transitioned to. */
bool NextBlockIsParameterTransition(const CBlockIndex* pindexPrev, const Consensus::Params& consensus, DynaFedParamEntry& winning_entry);

/* Compute the next block's enforced parameters */
DynaFedParamEntry ComputeNextBlockFullCurrentParameters(const CBlockIndex* pindexPrev, const Consensus::Params& consensus);
/* Compute the next block's expected published parameters. Blocks at "epoch_age" of non-0 only
 * publish signblockscript-related fields */
DynaFedParamEntry ComputeNextBlockCurrentParameters(const CBlockIndex* pindexPrev, const Consensus::Params& consensus);

/* Get the threshold (t) and maybe the total pubkeys (n) of the first OP_CHECKMULTISIG in the fedpegscript.
 * Assumes the fedpegscript starts with the threshold, otherwise returns false.
 * Uses CScript::DecodeOP_N, so only supports up to a threshold of 16, otherwise asserts.
 * Supports a fedpegscript like OP_TRUE by returning early. */
bool ParseFedPegQuorum(const CScript& fedpegscript, int& t, int& n);

#endif // BITCOIN_DYNAFED_H
