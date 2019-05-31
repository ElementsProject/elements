
#ifndef BITCOIN_DYNAFED_H
#define BITCOIN_DYNAFED_H

#include <chain.h>
#include <chainparams.h>
#include <primitives/block.h>


bool NextBlockIsParameterTransition(const CBlockIndex* pindexPrev, const Consensus::Params& consensus, ConsensusParamEntry& winning_entry);

/* Compute the next block's enforced parameters */
ConsensusParamEntry ComputeNextBlockFullCurrentParameters(const CBlockIndex* pindexPrev, const Consensus::Params& consensus);
/* Compute the next block's expected published parameters. Blocks at "epoch_age" of non-0 only
 * publish signblockscript-related fields */
ConsensusParamEntry ComputeNextBlockCurrentParameters(const CBlockIndex* pindexPrev, const Consensus::Params& consensus);


#endif //  BITCOIN_DYNAFED_H
