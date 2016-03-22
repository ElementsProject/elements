#ifndef BITCOIN_BLIND_H_
#define BITCOIN_BLIND_H_ 1

#include "key.h"
#include "pubkey.h"
#include "primitives/transaction.h"

bool UnblindOutput(const CKey& blinding_key, const CTxOut& txout, CAmount& amount_out, uint256& blinding_factor_out);

/* Returns false if there is no output to create where the non-zero resultant (inputs - outputs) factor can be put.
 * The caller should retry with an extra blinded output, in that case.
 */
bool BlindOutputs(const std::vector<uint256>& input_blinding_factors, const std::vector<uint256>& output_blinding_factors, const std::vector<CPubKey>& output_pubkeys, CMutableTransaction& tx);

#endif
