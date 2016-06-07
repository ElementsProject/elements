#ifndef BITCOIN_BLIND_H_
#define BITCOIN_BLIND_H_ 1

#include "key.h"
#include "pubkey.h"
#include "primitives/transaction.h"

bool UnblindOutput(const CKey& blinding_key, const CTxOut& txout, CAmount& amount_out, uint256& blinding_factor_out);

/* Returns false if there is no output to create where the non-zero resultant (inputs - outputs) factor can be put.
 * The caller should retry with an extra blinded output, in that case.
 * @param[in]   input_blinding_factors - A vector of input blinding factors that will be used to create the balanced output blinding factors
 * @param[in/out]   output_blinding_factors - A vector of blinding factors. Null uint256 values are used to signal to the callee that a new blinding is needed. New blinds then replace the blank values.
 * @param[in]   blinding factor must be created for the commitments and range proof creation. Non-null is used to signal that the given value should be used.
 * @param[in]   output_pubkeys - If non-null, these pubkeys will be used in conjunction with the non-null passed in output blinding factors.
 * @param[in/out]   tx - The transaction to be modified.
 */
bool BlindOutputs(const std::vector<uint256>& input_blinding_factors, std::vector<uint256>& output_blinding_factors, const std::vector<CPubKey>& output_pubkeys, CMutableTransaction& tx);

#endif
