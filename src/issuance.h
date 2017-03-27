#include "primitives/transaction.h"
#include "amount.h"
#include "hash.h"
#include "consensus/merkle.h"

#ifndef BITCOIN_ISSUANCE_H
#define BITCOIN_ISSUANCE_H

/**
 * Calculate the asset entropy from an COutPoint and a tx-author specified
 * Ricardian contract. See Definition 18 of the confidential assets paper.
 *
 * @param[out]  entropy       The asset entropy, which is used as input to
 *                            CalculateAsset and CalculateReissuanceToken.
 * @param[in]   prevout       Reference to the UTXO being spent.
 * @param[in]   contracthash  Root hash of the issuer-specified Ricardian
 *                            contract.
 */
void GenerateAssetEntropy(uint256& entropy, const COutPoint& prevout, const uint256& contracthash);

/**
 * Derive the asset from the entropy. See Definintion 19 of the confidential
 * assets paper.
 *
 * @param[out]  asset    The nonce used as auxiliary input to the Pedersen
 *                       commitment setup to derive the unblinded asset tag.
 * @param[in]   entropy  The asset entropy returned by GenerateAssetEntropy.
 */
void CalculateAsset(CAsset& asset, const uint256& entropy);

/**
 * Derive the asset reissuance token asset from the entropy and reissuance
 * parameters (confidential or explicit). See Definition 21 of the confidential
 * assets paper.
 *
 * @param[out]  reissuanceToken  The nonce used as auxiliary input to the
 *                               Pedersen commitment setup to derive the
 *                               unblinded reissuance asset tag.
 * @param[in]   entropy          The asset entropy returned by GenerateAssetEntropy.
 * @param[in]   fConfidential    Set to true if the initial issuance was blinded,
 *                               false otherwise.
 */
void CalculateReissuanceToken(CAsset& reissuanceToken, const uint256& entropy, bool fConfidential);

#endif // BITCOIN_ISSUANCE_H
