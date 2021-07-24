/* This module defines primitives and jets that are specific to the Elements application for Simplicity.
 */
#ifndef SIMPLICITY_PRIMITIVE_ELEMENTS_JETS_H
#define SIMPLICITY_PRIMITIVE_ELEMENTS_JETS_H

#include "../../jets.h"

/* Primitives for the Elements application of Simplicity. */
bool version(frameItem* dst, frameItem src, const txEnv* env);
bool lockTime(frameItem* dst, frameItem src, const txEnv* env);
bool inputIsPegin(frameItem* dst, frameItem src, const txEnv* env);
bool inputPrevOutpoint(frameItem* dst, frameItem src, const txEnv* env);
bool inputAsset(frameItem* dst, frameItem src, const txEnv* env);
bool inputAmount(frameItem* dst, frameItem src, const txEnv* env);
bool inputScriptHash(frameItem* dst, frameItem src, const txEnv* env);
bool inputSequence(frameItem* dst, frameItem src, const txEnv* env);
bool inputIssuanceBlinding(frameItem* dst, frameItem src, const txEnv* env);
bool inputIssuanceContract(frameItem* dst, frameItem src, const txEnv* env);
bool inputIssuanceEntropy(frameItem* dst, frameItem src, const txEnv* env);
bool inputIssuanceAssetAmt(frameItem* dst, frameItem src, const txEnv* env);
bool inputIssuanceTokenAmt(frameItem* dst, frameItem src, const txEnv* env);
bool outputAsset(frameItem* dst, frameItem src, const txEnv* env);
bool outputAmount(frameItem* dst, frameItem src, const txEnv* env);
bool outputNonce(frameItem* dst, frameItem src, const txEnv* env);
bool outputScriptHash(frameItem* dst, frameItem src, const txEnv* env);
bool outputNullDatum(frameItem* dst, frameItem src, const txEnv* env);
bool scriptCMR(frameItem* dst, frameItem src, const txEnv* env);
bool currentIndex(frameItem* dst, frameItem src, const txEnv* env);
bool currentIsPegin(frameItem* dst, frameItem src, const txEnv* env);
bool currentPrevOutpoint(frameItem* dst, frameItem src, const txEnv* env);
bool currentAsset(frameItem* dst, frameItem src, const txEnv* env);
bool currentAmount(frameItem* dst, frameItem src, const txEnv* env);
bool currentScriptHash(frameItem* dst, frameItem src, const txEnv* env);
bool currentSequence(frameItem* dst, frameItem src, const txEnv* env);
bool currentIssuanceBlinding(frameItem* dst, frameItem src, const txEnv* env);
bool currentIssuanceContract(frameItem* dst, frameItem src, const txEnv* env);
bool currentIssuanceEntropy(frameItem* dst, frameItem src, const txEnv* env);
bool currentIssuanceAssetAmt(frameItem* dst, frameItem src, const txEnv* env);
bool currentIssuanceTokenAmt(frameItem* dst, frameItem src, const txEnv* env);
bool inputsHash(frameItem* dst, frameItem src, const txEnv* env);
bool outputsHash(frameItem* dst, frameItem src, const txEnv* env);
bool numInputs(frameItem* dst, frameItem src, const txEnv* env);
bool numOutputs(frameItem* dst, frameItem src, const txEnv* env);

/* :TODO: Not yet implemented.
bool fees(frameItem* dst, frameItem src, const txEnv* env);
*/

#endif
