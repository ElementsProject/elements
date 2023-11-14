/* This module defines primitives and jets that are specific to the Elements application for Simplicity.
 */
#ifndef SIMPLICITY_PRIMITIVE_ELEMENTS_JETS_H
#define SIMPLICITY_PRIMITIVE_ELEMENTS_JETS_H

#include "../../jets.h"

/* Primitives for the Elements application of Simplicity. */
bool version(frameItem* dst, frameItem src, const txEnv* env);
bool lock_time(frameItem* dst, frameItem src, const txEnv* env);
bool input_pegin(frameItem* dst, frameItem src, const txEnv* env);
bool input_prev_outpoint(frameItem* dst, frameItem src, const txEnv* env);
bool input_asset(frameItem* dst, frameItem src, const txEnv* env);
bool input_amount(frameItem* dst, frameItem src, const txEnv* env);
bool input_script_hash(frameItem* dst, frameItem src, const txEnv* env);
bool input_sequence(frameItem* dst, frameItem src, const txEnv* env);
bool input_annex_hash(frameItem* dst, frameItem src, const txEnv* env);
bool input_script_sig_hash(frameItem* dst, frameItem src, const txEnv* env);
bool reissuance_blinding(frameItem* dst, frameItem src, const txEnv* env);
bool new_issuance_contract(frameItem* dst, frameItem src, const txEnv* env);
bool reissuance_entropy(frameItem* dst, frameItem src, const txEnv* env);
bool issuance_asset_amount(frameItem* dst, frameItem src, const txEnv* env);
bool issuance_token_amount(frameItem* dst, frameItem src, const txEnv* env);
bool issuance_asset_proof(frameItem* dst, frameItem src, const txEnv* env);
bool issuance_token_proof(frameItem* dst, frameItem src, const txEnv* env);
bool output_asset(frameItem* dst, frameItem src, const txEnv* env);
bool output_amount(frameItem* dst, frameItem src, const txEnv* env);
bool output_nonce(frameItem* dst, frameItem src, const txEnv* env);
bool output_script_hash(frameItem* dst, frameItem src, const txEnv* env);
bool output_null_datum(frameItem* dst, frameItem src, const txEnv* env);
bool output_is_fee(frameItem* dst, frameItem src, const txEnv* env);
bool output_surjection_proof(frameItem* dst, frameItem src, const txEnv* env);
bool output_range_proof(frameItem* dst, frameItem src, const txEnv* env);
bool genesis_block_hash(frameItem* dst, frameItem src, const txEnv* env);
bool script_cmr(frameItem* dst, frameItem src, const txEnv* env);
bool current_index(frameItem* dst, frameItem src, const txEnv* env);
bool current_pegin(frameItem* dst, frameItem src, const txEnv* env);
bool current_prev_outpoint(frameItem* dst, frameItem src, const txEnv* env);
bool current_asset(frameItem* dst, frameItem src, const txEnv* env);
bool current_amount(frameItem* dst, frameItem src, const txEnv* env);
bool current_script_hash(frameItem* dst, frameItem src, const txEnv* env);
bool current_sequence(frameItem* dst, frameItem src, const txEnv* env);
bool current_reissuance_blinding(frameItem* dst, frameItem src, const txEnv* env);
bool current_new_issuance_contract(frameItem* dst, frameItem src, const txEnv* env);
bool current_reissuance_entropy(frameItem* dst, frameItem src, const txEnv* env);
bool current_issuance_asset_amount(frameItem* dst, frameItem src, const txEnv* env);
bool current_issuance_token_amount(frameItem* dst, frameItem src, const txEnv* env);
bool current_issuance_asset_proof(frameItem* dst, frameItem src, const txEnv* env);
bool current_issuance_token_proof(frameItem* dst, frameItem src, const txEnv* env);
bool current_annex_hash(frameItem* dst, frameItem src, const txEnv* env);
bool current_script_sig_hash(frameItem* dst, frameItem src, const txEnv* env);
bool tapleaf_version(frameItem* dst, frameItem src, const txEnv* env);
bool tappath(frameItem* dst, frameItem src, const txEnv* env);
bool internal_key(frameItem* dst, frameItem src, const txEnv* env);
bool num_inputs(frameItem* dst, frameItem src, const txEnv* env);
bool num_outputs(frameItem* dst, frameItem src, const txEnv* env);

/* Jets for the Elements application of Simplicity. */
bool tx_is_final(frameItem* dst, frameItem src, const txEnv* env);
bool tx_lock_height(frameItem* dst, frameItem src, const txEnv* env);
bool tx_lock_time(frameItem* dst, frameItem src, const txEnv* env);
bool tx_lock_distance(frameItem* dst, frameItem src, const txEnv* env);
bool tx_lock_duration(frameItem* dst, frameItem src, const txEnv* env);
bool check_lock_height(frameItem* dst, frameItem src, const txEnv* env);
bool check_lock_time(frameItem* dst, frameItem src, const txEnv* env);
bool check_lock_distance(frameItem* dst, frameItem src, const txEnv* env);
bool check_lock_duration(frameItem* dst, frameItem src, const txEnv* env);
bool calculate_issuance_entropy(frameItem* dst, frameItem src, const txEnv* env);
bool calculate_asset(frameItem* dst, frameItem src, const txEnv* env);
bool calculate_explicit_token(frameItem* dst, frameItem src, const txEnv* env);
bool calculate_confidential_token(frameItem* dst, frameItem src, const txEnv* env);
bool build_tapleaf_simplicity(frameItem* dst, frameItem src, const txEnv* env);
bool build_tapbranch(frameItem* dst, frameItem src, const txEnv* env);
bool outpoint_hash(frameItem* dst, frameItem src, const txEnv* env);
bool asset_amount_hash(frameItem* dst, frameItem src, const txEnv* env);
bool nonce_hash(frameItem* dst, frameItem src, const txEnv* env);
bool annex_hash(frameItem* dst, frameItem src, const txEnv* env);
bool issuance(frameItem* dst, frameItem src, const txEnv* env);
bool issuance_entropy(frameItem* dst, frameItem src, const txEnv* env);
bool issuance_asset(frameItem* dst, frameItem src, const txEnv* env);
bool issuance_token(frameItem* dst, frameItem src, const txEnv* env);
bool output_amounts_hash(frameItem* dst, frameItem src, const txEnv* env);
bool output_nonces_hash(frameItem* dst, frameItem src, const txEnv* env);
bool output_scripts_hash(frameItem* dst, frameItem src, const txEnv* env);
bool output_range_proofs_hash(frameItem* dst, frameItem src, const txEnv* env);
bool output_surjection_proofs_hash(frameItem* dst, frameItem src, const txEnv* env);
bool outputs_hash(frameItem* dst, frameItem src, const txEnv* env);
bool input_outpoints_hash(frameItem* dst, frameItem src, const txEnv* env);
bool input_amounts_hash(frameItem* dst, frameItem src, const txEnv* env);
bool input_scripts_hash(frameItem* dst, frameItem src, const txEnv* env);
bool input_utxos_hash(frameItem* dst, frameItem src, const txEnv* env);
bool input_sequences_hash(frameItem* dst, frameItem src, const txEnv* env);
bool input_annexes_hash(frameItem* dst, frameItem src, const txEnv* env);
bool input_script_sigs_hash(frameItem* dst, frameItem src, const txEnv* env);
bool inputs_hash(frameItem* dst, frameItem src, const txEnv* env);
bool issuance_asset_amounts_hash(frameItem* dst, frameItem src, const txEnv* env);
bool issuance_token_amounts_hash(frameItem* dst, frameItem src, const txEnv* env);
bool issuance_range_proofs_hash(frameItem* dst, frameItem src, const txEnv* env);
bool issuance_blinding_entropy_hash(frameItem* dst, frameItem src, const txEnv* env);
bool issuances_hash(frameItem* dst, frameItem src, const txEnv* env);
bool tx_hash(frameItem* dst, frameItem src, const txEnv* env);
bool tapleaf_hash(frameItem* dst, frameItem src, const txEnv* env);
bool tappath_hash(frameItem* dst, frameItem src, const txEnv* env);
bool tap_env_hash(frameItem* dst, frameItem src, const txEnv* env);
bool sig_all_hash(frameItem* dst, frameItem src, const txEnv* env);

#endif
