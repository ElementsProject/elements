This directory contains a modified copy of the libsecp256k1 branch `c083cc6e52a3ab749f5451de9c515d75897649c6` from <https://github.com/bitcoin-core/secp256k1/commit/c083cc6e52a3ab749f5451de9c515d75897649c6>.
In general, the files in this directory should be compared with the corresponding files in the `src` directory from libsecp256k1.
There are some exceptions however:

* `secp256k1.h` should be compared with `include/secp256k1.h`.
* `secp256k1_impl.h` should be compared with `src/secp256k1.c`.
* `extrakeys.h` should be compared with `include/secp256k1_extrakeys.h`.
* `extrakeys_impl.h` should be compared with `src/modules/extrakeys/main_impl.h`.
* `schnorrsig.h` should be compared with `include/secp256k1_schnorrsig.h`.
* `schnorrsig_impl.h` should be compared with `src/modules/schnorrsig/main_impl.h`.


Our use of libsecp256k1 for various jets requires access to the internal functions that are not exposed by the their API, so we cannot use libsecp256k1's normal interface.
Furthermore, because Simplicity has no abstract data types, the specific details of the representation of field and group elements computed by jetted functions ends up being consensus critical.
Therefore, even if libsecp256k1's interface exposed the functionality we needed, we still wouldn't be able perform libsecp256k1 version upgrades because different versions of libsecp256k1 do not guarantee that their functions won't change the representation of computed field and group elements.
Even libsecp256k1's configuration options, including `ECMULT_WINDOW_SIZE`, all can affect the representation of the computed group elements.
Therefore we need to fix these options to specific values.

Simplicity computations are on public data and therefore we do not jet functions that manipulate private or secret data.
In particular, we only need to jet variable-time algorithms when there is a choice of variable-time or constant-time algorithms.

In incorporating the libsecp256k1 library into the Simplicity library, there is a tension between making minimal changes to the library versus removing configuration options and other code that, if they were activated, could cause consensus incompatible changes in functionality.
Because we will not be able to easily migrate to newer versions of libsecp256k1 anyways, we have take a heavy-handed approach to trimming unused configuration options, dead code, functions specific to working with secret data, etc.
In some cases we have made minor code changes:

* Some casts have been slightly modified to remove warnings caused by our choice of GCC flags.
* The definition of `ALIGNMENT` has been modified to take advantage of C11's `max_align_t`.
* `secp256k1_fe_sqrt` has been modified to call `secp256k1_fe_equal_var` (as `secp256k1_fe_equal` has been removed).  The function has been renamed to `secp256k1_fe_sqrt_var` and similar for other indirect callers.
* The uses of secp256k1's `hash.h` for Schnorr signatures has been replaced with calls to Simplicity's internal `sha256.h` implementation.  This removes the duplication of functionality and replaces the non-portable use of the `WORDS_BIGENDIAN` flag in `hash_impl.h` with our portable implementation.
* `checked_malloc` and `checked_realloc` have been removed along with any functions that called themm.
* The constant variable `SECP256K1_ECMULT_CONTEXT_PREALLOCATED_SIZE` has been replaced with a macro so that it can be used as a constant expression for static array allocations.
* `ARG_CHECK` has been replaced by `VERIFY_CHECK` so that callbacks can be removed.
* Callbacks have been removed.
* `secp256k1_context` has been removed and replaced by `secp256k1_ecmult_context` in those few places where anything is needed.  No other parts of the of `secp256k1_context` are used in Simplicity jets.
