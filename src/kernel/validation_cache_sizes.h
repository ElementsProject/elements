// Copyright (c) 2022 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_KERNEL_VALIDATION_CACHE_SIZES_H
#define BITCOIN_KERNEL_VALIDATION_CACHE_SIZES_H

#include <script/sigcache.h>

#include <cstddef>
#include <limits>

namespace kernel {
struct ValidationCacheSizes {
    size_t signature_cache_bytes{DEFAULT_MAX_SIG_CACHE_BYTES / 4};
    size_t script_execution_cache_bytes{DEFAULT_MAX_SIG_CACHE_BYTES / 4};
    // ELEMENTS
    size_t rangeproof_cache_bytes{DEFAULT_MAX_SIG_CACHE_BYTES / 4};
    size_t surjectionproof_execution_cache_bytes{DEFAULT_MAX_SIG_CACHE_BYTES / 4};
};
}

#endif // BITCOIN_KERNEL_VALIDATION_CACHE_SIZES_H
