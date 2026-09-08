// Copyright (c) 2026 The Elements developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.
//
// Tests for the Elements proof-cache entry computation (script/sigcache.cpp).
//
// These tests guard the collision-resistance and domain-separation properties
// of the cache keys used for the range-proof and surjection-proof caches.
// A cache entry is a *positive* verification result, so a key collision means
// accepting a proof without ever verifying it. The keys are computed with
// CHashWriter serialization, which length-prefixes every field, so two
// distinct argument tuples must never produce the same cache entry, and the
// two proof types must live in disjoint key spaces (domain separation).

#include <script/sigcache.h>
#include <test/util/setup_common.h>
#include <uint256.h>

#include <secp256k1_generator.h>

#include <boost/test/unit_test.hpp>

#include <vector>

BOOST_FIXTURE_TEST_SUITE(sigcache_tests, BasicTestingSetup)

// Two (proof, commitment) tuples whose concatenations would be byte-identical
// under the OLD raw-CSHA256 scheme (proof=AB commitment=CD  vs  proof=ABC
// commitment=D) must produce DIFFERENT cache entries under the new
// length-prefixing scheme. This is the core collision-resistance property.
BOOST_AUTO_TEST_CASE(rangeproof_entry_field_boundary)
{
    std::vector<unsigned char> proof_a   = {0xAA, 0xBB};
    std::vector<unsigned char> commit_a  = {0xCC, 0xDD};
    std::vector<unsigned char> asset_a   = {0x11};

    std::vector<unsigned char> proof_b   = {0xAA, 0xBB, 0xCC};
    std::vector<unsigned char> commit_b  = {0xDD};
    std::vector<unsigned char> asset_b   = {0x11};

    // Concatenations are identical: AA BB CC DD 11 == AA BB CC DD 11.
    // Under the old raw-Write scheme these collided; they must not now.
    CScript script;

    uint256 entry_a, entry_b;
    TestComputeEntryRangeProof(entry_a, proof_a, commit_a, asset_a, script);
    TestComputeEntryRangeProof(entry_b, proof_b, commit_b, asset_b, script);

    BOOST_CHECK(entry_a != entry_b);
}

// Same field-boundary property for the surjection-proof entry, varying the
// proof vs commitment split with a fixed hash.
BOOST_AUTO_TEST_CASE(surjectionproof_entry_field_boundary)
{
    uint256 hash = uint256S("0x1234");

    std::vector<unsigned char> proof_a  = {0x01, 0x02};
    std::vector<unsigned char> commit_a = {0x03, 0x04};

    std::vector<unsigned char> proof_b  = {0x01, 0x02, 0x03};
    std::vector<unsigned char> commit_b = {0x04};

    std::vector<secp256k1_generator> vTags; // empty tags — same in both cases

    uint256 entry_a, entry_b;
    TestComputeEntrySurjectionProof(entry_a, hash, proof_a, commit_a, vTags);
    TestComputeEntrySurjectionProof(entry_b, hash, proof_b, commit_b, vTags);

    BOOST_CHECK(entry_a != entry_b);
}

// The scriptPubKey is variable-length and part of the range-proof key. Two
// calls differing only in the script must produce different entries (an
// attacker must not be able to replay a cached proof against a different
// output script).
BOOST_AUTO_TEST_CASE(rangeproof_entry_script_sensitivity)
{
    std::vector<unsigned char> proof  = {0x01, 0x02, 0x03};
    std::vector<unsigned char> commit = {0x04, 0x05};
    std::vector<unsigned char> asset  = {0x06};

    CScript script_a;
    script_a << OP_TRUE;
    CScript script_b;
    script_b << OP_FALSE;

    uint256 entry_a, entry_b;
    TestComputeEntryRangeProof(entry_a, proof, commit, asset, script_a);
    TestComputeEntryRangeProof(entry_b, proof, commit, asset, script_b);

    BOOST_CHECK(entry_a != entry_b);
}

// Domain separation: a range-proof tuple and a surjection-proof tuple must
// never share a cache entry even when their byte content is arranged to look
// similar. The two caches use distinct salted midstates ('r' vs 's'), so the
// same logical content must hash differently across the two domains.
BOOST_AUTO_TEST_CASE(proof_caches_domain_separation)
{
    uint256 hash = uint256S("0xabcd");
    std::vector<unsigned char> proof  = {0x01, 0x02, 0x03};
    std::vector<unsigned char> commit = {0x04, 0x05, 0x06};
    std::vector<unsigned char> asset  = {0x07, 0x08};
    CScript script;
    std::vector<secp256k1_generator> vTags;

    uint256 range_entry, surj_entry;
    TestComputeEntryRangeProof(range_entry, proof, commit, asset, script);
    TestComputeEntrySurjectionProof(surj_entry, hash, proof, commit, vTags);

    // Different domains must not collide with each other's entries.
    BOOST_CHECK(range_entry != surj_entry);
}

// Determinism: the same tuple must always produce the same entry within a
// process (the salt is fixed per-process), which is what makes the cache
// usable at all.
BOOST_AUTO_TEST_CASE(entries_are_deterministic)
{
    std::vector<unsigned char> proof  = {0xde, 0xad};
    std::vector<unsigned char> commit = {0xbe, 0xef};
    std::vector<unsigned char> asset  = {0x00};
    CScript script;
    script << OP_RETURN;

    uint256 e1, e2;
    TestComputeEntryRangeProof(e1, proof, commit, asset, script);
    TestComputeEntryRangeProof(e2, proof, commit, asset, script);
    BOOST_CHECK(e1 == e2);

    uint256 hash = uint256S("0x99");
    std::vector<secp256k1_generator> vTags;
    uint256 s1, s2;
    TestComputeEntrySurjectionProof(s1, hash, proof, commit, vTags);
    TestComputeEntrySurjectionProof(s2, hash, proof, commit, vTags);
    BOOST_CHECK(s1 == s2);
}

// vTags sensitivity: two surjection-proof calls that differ only in vTags
// must produce different cache entries (otherwise an attacker could cause
// a cache hit for a proof verified with different input tags).
BOOST_AUTO_TEST_CASE(surjectionproof_entry_vtags_sensitivity)
{
    uint256 hash = uint256S("0xdeadbeef");
    std::vector<unsigned char> proof  = {0x01, 0x02};
    std::vector<unsigned char> commit = {0x03, 0x04};

    secp256k1_generator gen_a, gen_b;
    // Fill with distinct byte patterns.
    memset(gen_a.data, 0xAA, sizeof(gen_a.data));
    memset(gen_b.data, 0xBB, sizeof(gen_b.data));

    std::vector<secp256k1_generator> vTags_a = {gen_a};
    std::vector<secp256k1_generator> vTags_b = {gen_b};

    uint256 entry_a, entry_b;
    TestComputeEntrySurjectionProof(entry_a, hash, proof, commit, vTags_a);
    TestComputeEntrySurjectionProof(entry_b, hash, proof, commit, vTags_b);

    BOOST_CHECK(entry_a != entry_b);
}

BOOST_AUTO_TEST_SUITE_END()
