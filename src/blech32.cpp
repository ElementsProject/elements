// Copyright (c) 2017 Pieter Wuille
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <blech32.h>

namespace blech32
{

typedef std::vector<uint8_t> data;

/** The Bech32 character set for encoding. */
const char* CHARSET = "qpzry9x8gf2tvdw0s3jn54khce6mua7l";

/** The Bech32 character set for decoding. */
const int8_t CHARSET_REV[128] = {
    -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
    -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
    -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
    15, -1, 10, 17, 21, 20, 26, 30,  7,  5, -1, -1, -1, -1, -1, -1,
    -1, 29, -1, 24, 13, 25,  9,  8, 23, -1, 18, 22, 31, 27, 19, -1,
     1,  0,  3, 16, 11, 28, 12, 14,  6,  4,  2, -1, -1, -1, -1, -1,
    -1, 29, -1, 24, 13, 25,  9,  8, 23, -1, 18, 22, 31, 27, 19, -1,
     1,  0,  3, 16, 11, 28, 12, 14,  6,  4,  2, -1, -1, -1, -1, -1
};

/** Concatenate two byte arrays. */
data Cat(data x, const data& y)
{
    x.insert(x.end(), y.begin(), y.end());
    return x;
}

/** This function will compute what 12 5-bit values to XOR into the last 12 input values, in order to
 *  make the checksum 0. These 12 values are packed together in a single 60-bit integer. The higher
 *  bits correspond to earlier values. */
uint64_t PolyMod(const data& v)
{
    // The input is interpreted as a list of coefficients of a polynomial over F = GF(32), with an
    // implicit 1 in front. If the input is [v0,v1,v2,v3,v4], that polynomial is v(x) =
    // 1*x^5 + v0*x^4 + v1*x^3 + v2*x^2 + v3*x + v4. The implicit 1 guarantees that
    // [v0,v1,v2,...] has a distinct checksum from [0,v0,v1,v2,...].

    // The output is a 60-bit integer whose 5-bit groups are the coefficients of the remainder of
    // v(x) mod g(x), where g(x) is the Blech32 generator,
    // x^12 + {31}x^10 + {10}x^9 + {18}x^8 + {31}x^7 + {14}x^6
    //      +  {18}x^5 + {23}x^3 + {22}x^2 +  {4}x   +  {6}   . g(x) is chosen in such a way
    // that the resulting code is a BCH code, guaranteeing detection of up to ??? errors within a
    // window of ??? characters. Among the various possible BCH codes, one was selected to in
    // fact guarantee detection of up to ??? errors within a window of ??? characters.

    // Note that the coefficients are elements of GF(32), here represented as decimal numbers
    // between {}. In this finite field, addition is just XOR of the corresponding numbers. For
    // example, {27} + {13} = {27 ^ 13} = {22}. Multiplication is more complicated, and requires
    // treating the bits of values themselves as coefficients of a polynomial over a smaller field,
    // GF(2), and multiplying those polynomials mod a^5 + a^3 + 1. For example, {5} * {26} =
    // (a^2 + 1) * (a^4 + a^3 + a) = (a^4 + a^3 + a) * a^2 + (a^4 + a^3 + a) = a^6 + a^5 + a^4 + a
    // = a^3 + 1 (mod a^5 + a^3 + 1) = {9}.

    // During the course of the loop below, `c` contains the bitpacked coefficients of the
    // polynomial constructed from just the values of v that were processed so far, mod g(x). In
    // the above example, `c` initially corresponds to 1 mod (x), and after processing 2 inputs of
    // v, it corresponds to x^2 + v0*x + v1 mod g(x). As 1 mod g(x) = 1, that is the starting value
    // for `c`.
    uint64_t c = 1;
    for (const auto v_i : v) {
        // We want to update `c` to correspond to a polynomial with one extra term. If the initial
        // value of `c` consists of the coefficients of c(x) = f(x) mod g(x), we modify it to
        // correspond to c'(x) = (f(x) * x + v_i) mod g(x), where v_i is the next input to
        // process. Simplifying:
        // c'(x) = (f(x) * x + v_i) mod g(x)
        //         ((f(x) mod g(x)) * x + v_i) mod g(x)
        //         (c(x) * x + v_i) mod g(x)
        // If c(x) = c0*x^11 + c1*x^10 + c2*x^9 + c3*x^8 + c4*x^7 + c5*x^6 +
        //          c6*x^5 + c7*x^4 + c8*x^3 + c9*x^2 + c10*x + c11, we want to compute
        // c'(x) = (c0*x^11 + c1*x^10 + c2*x^9 + c3*x^8 + c4*x^7 + c5*x^6 +
        //          c6*x^5 + c7*x^4 + c8*x^3 + c9*x^2 + c10*x + c11) * x + v_i mod g(x)
        //       = c0*x^12 + c1*x^11 + c2*x^10 + c3*x^9 + c4*x^8 + c5*x^7 +
        //         c6*x^6 + c7*x^5 + c8*x^4 + c9*x^3 + c10*x^2 + c11*x + v_i mod g(x)
        //       = c0*(x^12 mod g(x)) + c1*x^11 + c2*x^10 + c3*x^9 + c4*x^8 + c5*x^7 +
        //         c6*x^6 + c7*x^5 + c8*x^4 + c9*x^3 + c10*x^2 + c11*x + v_i
        // If we call (x^12 mod g(x)) = k(x), this can be written as
        // c'(x) = (c1*x^11 + c2*x^10 + c3*x^9 + c4*x^8 + c5*x^7 + c6*x^6 +
        //             c7*x^5 + c8*x^4 + c9*x^3 + c10*x^2 + c11 * x + v_i) + c0*k(x)

        // First, determine the value of c0:
        uint8_t c0 = c >> 55; // BLECH32: 25->55

        // Then compute c1*x^11 + c2*x^10 + c3*x^9 + c4*x^8 + c5*x^7 + c6*x^6 +
        //  c7*x^5 + c8*x^4 + c9*x^3 + c10*x^2 + c11 * x + v_i:
        c = ((c & 0x7fffffffffffff) << 5) ^ v_i; // BLECH32: 0x1ffffff->0x7fffffffffffff

        // Finally, for each set bit n in c0, conditionally add {2^n}k(x):
        if (c0 & 1)  c ^= 0x7d52fba40bd886; // BLECH32:     k(x) = {31}x^10 + {10}x^9 + {18}x^8 + {31}x^7 + {14}x^6 + {18}x^5 + {23}x^3 + {22}x^2 +  {4}x +  {6}
        if (c0 & 2)  c ^= 0x5e8dbf1a03950c; // BLECH32:  {2}k(x) = {23}x^10 + {20}x^9 + {13}x^8 + {23}x^7 + {28}x^6 + {13}x^5 +  {7}x^3 +  {5}x^2 +  {8}x + {12}
        if (c0 & 4)  c ^= 0x1c3a3c74072a18; // BLECH32:  {4}k(x) =  {7}x^10 +  {1}x^9 + {26}x^8 +  {7}x^7 + {17}x^6 + {26}x^5 + {14}x^3 + {10}x^2 + {16}x + {24}
        if (c0 & 8)  c ^= 0x385d72fa0e5139; // BLECH32:  {8}k(x) = {14}x^10 +  {2}x^9 + {29}x^8 + {14}x^7 + {11}x^6 + {29}x^5 + {28}x^3 + {20}x^2 +  {9}x + {25}
        if (c0 & 16) c ^= 0x7093e5a608865b; // BLECH32: {16}k(x) = {28}x^10 +  {4}x^9 + {19}x^8 + {28}x^7 + {22}x^6 + {19}x^5 + {17}x^3 +  {1}x^2 + {18}x + {27}
    }
    return c;
}

/** Convert to lower case. */
inline unsigned char LowerCase(unsigned char c)
{
    return (c >= 'A' && c <= 'Z') ? (c - 'A') + 'a' : c;
}

/** Expand a HRP for use in checksum computation. */
data ExpandHRP(const std::string& hrp)
{
    data ret;
    ret.reserve(hrp.size() + 90);
    ret.resize(hrp.size() * 2 + 1);
    for (size_t i = 0; i < hrp.size(); ++i) {
        unsigned char c = hrp[i];
        ret[i] = c >> 5;
        ret[i + hrp.size() + 1] = c & 0x1f;
    }
    ret[hrp.size()] = 0;
    return ret;
}

/** Verify a checksum. */
bool VerifyChecksum(const std::string& hrp, const data& values)
{
    // PolyMod computes what value to xor into the final values to make the checksum 0. However,
    // if we required that the checksum was 0, it would be the case that appending a 0 to a valid
    // list of values would result in a new valid list. For that reason, Blech32 requires the
    // resulting checksum to be 1 instead.
    return PolyMod(Cat(ExpandHRP(hrp), values)) == 1;
}

/** Create a checksum. */
data CreateChecksum(const std::string& hrp, const data& values)
{
    data enc = Cat(ExpandHRP(hrp), values);
    enc.resize(enc.size() + 12); // BLECH32: Append 6->12 zeroes
    uint64_t mod = PolyMod(enc) ^ 1; // Determine what to XOR into those 12 zeroes.
    data ret(12); // BLECH32: 6->12
    for (size_t i = 0; i < 12; ++i) { // BLECH32: 6->12
        // Convert the 5-bit groups in mod to checksum values.
        ret[i] = (mod >> (5 * (11 - i))) & 31; // BLECH32: 5->11
    }
    return ret;
}

/** Encode a Blech32 string. */
std::string Encode(const std::string& hrp, const data& values) {
    data checksum = CreateChecksum(hrp, values);
    data combined = Cat(values, checksum);
    std::string ret = hrp + '1';
    ret.reserve(ret.size() + combined.size());
    for (const auto c : combined) {
        ret += CHARSET[c];
    }
    return ret;
}

/** Decode a Blech32 string. */
std::pair<std::string, data> Decode(const std::string& str) {
    bool lower = false, upper = false;
    for (size_t i = 0; i < str.size(); ++i) {
        unsigned char c = str[i];
        if (c >= 'a' && c <= 'z') lower = true;
        else if (c >= 'A' && c <= 'Z') upper = true;
        else if (c < 33 || c > 126) return {};
    }
    if (lower && upper) return {};
    size_t pos = str.rfind('1');
    if (str.size() > 1000 || pos == str.npos || pos == 0 || pos + 13 > str.size()) { // BLECH32: 90->1000, 7->13
        return {};
    }
    data values(str.size() - 1 - pos);
    for (size_t i = 0; i < str.size() - 1 - pos; ++i) {
        unsigned char c = str[i + pos + 1];
        int8_t rev = CHARSET_REV[c];

        if (rev == -1) {
            return {};
        }
        values[i] = rev;
    }
    std::string hrp;
    for (size_t i = 0; i < pos; ++i) {
        hrp += LowerCase(str[i]);
    }
    if (!VerifyChecksum(hrp, values)) {
        return {};
    }
    return {hrp, data(values.begin(), values.end() - 12)}; // BLECH32: 6->12
}

} // namespace blech32
