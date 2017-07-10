// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2016 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "interpreter.h"

#include <secp256k1.h>

#include "primitives/bitcoin/transaction.h"
#include "primitives/bitcoin/merkleblock.h"
#include "crypto/ripemd160.h"
#include "crypto/sha1.h"
#include "crypto/sha256.h"
#include "crypto/hmac_sha256.h"
#include "merkleblock.h"
#include "pow.h"
#include "pubkey.h"
#include "script/script.h"
#include "script/standard.h"
#include "streams.h"
#include "uint256.h"
#include "utilstrencodings.h"
#include "util.h"

#ifndef BITCOIN_SCRIPT_NO_CALLRPC
#include "callrpc.h"
#endif

using namespace std;

typedef vector<unsigned char> valtype;

namespace {

static secp256k1_context *secp256k1_ctx;

class CSecp256k1Init {
public:
    CSecp256k1Init() {
        secp256k1_ctx = secp256k1_context_create(SECP256K1_CONTEXT_VERIFY);
    }
    ~CSecp256k1Init() {
        secp256k1_context_destroy(secp256k1_ctx);
    }
};
static CSecp256k1Init instance_of_csecp256k1;

inline bool set_success(ScriptError* ret)
{
    if (ret)
        *ret = SCRIPT_ERR_OK;
    return true;
}

inline bool set_error(ScriptError* ret, const ScriptError serror)
{
    if (ret)
        *ret = serror;
    return false;
}

} // anon namespace

bool CastToBool(const valtype& vch)
{
    for (unsigned int i = 0; i < vch.size(); i++)
    {
        if (vch[i] != 0)
        {
            // Can be negative zero
            if (i == vch.size()-1 && vch[i] == 0x80)
                return false;
            return true;
        }
    }
    return false;
}

/**
 * Script is a stack machine (like Forth) that evaluates a predicate
 * returning a bool indicating valid or not.  There are no loops.
 */
#define stacktop(i)  (stack.at(stack.size()+(i)))
#define altstacktop(i)  (altstack.at(altstack.size()+(i)))
static inline void popstack(vector<valtype>& stack)
{
    if (stack.empty())
        throw runtime_error("popstack(): stack empty");
    stack.pop_back();
}

bool static IsCompressedOrUncompressedPubKey(const valtype &vchPubKey) {
    if (vchPubKey.size() < 33) {
        //  Non-canonical public key: too short
        return false;
    }
    if (vchPubKey[0] == 0x04) {
        if (vchPubKey.size() != 65) {
            //  Non-canonical public key: invalid length for uncompressed key
            return false;
        }
    } else if (vchPubKey[0] == 0x02 || vchPubKey[0] == 0x03) {
        if (vchPubKey.size() != 33) {
            //  Non-canonical public key: invalid length for compressed key
            return false;
        }
    } else {
        //  Non-canonical public key: neither compressed nor uncompressed
        return false;
    }
    return true;
}

bool static IsCompressedPubKey(const valtype &vchPubKey) {
    if (vchPubKey.size() != 33) {
        //  Non-canonical public key: invalid length for compressed key
        return false;
    }
    if (vchPubKey[0] != 0x02 && vchPubKey[0] != 0x03) {
        //  Non-canonical public key: invalid prefix for compressed key
        return false;
    }
    return true;
}

/**
 * A canonical signature exists of: <30> <total len> <02> <len R> <R> <02> <len S> <S> <hashtype>
 * Where R and S are not negative (their first byte has its highest bit not set), and not
 * excessively padded (do not start with a 0 byte, unless an otherwise negative number follows,
 * in which case a single 0 byte is necessary and even required).
 * 
 * See https://bitcointalk.org/index.php?topic=8392.msg127623#msg127623
 *
 * This function is consensus-critical since BIP66.
 */
bool static IsValidSignatureEncoding(const std::vector<unsigned char> &sig) {
    // Format: 0x30 [total-length] 0x02 [R-length] [R] 0x02 [S-length] [S] [sighash]
    // * total-length: 1-byte length descriptor of everything that follows,
    //   excluding the sighash byte.
    // * R-length: 1-byte length descriptor of the R value that follows.
    // * R: arbitrary-length big-endian encoded R value. It must use the shortest
    //   possible encoding for a positive integers (which means no null bytes at
    //   the start, except a single one when the next byte has its highest bit set).
    // * S-length: 1-byte length descriptor of the S value that follows.
    // * S: arbitrary-length big-endian encoded S value. The same rules apply.
    // * sighash: 1-byte value indicating what data is hashed (not part of the DER
    //   signature)

    // Minimum and maximum size constraints.
    if (sig.size() < 9) return false;
    if (sig.size() > 73) return false;

    // A signature is of type 0x30 (compound).
    if (sig[0] != 0x30) return false;

    // Make sure the length covers the entire signature.
    if (sig[1] != sig.size() - 3) return false;

    // Extract the length of the R element.
    unsigned int lenR = sig[3];

    // Make sure the length of the S element is still inside the signature.
    if (5 + lenR >= sig.size()) return false;

    // Extract the length of the S element.
    unsigned int lenS = sig[5 + lenR];

    // Verify that the length of the signature matches the sum of the length
    // of the elements.
    if ((size_t)(lenR + lenS + 7) != sig.size()) return false;
 
    // Check whether the R element is an integer.
    if (sig[2] != 0x02) return false;

    // Zero-length integers are not allowed for R.
    if (lenR == 0) return false;

    // Negative numbers are not allowed for R.
    if (sig[4] & 0x80) return false;

    // Null bytes at the start of R are not allowed, unless R would
    // otherwise be interpreted as a negative number.
    if (lenR > 1 && (sig[4] == 0x00) && !(sig[5] & 0x80)) return false;

    // Check whether the S element is an integer.
    if (sig[lenR + 4] != 0x02) return false;

    // Zero-length integers are not allowed for S.
    if (lenS == 0) return false;

    // Negative numbers are not allowed for S.
    if (sig[lenR + 6] & 0x80) return false;

    // Null bytes at the start of S are not allowed, unless S would otherwise be
    // interpreted as a negative number.
    if (lenS > 1 && (sig[lenR + 6] == 0x00) && !(sig[lenR + 7] & 0x80)) return false;

    return true;
}

bool static IsLowDERSignature(const valtype &vchSig, ScriptError* serror) {
    if (!IsValidSignatureEncoding(vchSig)) {
        return set_error(serror, SCRIPT_ERR_SIG_DER);
    }
    std::vector<unsigned char> vchSigCopy(vchSig.begin(), vchSig.begin() + vchSig.size() - 1);
    if (!CPubKey::CheckLowS(vchSigCopy)) {
        return set_error(serror, SCRIPT_ERR_SIG_HIGH_S);
    }
    return true;
}

bool static IsDefinedHashtypeSignature(const valtype &vchSig) {
    if (vchSig.size() == 0) {
        return false;
    }
    unsigned char nHashType = vchSig[vchSig.size() - 1] & (~(SIGHASH_ANYONECANPAY));
    if (nHashType < SIGHASH_ALL || nHashType > SIGHASH_SINGLE)
        return false;

    return true;
}

bool CheckSignatureEncoding(const vector<unsigned char> &vchSig, unsigned int flags, ScriptError* serror) {
    // Empty signature. Not strictly DER encoded, but allowed to provide a
    // compact way to provide an invalid signature for use with CHECK(MULTI)SIG
    if (vchSig.size() == 0) {
        return true;
    }
    if ((flags & (SCRIPT_VERIFY_DERSIG | SCRIPT_VERIFY_LOW_S | SCRIPT_VERIFY_STRICTENC)) != 0 && !IsValidSignatureEncoding(vchSig)) {
        return set_error(serror, SCRIPT_ERR_SIG_DER);
    } else if ((flags & SCRIPT_VERIFY_LOW_S) != 0 && !IsLowDERSignature(vchSig, serror)) {
        // serror is set
        return false;
    } else if ((flags & SCRIPT_VERIFY_STRICTENC) != 0 && !IsDefinedHashtypeSignature(vchSig)) {
        return set_error(serror, SCRIPT_ERR_SIG_HASHTYPE);
    }
    return true;
}

bool static CheckPubKeyEncoding(const valtype &vchPubKey, unsigned int flags, const SigVersion &sigversion, ScriptError* serror) {
    if ((flags & SCRIPT_VERIFY_STRICTENC) != 0 && !IsCompressedOrUncompressedPubKey(vchPubKey)) {
        return set_error(serror, SCRIPT_ERR_PUBKEYTYPE);
    }
    // Only compressed keys are accepted in segwit
    if ((flags & SCRIPT_VERIFY_WITNESS_PUBKEYTYPE) != 0 && sigversion == SIGVERSION_WITNESS_V0 && !IsCompressedPubKey(vchPubKey)) {
        return set_error(serror, SCRIPT_ERR_WITNESS_PUBKEYTYPE);
    }
    return true;
}

bool static CheckMinimalPush(const valtype& data, opcodetype opcode) {
    if (data.size() == 0) {
        // Could have used OP_0.
        return opcode == OP_0;
    } else if (data.size() == 1 && data[0] >= 1 && data[0] <= 16) {
        // Could have used OP_1 .. OP_16.
        return opcode == OP_1 + (data[0] - 1);
    } else if (data.size() == 1 && data[0] == 0x81) {
        // Could have used OP_1NEGATE.
        return opcode == OP_1NEGATE;
    } else if (data.size() <= 75) {
        // Could have used a direct push (opcode indicating number of bytes pushed + those bytes).
        return opcode == data.size();
    } else if (data.size() <= 255) {
        // Could have used OP_PUSHDATA.
        return opcode == OP_PUSHDATA1;
    } else if (data.size() <= 65535) {
        // Could have used OP_PUSHDATA2.
        return opcode == OP_PUSHDATA2;
    }
    return true;
}

bool static WithdrawProofReadStackItem(const vector<valtype>& stack, const bool fRequireMinimal, int *stackOffset, valtype& read)
{
    if (stack.size() < size_t(-(*stackOffset)))
        return false;
    int pushCount = CScriptNum(stacktop(*stackOffset), fRequireMinimal).getint();
    if (pushCount < 0 || pushCount > 2000 || stack.size() < size_t(-(*stackOffset) + pushCount))
        return false;
    (*stackOffset)--;

    read.reserve(pushCount > 1 ? pushCount * 520 : 0);
    for (int i = pushCount - 1; i >= 0; i--) {
        if (i != 0 && stacktop((*stackOffset) - i).size() != 520)
            return false;
        const valtype& stackElem = stacktop((*stackOffset) - i);
        read.insert(read.end(), stackElem.begin(), stackElem.end());
    }
    (*stackOffset) -= pushCount;
    return true;
}

bool EvalScript(vector<vector<unsigned char> >& stack, const CScript& script, unsigned int flags, const BaseSignatureChecker& checker, SigVersion sigversion, ScriptError* serror)
{
    static const CScriptNum bnZero(0);
    static const CScriptNum bnOne(1);
    static const CScriptNum bnFalse(0);
    static const CScriptNum bnTrue(1);
    static const valtype vchFalse(0);
    static const valtype vchZero(0);
    static const valtype vchTrue(1, 1);

    CScript::const_iterator pc = script.begin();
    CScript::const_iterator pend = script.end();
    CScript::const_iterator pbegincodehash = script.begin();
    opcodetype opcode;
    valtype vchPushValue;
    vector<bool> vfExec;
    vector<valtype> altstack;
    set_error(serror, SCRIPT_ERR_UNKNOWN_ERROR);
    if (script.size() > MAX_SCRIPT_SIZE)
        return set_error(serror, SCRIPT_ERR_SCRIPT_SIZE);
    int nOpCount = 0;
    bool fRequireMinimal = (flags & SCRIPT_VERIFY_MINIMALDATA) != 0;

    try
    {
        while (pc < pend)
        {
            bool fExec = !count(vfExec.begin(), vfExec.end(), false);

            //
            // Read instruction
            //
            if (!script.GetOp(pc, opcode, vchPushValue))
                return set_error(serror, SCRIPT_ERR_BAD_OPCODE);
            if (vchPushValue.size() > MAX_SCRIPT_ELEMENT_SIZE)
                return set_error(serror, SCRIPT_ERR_PUSH_SIZE);

            // Note how OP_RESERVED does not count towards the opcode limit.
            if (opcode > OP_16 && ++nOpCount > MAX_OPS_PER_SCRIPT)
                return set_error(serror, SCRIPT_ERR_OP_COUNT);

            if (opcode == OP_2MUL ||
                opcode == OP_2DIV ||
                opcode == OP_MUL ||
                opcode == OP_DIV ||
                opcode == OP_MOD)
                return set_error(serror, SCRIPT_ERR_DISABLED_OPCODE); // Disabled opcodes.

            if (fExec && 0 <= opcode && opcode <= OP_PUSHDATA4) {
                if (fRequireMinimal && !CheckMinimalPush(vchPushValue, opcode)) {
                    return set_error(serror, SCRIPT_ERR_MINIMALDATA);
                }
                stack.push_back(vchPushValue);
            } else if (fExec || (OP_IF <= opcode && opcode <= OP_ENDIF))
            switch (opcode)
            {
                //
                // Push value
                //
                case OP_1NEGATE:
                case OP_1:
                case OP_2:
                case OP_3:
                case OP_4:
                case OP_5:
                case OP_6:
                case OP_7:
                case OP_8:
                case OP_9:
                case OP_10:
                case OP_11:
                case OP_12:
                case OP_13:
                case OP_14:
                case OP_15:
                case OP_16:
                {
                    // ( -- value)
                    CScriptNum bn((int)opcode - (int)(OP_1 - 1));
                    stack.push_back(bn.getvch());
                    // The result of these opcodes should always be the minimal way to push the data
                    // they push, so no need for a CheckMinimalPush here.
                }
                break;


                //
                // Control
                //
                case OP_NOP:
                    break;

                case OP_CHECKLOCKTIMEVERIFY:
                {
                    if (!(flags & SCRIPT_VERIFY_CHECKLOCKTIMEVERIFY)) {
                        // not enabled; treat as a NOP2
                        if (flags & SCRIPT_VERIFY_DISCOURAGE_UPGRADABLE_NOPS) {
                            return set_error(serror, SCRIPT_ERR_DISCOURAGE_UPGRADABLE_NOPS);
                        }
                        break;
                    }

                    if (stack.size() < 1)
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);

                    // Note that elsewhere numeric opcodes are limited to
                    // operands in the range -2**31+1 to 2**31-1, however it is
                    // legal for opcodes to produce results exceeding that
                    // range. This limitation is implemented by CScriptNum's
                    // default 4-byte limit.
                    //
                    // If we kept to that limit we'd have a year 2038 problem,
                    // even though the nLockTime field in transactions
                    // themselves is uint32 which only becomes meaningless
                    // after the year 2106.
                    //
                    // Thus as a special case we tell CScriptNum to accept up
                    // to 5-byte bignums, which are good until 2**39-1, well
                    // beyond the 2**32-1 limit of the nLockTime field itself.
                    const CScriptNum nLockTime(stacktop(-1), fRequireMinimal, 5);

                    // In the rare event that the argument may be < 0 due to
                    // some arithmetic being done first, you can always use
                    // 0 MAX CHECKLOCKTIMEVERIFY.
                    if (nLockTime < 0)
                        return set_error(serror, SCRIPT_ERR_NEGATIVE_LOCKTIME);

                    // Actually compare the specified lock time with the transaction.
                    if (!checker.CheckLockTime(nLockTime))
                        return set_error(serror, SCRIPT_ERR_UNSATISFIED_LOCKTIME);

                    break;
                }

                case OP_CHECKSEQUENCEVERIFY:
                {
                    if (!(flags & SCRIPT_VERIFY_CHECKSEQUENCEVERIFY)) {
                        // not enabled; treat as a NOP3
                        if (flags & SCRIPT_VERIFY_DISCOURAGE_UPGRADABLE_NOPS) {
                            return set_error(serror, SCRIPT_ERR_DISCOURAGE_UPGRADABLE_NOPS);
                        }
                        break;
                    }

                    if (stack.size() < 1)
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);

                    // nSequence, like nLockTime, is a 32-bit unsigned integer
                    // field. See the comment in CHECKLOCKTIMEVERIFY regarding
                    // 5-byte numeric operands.
                    const CScriptNum nSequence(stacktop(-1), fRequireMinimal, 5);

                    // In the rare event that the argument may be < 0 due to
                    // some arithmetic being done first, you can always use
                    // 0 MAX CHECKSEQUENCEVERIFY.
                    if (nSequence < 0)
                        return set_error(serror, SCRIPT_ERR_NEGATIVE_LOCKTIME);

                    // To provide for future soft-fork extensibility, if the
                    // operand has the disabled lock-time flag set,
                    // CHECKSEQUENCEVERIFY behaves as a NOP.
                    if ((nSequence & CTxIn::SEQUENCE_LOCKTIME_DISABLE_FLAG) != 0)
                        break;

                    // Compare the specified sequence number with the input.
                    if (!checker.CheckSequence(nSequence))
                        return set_error(serror, SCRIPT_ERR_UNSATISFIED_LOCKTIME);

                    break;
                }

                case OP_NOP1: case OP_NOP5:
                case OP_NOP6: case OP_NOP7: case OP_NOP8: case OP_NOP9: case OP_NOP10:
                {
                    if (flags & SCRIPT_VERIFY_DISCOURAGE_UPGRADABLE_NOPS)
                        return set_error(serror, SCRIPT_ERR_DISCOURAGE_UPGRADABLE_NOPS);
                }
                break;

                case OP_IF:
                case OP_NOTIF:
                {
                    // <expression> if [statements] [else [statements]] endif
                    bool fValue = false;
                    if (fExec)
                    {
                        if (stack.size() < 1)
                            return set_error(serror, SCRIPT_ERR_UNBALANCED_CONDITIONAL);
                        valtype& vch = stacktop(-1);
                        if (sigversion == SIGVERSION_WITNESS_V0 && (flags & SCRIPT_VERIFY_MINIMALIF)) {
                            if (vch.size() > 1)
                                return set_error(serror, SCRIPT_ERR_MINIMALIF);
                            if (vch.size() == 1 && vch[0] != 1)
                                return set_error(serror, SCRIPT_ERR_MINIMALIF);
                        }
                        fValue = CastToBool(vch);
                        if (opcode == OP_NOTIF)
                            fValue = !fValue;
                        popstack(stack);
                    }
                    vfExec.push_back(fValue);
                }
                break;

                case OP_ELSE:
                {
                    if (vfExec.empty())
                        return set_error(serror, SCRIPT_ERR_UNBALANCED_CONDITIONAL);
                    vfExec.back() = !vfExec.back();
                }
                break;

                case OP_ENDIF:
                {
                    if (vfExec.empty())
                        return set_error(serror, SCRIPT_ERR_UNBALANCED_CONDITIONAL);
                    vfExec.pop_back();
                }
                break;

                case OP_VERIFY:
                {
                    // (true -- ) or
                    // (false -- false) and return
                    if (stack.size() < 1)
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);
                    bool fValue = CastToBool(stacktop(-1));
                    if (fValue)
                        popstack(stack);
                    else
                        return set_error(serror, SCRIPT_ERR_VERIFY);
                }
                break;

                case OP_RETURN:
                {
                    return set_error(serror, SCRIPT_ERR_OP_RETURN);
                }
                break;


                //
                // Stack ops
                //
                case OP_TOALTSTACK:
                {
                    if (stack.size() < 1)
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);
                    altstack.push_back(stacktop(-1));
                    popstack(stack);
                }
                break;

                case OP_FROMALTSTACK:
                {
                    if (altstack.size() < 1)
                        return set_error(serror, SCRIPT_ERR_INVALID_ALTSTACK_OPERATION);
                    stack.push_back(altstacktop(-1));
                    popstack(altstack);
                }
                break;

                case OP_2DROP:
                {
                    // (x1 x2 -- )
                    if (stack.size() < 2)
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);
                    popstack(stack);
                    popstack(stack);
                }
                break;

                case OP_2DUP:
                {
                    // (x1 x2 -- x1 x2 x1 x2)
                    if (stack.size() < 2)
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);
                    valtype vch1 = stacktop(-2);
                    valtype vch2 = stacktop(-1);
                    stack.push_back(vch1);
                    stack.push_back(vch2);
                }
                break;

                case OP_3DUP:
                {
                    // (x1 x2 x3 -- x1 x2 x3 x1 x2 x3)
                    if (stack.size() < 3)
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);
                    valtype vch1 = stacktop(-3);
                    valtype vch2 = stacktop(-2);
                    valtype vch3 = stacktop(-1);
                    stack.push_back(vch1);
                    stack.push_back(vch2);
                    stack.push_back(vch3);
                }
                break;

                case OP_2OVER:
                {
                    // (x1 x2 x3 x4 -- x1 x2 x3 x4 x1 x2)
                    if (stack.size() < 4)
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);
                    valtype vch1 = stacktop(-4);
                    valtype vch2 = stacktop(-3);
                    stack.push_back(vch1);
                    stack.push_back(vch2);
                }
                break;

                case OP_2ROT:
                {
                    // (x1 x2 x3 x4 x5 x6 -- x3 x4 x5 x6 x1 x2)
                    if (stack.size() < 6)
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);
                    valtype vch1 = stacktop(-6);
                    valtype vch2 = stacktop(-5);
                    stack.erase(stack.end()-6, stack.end()-4);
                    stack.push_back(vch1);
                    stack.push_back(vch2);
                }
                break;

                case OP_2SWAP:
                {
                    // (x1 x2 x3 x4 -- x3 x4 x1 x2)
                    if (stack.size() < 4)
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);
                    swap(stacktop(-4), stacktop(-2));
                    swap(stacktop(-3), stacktop(-1));
                }
                break;

                case OP_IFDUP:
                {
                    // (x - 0 | x x)
                    if (stack.size() < 1)
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);
                    valtype vch = stacktop(-1);
                    if (CastToBool(vch))
                        stack.push_back(vch);
                }
                break;

                case OP_DEPTH:
                {
                    // -- stacksize
                    CScriptNum bn(stack.size());
                    stack.push_back(bn.getvch());
                }
                break;

                case OP_DROP:
                {
                    // (x -- )
                    if (stack.size() < 1)
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);
                    popstack(stack);
                }
                break;

                case OP_DUP:
                {
                    // (x -- x x)
                    if (stack.size() < 1)
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);
                    valtype vch = stacktop(-1);
                    stack.push_back(vch);
                }
                break;

                case OP_NIP:
                {
                    // (x1 x2 -- x2)
                    if (stack.size() < 2)
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);
                    stack.erase(stack.end() - 2);
                }
                break;

                case OP_OVER:
                {
                    // (x1 x2 -- x1 x2 x1)
                    if (stack.size() < 2)
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);
                    valtype vch = stacktop(-2);
                    stack.push_back(vch);
                }
                break;

                case OP_PICK:
                case OP_ROLL:
                {
                    // (xn ... x2 x1 x0 n - xn ... x2 x1 x0 xn)
                    // (xn ... x2 x1 x0 n - ... x2 x1 x0 xn)
                    if (stack.size() < 2)
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);
                    int n = CScriptNum(stacktop(-1), fRequireMinimal).getint();
                    popstack(stack);
                    if (n < 0 || n >= (int)stack.size())
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);
                    valtype vch = stacktop(-n-1);
                    if (opcode == OP_ROLL)
                        stack.erase(stack.end()-n-1);
                    stack.push_back(vch);
                }
                break;

                case OP_ROT:
                {
                    // (x1 x2 x3 -- x2 x3 x1)
                    //  x2 x1 x3  after first swap
                    //  x2 x3 x1  after second swap
                    if (stack.size() < 3)
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);
                    swap(stacktop(-3), stacktop(-2));
                    swap(stacktop(-2), stacktop(-1));
                }
                break;

                case OP_SWAP:
                {
                    // (x1 x2 -- x2 x1)
                    if (stack.size() < 2)
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);
                    swap(stacktop(-2), stacktop(-1));
                }
                break;

                case OP_TUCK:
                {
                    // (x1 x2 -- x2 x1 x2)
                    if (stack.size() < 2)
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);
                    valtype vch = stacktop(-1);
                    stack.insert(stack.end()-2, vch);
                }
                break;

                case OP_CAT:
                {
                    if (stack.size() < 2)
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);
                    valtype vch1 = stacktop(-2);
                    valtype vch2 = stacktop(-1);

                    if (vch1.size() + vch2.size() > MAX_SCRIPT_ELEMENT_SIZE)
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);

                    valtype vch3;
                    vch3.reserve(vch1.size() + vch2.size());
                    vch3.insert(vch3.end(), vch1.begin(), vch1.end());
                    vch3.insert(vch3.end(), vch2.begin(), vch2.end());

                    popstack(stack);
                    popstack(stack);
                    stack.push_back(vch3);
                }
                break;

                case OP_SIZE:
                {
                    // (in -- in size)
                    if (stack.size() < 1)
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);
                    CScriptNum bn(stacktop(-1).size());
                    stack.push_back(bn.getvch());
                }
                break;

                //
                // String operators
                //
                case OP_LEFT:
                case OP_RIGHT:
                {
                    if (stack.size() < 2)
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);

                    valtype vch1 = stacktop(-2);
                    CScriptNum start(stacktop(-1), fRequireMinimal);

                    if (start < 0)
                        return set_error(serror, SCRIPT_ERR_UNKNOWN_ERROR);

                    valtype vch2;
                    switch (opcode) {
                        case OP_RIGHT:
                        {
                            if (start >= vch1.size())
                                vch2 = vchZero;
                            else
                                vch2.insert(vch2.begin(), vch1.begin() + start.getint(), vch1.end());
                            break;
                        }
                        case OP_LEFT:
                        {
                            if (start >= vch1.size())
                                vch2 = vch1;
                            else
                                vch2.insert(vch2.begin(), vch1.begin(), vch1.begin() + start.getint());
                            break;
                        }
                        default:
                        {
                            assert(!"invalid opcode");
                            break;
                        }
                    }
                    popstack(stack);
                    popstack(stack);
                    stack.push_back(vch2);
                }
                break;

                case OP_SUBSTR:
                case OP_SUBSTR_LAZY:
                {
                    if (stack.size() < 3)
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);

                    valtype vch1 = stacktop(-3);
                    CScriptNum start(stacktop(-2), fRequireMinimal);
                    CScriptNum length(stacktop(-1), fRequireMinimal);

                    if (opcode == OP_SUBSTR_LAZY) {
                        if (start < 0)
                            start = 0;

                        if (length < 0)
                            length = 0;

                        if (start >= vch1.size()) {
                            popstack(stack);
                            popstack(stack);
                            popstack(stack);
                            stack.push_back(vchZero);
                            break;
                        }

                        if (length > MAX_SCRIPT_ELEMENT_SIZE)
                            length = MAX_SCRIPT_ELEMENT_SIZE;

                        // start + length cannot overflow because of the restrictions immediately abo
                        if (start + length > vch1.size()) {
                            length = CScriptNum(vch1.size()) - start;
                        }
                    }

                    if (length < 0 || start < 0)
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);

                    if (start >= vch1.size())
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);

                    if (length > vch1.size())
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);

                    if ((start + length) > vch1.size())
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);

                    valtype vch2;
                    vch2.insert(vch2.begin(), vch1.begin() + start.getint(), vch1.begin() + (start + length).getint());

                    popstack(stack);
                    popstack(stack);
                    popstack(stack);
                    stack.push_back(vch2);
                }
                break;

                //
                // Bitwise logic
                //
                case OP_RSHIFT:
                {
                    if (stack.size() < 2)
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);
                    valtype vch1 = stacktop(-2);
                    CScriptNum bn(stacktop(-1), fRequireMinimal);

                    if (bn < 0)
                        return set_error(serror, SCRIPT_ERR_UNKNOWN_ERROR);

                    unsigned int full_bytes = bn.getint() / 8;
                    unsigned int bits = bn.getint() % 8;

                    if (full_bytes >= vch1.size()) {
                        popstack(stack);
                        popstack(stack);
                        stack.push_back(vchZero);
                        break;
                    }

                    valtype vch2;
                    vch2.insert(vch2.begin(), vch1.begin() + full_bytes, vch1.end());

                    uint16_t temp = 0;
                    for (int i=(vch2.size()-1);i>=0;--i) {
                        temp = (vch2[i] << (8 - bits)) | ((temp << 8) & 0xff00);
                        vch2[i] = (temp & 0xff00) >> 8;
                    }

                    // 0x0fff >> 4 == 0x00ff or 0xff, reduce to minimal representation
                    while (!vch2.empty() && vch2.back() == 0)
                        vch2.pop_back();

                    popstack(stack);
                    popstack(stack);
                    stack.push_back(vch2);
                }
                break;

                case OP_LSHIFT:
                {
                    if (stack.size() < 2)
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);
                    valtype vch1 = stacktop(-2);
                    CScriptNum bn(stacktop(-1), fRequireMinimal);

                    if (bn < 0)
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);

                    unsigned int full_bytes = bn.getint() / 8;
                    unsigned int bits = bn.getint() % 8;

                    if (vch1.size() + full_bytes + (bits ? 1 : 0) > MAX_SCRIPT_ELEMENT_SIZE)
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);

                    valtype vch2;
                    vch2.reserve(vch1.size() + full_bytes + 1);
                    vch2.insert(vch2.end(), full_bytes, 0);
                    vch2.insert(vch2.end(), vch1.begin(), vch1.end());
                    vch2.insert(vch2.end(), 1, 0);

                    uint16_t temp = 0;
                    for (size_t i=0;i<vch2.size();++i) {
                        temp = (vch2[i] << bits) | (temp >> 8);
                        vch2[i] = temp & 0xff;
                    }

                    // reduce to minimal representation
                    while (!vch2.empty() && vch2.back() == 0)
                        vch2.pop_back();

                    popstack(stack);
                    popstack(stack);
                    stack.push_back(vch2);
                }
                break;

                case OP_INVERT:
                {
                    if (stack.size() < 1)
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);
                    valtype& vch1 = stacktop(-1);
                    for (size_t i = 0; i < vch1.size(); ++i)
                        vch1[i] = ~vch1[i];
                }
                break;

                case OP_AND:
                {
                    // (x1 x2 -- x1 & x2)
                    if (stack.size() < 2)
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);
                    valtype& vch1 = stacktop(-1);
                    valtype& vch2 = stacktop(-2);
                    if (vch1.size() != vch2.size())
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);

                    valtype vch3(vch1);
                    for (size_t i = 0; i < vch1.size(); i++)
                        vch3[i] &= vch2[i];
                    popstack(stack);
                    popstack(stack);
                    stack.push_back(vch3);
                }
                break;

                case OP_OR:
                {
                    // (x1 x2 -- x1 | x2)
                    if (stack.size() < 2)
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);
                    valtype& vch1 = stacktop(-1);
                    valtype& vch2 = stacktop(-2);
                    if (vch1.size() != vch2.size())
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);

                    valtype vch3(vch1);
                    for (size_t i = 0; i < vch1.size(); i++)
                        vch3[i] |= vch2[i];
                    popstack(stack);
                    popstack(stack);
                    stack.push_back(vch3);
                }
                break;

                case OP_XOR:
                {
                    // (x1 x2 -- x1 ^ x2)
                    if (stack.size() < 2)
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);
                    valtype& vch1 = stacktop(-1);
                    valtype& vch2 = stacktop(-2);
                    if (vch1.size() != vch2.size())
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);

                    valtype vch3(vch1);
                    for (size_t i = 0; i < vch1.size(); i++)
                        vch3[i] ^= vch2[i];
                    popstack(stack);
                    popstack(stack);
                    stack.push_back(vch3);
                }
                break;

                case OP_EQUAL:
                case OP_EQUALVERIFY:
                //case OP_NOTEQUAL: // use OP_NUMNOTEQUAL
                {
                    // (x1 x2 - bool)
                    if (stack.size() < 2)
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);
                    valtype& vch1 = stacktop(-2);
                    valtype& vch2 = stacktop(-1);
                    bool fEqual = (vch1 == vch2);
                    // OP_NOTEQUAL is disabled because it would be too easy to say
                    // something like n != 1 and have some wiseguy pass in 1 with extra
                    // zero bytes after it (numerically, 0x01 == 0x0001 == 0x000001)
                    //if (opcode == OP_NOTEQUAL)
                    //    fEqual = !fEqual;
                    popstack(stack);
                    popstack(stack);
                    stack.push_back(fEqual ? vchTrue : vchFalse);
                    if (opcode == OP_EQUALVERIFY)
                    {
                        if (fEqual)
                            popstack(stack);
                        else
                            return set_error(serror, SCRIPT_ERR_EQUALVERIFY);
                    }
                }
                break;


                //
                // Numeric
                //
                case OP_1ADD:
                case OP_1SUB:
                case OP_NEGATE:
                case OP_ABS:
                case OP_NOT:
                case OP_0NOTEQUAL:
                {
                    // (in -- out)
                    if (stack.size() < 1)
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);
                    CScriptNum bn(stacktop(-1), fRequireMinimal);
                    switch (opcode)
                    {
                    case OP_1ADD:       bn += bnOne; break;
                    case OP_1SUB:       bn -= bnOne; break;
                    case OP_NEGATE:     bn = -bn; break;
                    case OP_ABS:        if (bn < bnZero) bn = -bn; break;
                    case OP_NOT:        bn = (bn == bnZero); break;
                    case OP_0NOTEQUAL:  bn = (bn != bnZero); break;
                    default:            assert(!"invalid opcode"); break;
                    }
                    popstack(stack);
                    stack.push_back(bn.getvch());
                }
                break;

                case OP_ADD:
                case OP_SUB:
                case OP_BOOLAND:
                case OP_BOOLOR:
                case OP_NUMEQUAL:
                case OP_NUMEQUALVERIFY:
                case OP_NUMNOTEQUAL:
                case OP_LESSTHAN:
                case OP_GREATERTHAN:
                case OP_LESSTHANOREQUAL:
                case OP_GREATERTHANOREQUAL:
                case OP_MIN:
                case OP_MAX:
                {
                    // (x1 x2 -- out)
                    if (stack.size() < 2)
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);
                    CScriptNum bn1(stacktop(-2), fRequireMinimal);
                    CScriptNum bn2(stacktop(-1), fRequireMinimal);
                    CScriptNum bn(0);
                    switch (opcode)
                    {
                    case OP_ADD:
                        bn = bn1 + bn2;
                        break;

                    case OP_SUB:
                        bn = bn1 - bn2;
                        break;

                    case OP_BOOLAND:             bn = (bn1 != bnZero && bn2 != bnZero); break;
                    case OP_BOOLOR:              bn = (bn1 != bnZero || bn2 != bnZero); break;
                    case OP_NUMEQUAL:            bn = (bn1 == bn2); break;
                    case OP_NUMEQUALVERIFY:      bn = (bn1 == bn2); break;
                    case OP_NUMNOTEQUAL:         bn = (bn1 != bn2); break;
                    case OP_LESSTHAN:            bn = (bn1 < bn2); break;
                    case OP_GREATERTHAN:         bn = (bn1 > bn2); break;
                    case OP_LESSTHANOREQUAL:     bn = (bn1 <= bn2); break;
                    case OP_GREATERTHANOREQUAL:  bn = (bn1 >= bn2); break;
                    case OP_MIN:                 bn = (bn1 < bn2 ? bn1 : bn2); break;
                    case OP_MAX:                 bn = (bn1 > bn2 ? bn1 : bn2); break;
                    default:                     assert(!"invalid opcode"); break;
                    }
                    popstack(stack);
                    popstack(stack);
                    stack.push_back(bn.getvch());

                    if (opcode == OP_NUMEQUALVERIFY)
                    {
                        if (CastToBool(stacktop(-1)))
                            popstack(stack);
                        else
                            return set_error(serror, SCRIPT_ERR_NUMEQUALVERIFY);
                    }
                }
                break;

                case OP_WITHIN:
                {
                    // (x min max -- out)
                    if (stack.size() < 3)
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);
                    CScriptNum bn1(stacktop(-3), fRequireMinimal);
                    CScriptNum bn2(stacktop(-2), fRequireMinimal);
                    CScriptNum bn3(stacktop(-1), fRequireMinimal);
                    bool fValue = (bn2 <= bn1 && bn1 < bn3);
                    popstack(stack);
                    popstack(stack);
                    popstack(stack);
                    stack.push_back(fValue ? vchTrue : vchFalse);
                }
                break;


                //
                // Crypto
                //
                case OP_RIPEMD160:
                case OP_SHA1:
                case OP_SHA256:
                case OP_HASH160:
                case OP_HASH256:
                {
                    // (in -- hash)
                    if (stack.size() < 1)
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);
                    valtype& vch = stacktop(-1);
                    valtype vchHash((opcode == OP_RIPEMD160 || opcode == OP_SHA1 || opcode == OP_HASH160) ? 20 : 32);
                    if (opcode == OP_RIPEMD160)
                        CRIPEMD160().Write(vch.data(), vch.size()).Finalize(vchHash.data());
                    else if (opcode == OP_SHA1)
                        CSHA1().Write(vch.data(), vch.size()).Finalize(vchHash.data());
                    else if (opcode == OP_SHA256)
                        CSHA256().Write(vch.data(), vch.size()).Finalize(vchHash.data());
                    else if (opcode == OP_HASH160)
                        CHash160().Write(vch.data(), vch.size()).Finalize(vchHash.data());
                    else if (opcode == OP_HASH256)
                        CHash256().Write(vch.data(), vch.size()).Finalize(vchHash.data());
                    popstack(stack);
                    stack.push_back(vchHash);
                }
                break;                                   

                case OP_CODESEPARATOR:
                {
                    // Hash starts after the code separator
                    pbegincodehash = pc;
                }
                break;

                case OP_CHECKSIG:
                case OP_CHECKSIGVERIFY:
                {
                    // (sig pubkey -- bool)
                    if (stack.size() < 2)
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);

                    valtype& vchSig    = stacktop(-2);
                    valtype& vchPubKey = stacktop(-1);

                    // Subset of script starting at the most recent codeseparator
                    CScript scriptCode(pbegincodehash, pend);

                    // Drop the signature in pre-segwit scripts but not segwit scripts
                    if (sigversion == SIGVERSION_BASE) {
                        scriptCode.FindAndDelete(CScript(vchSig));
                    }

                    if (!CheckSignatureEncoding(vchSig, flags, serror) || !CheckPubKeyEncoding(vchPubKey, flags, sigversion, serror)) {
                        //serror is set
                        return false;
                    }
                    bool fSuccess = checker.CheckSig(vchSig, vchPubKey, scriptCode, sigversion);

                    if (!fSuccess && (flags & SCRIPT_VERIFY_NULLFAIL) && vchSig.size())
                        return set_error(serror, SCRIPT_ERR_SIG_NULLFAIL);

                    popstack(stack);
                    popstack(stack);
                    stack.push_back(fSuccess ? vchTrue : vchFalse);
                    if (opcode == OP_CHECKSIGVERIFY)
                    {
                        if (fSuccess)
                            popstack(stack);
                        else
                            return set_error(serror, SCRIPT_ERR_CHECKSIGVERIFY);
                    }
                }
                break;

                case OP_CHECKMULTISIG:
                case OP_CHECKMULTISIGVERIFY:
                {
                    // ([sig ...] num_of_signatures [pubkey ...] num_of_pubkeys -- bool)

                    int i = 1;
                    if ((int)stack.size() < i)
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);

                    int nKeysCount = CScriptNum(stacktop(-i), fRequireMinimal).getint();
                    if (nKeysCount < 0 || nKeysCount > MAX_PUBKEYS_PER_MULTISIG)
                        return set_error(serror, SCRIPT_ERR_PUBKEY_COUNT);
                    nOpCount += nKeysCount;
                    if (nOpCount > MAX_OPS_PER_SCRIPT)
                        return set_error(serror, SCRIPT_ERR_OP_COUNT);
                    int ikey = ++i;
                    // ikey2 is the position of last non-signature item in the stack. Top stack item = 1.
                    // With SCRIPT_VERIFY_NULLFAIL, this is used for cleanup if operation fails.
                    int ikey2 = nKeysCount + 2;
                    i += nKeysCount;
                    if ((int)stack.size() < i)
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);

                    int nSigsCount = CScriptNum(stacktop(-i), fRequireMinimal).getint();
                    if (nSigsCount < 0 || nSigsCount > nKeysCount)
                        return set_error(serror, SCRIPT_ERR_SIG_COUNT);
                    int isig = ++i;
                    i += nSigsCount;
                    if ((int)stack.size() < i)
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);

                    // Subset of script starting at the most recent codeseparator
                    CScript scriptCode(pbegincodehash, pend);

                    // Drop the signature in pre-segwit scripts but not segwit scripts
                    for (int k = 0; k < nSigsCount; k++)
                    {
                        valtype& vchSig = stacktop(-isig-k);
                        if (sigversion == SIGVERSION_BASE) {
                            scriptCode.FindAndDelete(CScript(vchSig));
                        }
                    }

                    bool fSuccess = true;
                    while (fSuccess && nSigsCount > 0)
                    {
                        valtype& vchSig    = stacktop(-isig);
                        valtype& vchPubKey = stacktop(-ikey);

                        // Note how this makes the exact order of pubkey/signature evaluation
                        // distinguishable by CHECKMULTISIG NOT if the STRICTENC flag is set.
                        // See the script_(in)valid tests for details.
                        if (!CheckSignatureEncoding(vchSig, flags, serror) || !CheckPubKeyEncoding(vchPubKey, flags, sigversion, serror)) {
                            // serror is set
                            return false;
                        }

                        // Check signature
                        bool fOk = checker.CheckSig(vchSig, vchPubKey, scriptCode, sigversion);

                        if (fOk) {
                            isig++;
                            nSigsCount--;
                        }
                        ikey++;
                        nKeysCount--;

                        // If there are more signatures left than keys left,
                        // then too many signatures have failed. Exit early,
                        // without checking any further signatures.
                        if (nSigsCount > nKeysCount)
                            fSuccess = false;
                    }

                    // Clean up stack of actual arguments
                    while (i-- > 1) {
                        // If the operation failed, we require that all signatures must be empty vector
                        if (!fSuccess && (flags & SCRIPT_VERIFY_NULLFAIL) && !ikey2 && stacktop(-1).size())
                            return set_error(serror, SCRIPT_ERR_SIG_NULLFAIL);
                        if (ikey2 > 0)
                            ikey2--;
                        popstack(stack);
                    }

                    // A bug causes CHECKMULTISIG to consume one extra argument
                    // whose contents were not checked in any way.
                    //
                    // Unfortunately this is a potential source of mutability,
                    // so optionally verify it is exactly equal to zero prior
                    // to removing it from the stack.
                    if (stack.size() < 1)
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);
                    if ((flags & SCRIPT_VERIFY_NULLDUMMY) && stacktop(-1).size())
                        return set_error(serror, SCRIPT_ERR_SIG_NULLDUMMY);
                    popstack(stack);

                    stack.push_back(fSuccess ? vchTrue : vchFalse);

                    if (opcode == OP_CHECKMULTISIGVERIFY)
                    {
                        if (fSuccess)
                            popstack(stack);
                        else
                            return set_error(serror, SCRIPT_ERR_CHECKMULTISIGVERIFY);
                    }
                }
                break;

                case OP_CHECKSIGFROMSTACK:
                case OP_CHECKSIGFROMSTACKVERIFY:
                {
                    // (sig data pubkey  -- bool)
                    if (stack.size() < 3)
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);

                    valtype& vchSig    = stacktop(-3);
                    valtype& vchData   = stacktop(-2);
                    valtype& vchPubKey = stacktop(-1);

                    // Sigs from stack have no hash type, so we disable strictenc check
                    if (!CheckSignatureEncoding(vchSig, (flags & ~SCRIPT_VERIFY_STRICTENC), serror) || !CheckPubKeyEncoding(vchPubKey, flags, sigversion, serror)) {
                        //serror is set
                        return false;
                    }

                    valtype vchHash(32);
                    CSHA256().Write(vchData.data(), vchData.size()).Finalize(vchHash.data());
                    uint256 hash(vchHash);

                    CPubKey pubkey(vchPubKey);
                    bool fSuccess = pubkey.Verify(hash, vchSig);

                    popstack(stack);
                    popstack(stack);
                    popstack(stack);
                    stack.push_back(fSuccess ? vchTrue : vchFalse);

                    if (opcode == OP_CHECKSIGFROMSTACKVERIFY)
                    {
                        if (fSuccess)
                            popstack(stack);
                        else
                            return set_error(serror, SCRIPT_ERR_CHECKSIGFROMSTACKVERIFY);
                    }

                }
                break;

                case OP_DETERMINISTICRANDOM:
                {
                    if (stack.size() < 3)
                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);

                    valtype vchSeed = stacktop(-3);
                    CScriptNum bnMin(stacktop(-2), fRequireMinimal);
                    CScriptNum bnMax(stacktop(-1), fRequireMinimal);

                    if (bnMin > bnMax)
                        return set_error(serror, SCRIPT_ERR_UNKNOWN_ERROR);

                    if (bnMin == bnMax) {
                        popstack(stack);
                        popstack(stack);
                        popstack(stack);
                        stack.push_back(bnMin.getvch());
                        break;
                    }

                    // The range of the random source must be a multiple of the modulus
                    // to give every possible output value an equal possibility
                    uint64_t nMax = (bnMax-bnMin).getint();
                    uint64_t nRange = (std::numeric_limits<uint64_t>::max() / nMax) * nMax;
                    uint64_t nRand;

                    valtype vchHash(32, 0);
                    uint64_t nCounter = 0;
                    int nHashIndex = 3;
                    CSHA256 hasher;
                    hasher.Write(vchSeed.data(), vchSeed.size());
                    do {
                        if (nHashIndex >= 3) {
                            //TODO this isn't endian safe
                            CSHA256(hasher).Write((const unsigned char*)&nCounter, sizeof(nCounter)).Finalize(vchHash.data());
                            nHashIndex = 0;
                            nCounter++;
                        }

                        nRand = 0;
                        for (size_t i=0; i<8; ++i)
                            nRand |= ((uint64_t)vchHash[(nHashIndex*8) + i]) << (8*i);

                        nHashIndex++;
                    } while (nRand > nRange);
                    CScriptNum result(nRand % nMax);
                    result += bnMin.getint();

                    popstack(stack);
                    popstack(stack);
                    popstack(stack);
                    stack.push_back(result.getvch());
                 }
                 break;

                case OP_WITHDRAWPROOFVERIFY:
                {
                    // In the make-withdraw case, reads the following from the stack:
                    // 1. genesis block hash of the chain the withdraw is coming from
                    // 2. the index within the locking tx's outputs we are claiming
                    // 3. the locking tx itself (WithdrawProofReadStackItem)
                    // 4. the merkle block structure which contains the block in which
                    //    the locking transaction is present (WithdrawProofReadStackItem)
                    // 5. The contract which we are expected to send coins to
                    //
                    // In the combine-outputs case, reads the following from the stack:
                    // 1. genesis block hash of the chain the withdraw is coming from

                    if (flags & SCRIPT_VERIFY_WITHDRAW) {
                        if (stack.size() < 7 && stack.size() != 1)
                            return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);

                        const valtype &vgenesisHash = stacktop(-1);
                        if (vgenesisHash.size() != 32)
                            return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_FORMAT);

                        assert(checker.GetValueIn() != CConfidentialValue(-1)); // Not using a NoWithdrawSignatureChecker

                        CScript relockScript = CScript() << vgenesisHash << OP_WITHDRAWPROOFVERIFY;

                        if (stack.size() == 1) { // increasing value of locked coins
                            if (!checker.GetValueIn().IsExplicit())
                                return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_BLINDED_AMOUNTS);
                            CAmount minValue = checker.GetValueIn().GetAmount();
                            CTxOut newOutput = checker.GetOutputOffsetFromCurrent(0);
                            if (newOutput.IsNull()) {
                                newOutput = checker.GetOutputOffsetFromCurrent(-1);
                                if (!checker.GetValueInPrevIn().IsExplicit())
                                    return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_BLINDED_AMOUNTS);
                                minValue += checker.GetValueInPrevIn().GetAmount();
                            }
                            if (!newOutput.nValue.IsExplicit())
                                return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_BLINDED_AMOUNTS);
                            if (newOutput.scriptPubKey != relockScript || newOutput.nValue.GetAmount() < minValue)
                                return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_OUTPUT);
                        } else { // stack.size() >= 7...ie regular withdraw
                            int stackReadPos = -2;

                            const valtype &vlockTxOutIndex = stacktop(stackReadPos--);

                            valtype vlockTx;
                            if (!WithdrawProofReadStackItem(stack, fRequireMinimal, &stackReadPos, vlockTx))
                                return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);

                            valtype vmerkleBlock;
                            if (!WithdrawProofReadStackItem(stack, fRequireMinimal, &stackReadPos, vmerkleBlock))
                                return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);

                            if (stack.size() < size_t(-stackReadPos))
                                return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);
                            valtype vcontract = std::vector<unsigned char>(stacktop(stackReadPos--));

                            uint256 genesishash(vgenesisHash);

                            try {
                                Sidechain::Bitcoin::CMerkleBlock merkleBlock;
                                CDataStream merkleBlockStream(vmerkleBlock, SER_NETWORK, PROTOCOL_VERSION);
                                merkleBlockStream >> merkleBlock;
                                if (!merkleBlockStream.empty() || !CheckBitcoinProof(merkleBlock.header.GetHash(), merkleBlock.header.nBits))
                                    return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_BLOCK);

                                vector<uint256> txHashes;
                                vector<unsigned int> txIndices;
                                if (merkleBlock.txn.ExtractMatches(txHashes, txIndices) != merkleBlock.header.hashMerkleRoot || txHashes.size() != 1)
                                    return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_BLOCK);

                                // We disallow returns from the genesis block, allowing sidechains to
                                // make genesis outputs spendable with a 21m initially-locked-to-btc
                                // distributing transaction.
                                if (merkleBlock.header.GetHash() == genesishash)
                                    return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_BLOCK);

                                Sidechain::Bitcoin::CTransactionRef locktx;
                                CDataStream locktxStream(vlockTx, SER_NETWORK, PROTOCOL_VERSION);
                                locktxStream >> locktx;
                                if (!locktxStream.empty())
                                    return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_LOCKTX);

                                int nlocktxOut = CScriptNum(vlockTxOutIndex, fRequireMinimal).getint();
                                if (nlocktxOut < 0 || (unsigned int)nlocktxOut >= locktx->vout.size())
                                    return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_LOCKTX);

                                if (locktx->GetHash() != txHashes[0])
                                    return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_LOCKTX);

                                if (vcontract.size() != 40)
                                    return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_FORMAT);

                                opcodetype opcodeTmp;
                                CScript scriptDestination = checker.GetFedpegScript();
                                {
                                    CScript::iterator sdpc = scriptDestination.begin();
                                    vector<unsigned char> vch;
                                    while (scriptDestination.GetOp(sdpc, opcodeTmp, vch))
                                    {
                                        assert((vch.size() == 33 && opcodeTmp < OP_PUSHDATA4) ||
                                               (opcodeTmp <= OP_16 && opcodeTmp >= OP_1) || opcodeTmp == OP_CHECKMULTISIG);
                                        if (vch.size() == 33)
                                        {
                                            unsigned char tweak[32];
                                            size_t pub_len = 33;
                                            int ret;
                                            unsigned char *pub_start = &(*(sdpc - pub_len));
                                            CHMAC_SHA256(pub_start, pub_len).Write(&vcontract[0], 40).Finalize(tweak);
                                            secp256k1_pubkey pubkey;
                                            ret = secp256k1_ec_pubkey_parse(secp256k1_ctx, &pubkey, pub_start, pub_len);
                                            assert(ret == 1);
                                            // If someone creates a tweak that makes this fail, they broke SHA256
                                            ret = secp256k1_ec_pubkey_tweak_add(secp256k1_ctx, &pubkey, tweak);
                                            assert(ret == 1);
                                            ret = secp256k1_ec_pubkey_serialize(secp256k1_ctx, pub_start, &pub_len, &pubkey, SECP256K1_EC_COMPRESSED);
                                            assert(ret == 1);
                                            assert(pub_len == 33);
                                        }
                                    }
                                }

                                CScriptID expectedP2SH(scriptDestination);
                                if (locktx->vout[nlocktxOut].scriptPubKey != GetScriptForDestination(expectedP2SH))
                                    return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_OUTPUT_SCRIPTDEST);

                                vcontract.erase(vcontract.begin() + 4, vcontract.begin() + 20); // Remove the nonce from the contract before further processing
                                assert(vcontract.size() == 24);

                                // We check values by doing the following:
                                // * Tx must relock at least <unlocked coins> - <locked-on-bitcoin coins>
                                // * Tx must send at least the withdraw value to its P2SH withdraw, but may send more
                                CAmount withdrawVal = locktx->vout[nlocktxOut].nValue;
                                if (!checker.GetValueIn().IsExplicit()) // Heh, you just destroyed coins
                                    return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_BLINDED_AMOUNTS);

                                CAmount lockValueRequired = checker.GetValueIn().GetAmount() - withdrawVal;
                                if (lockValueRequired > 0) {
                                    const CTxOut newLockOutput = checker.GetOutputOffsetFromCurrent(1);
                                    if (!newLockOutput.nValue.IsExplicit())
                                        return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_BLINDED_AMOUNTS);
                                    if (newLockOutput.IsNull() || newLockOutput.scriptPubKey != relockScript || newLockOutput.nValue.GetAmount() < lockValueRequired)
                                        return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_RELOCK_SCRIPTVAL);
                                }

                                const CTxOut withdrawOutput = checker.GetOutputOffsetFromCurrent(0);
                                if (!withdrawOutput.nValue.IsExplicit())
                                    return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_BLINDED_AMOUNTS);
                                if (withdrawOutput.nValue.GetAmount() < withdrawVal)
                                    return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_OUTPUT_VAL);

                                CScript expectedWithdrawScriptPubKey;
                                if (vcontract[0] == 'P' && vcontract[1] == '2' && vcontract[2] == 'S' && vcontract[3] == 'H')
                                    expectedWithdrawScriptPubKey = CScript() << OP_HASH160 << std::vector<unsigned char>(vcontract.begin() + 4, vcontract.begin() + 24) << OP_EQUAL;
                                else if (vcontract[0] == 'P' && vcontract[1] == '2' && vcontract[2] == 'P' && vcontract[3] == 'H')
                                    expectedWithdrawScriptPubKey = CScript() << OP_DUP << OP_HASH160 << std::vector<unsigned char>(vcontract.begin() + 4, vcontract.begin() + 24) << OP_EQUALVERIFY << OP_CHECKSIG;
                                else
                                    return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_FORMAT);

                                if (withdrawOutput.scriptPubKey != expectedWithdrawScriptPubKey)
                                    return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_OUTPUT_SCRIPT);

#ifndef BITCOIN_SCRIPT_NO_CALLRPC
                                if (GetBoolArg("-validatepegin", DEFAULT_VALIDATE_PEGIN) && !checker.IsConfirmedBitcoinBlock(genesishash, merkleBlock.header.GetHash(), flags & SCRIPT_VERIFY_INCREASE_CONFIRMATIONS_REQUIRED))
                                    return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_BLOCKCONFIRMED);
#endif
                            } catch (std::exception& e) {
                                // Probably invalid encoding of something which was deserialized
                                return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_FORMAT);
                            }
                        }
                    } // else...OP_NOP3
                }
                break;

                default:
                    return set_error(serror, SCRIPT_ERR_BAD_OPCODE);
            }

            // Size limits
            if (stack.size() + altstack.size() > 1000)
                return set_error(serror, SCRIPT_ERR_STACK_SIZE);
        }
    }
    catch (...)
    {
        return set_error(serror, SCRIPT_ERR_UNKNOWN_ERROR);
    }

    if (!vfExec.empty())
        return set_error(serror, SCRIPT_ERR_UNBALANCED_CONDITIONAL);

    return set_success(serror);
}

namespace {

/**
 * Wrapper that serializes like CTransaction, but with the modifications
 *  required for the signature hash done in-place
 */
class CTransactionSignatureSerializer {
private:
    const CTransaction& txTo;  //!< reference to the spending transaction (the one being serialized)
    const CScript& scriptCode; //!< output script being consumed
    const unsigned int nIn;    //!< input index of txTo being signed
    const bool fAnyoneCanPay;  //!< whether the hashtype has the SIGHASH_ANYONECANPAY flag set
    const bool fHashSingle;    //!< whether the hashtype is SIGHASH_SINGLE
    const bool fHashNone;      //!< whether the hashtype is SIGHASH_NONE

public:
    CTransactionSignatureSerializer(const CTransaction &txToIn, const CScript &scriptCodeIn, unsigned int nInIn, int nHashTypeIn) :
        txTo(txToIn), scriptCode(scriptCodeIn), nIn(nInIn),
        fAnyoneCanPay(!!(nHashTypeIn & SIGHASH_ANYONECANPAY)),
        fHashSingle((nHashTypeIn & 0x1f) == SIGHASH_SINGLE),
        fHashNone((nHashTypeIn & 0x1f) == SIGHASH_NONE) {}

    /** Serialize the passed scriptCode, skipping OP_CODESEPARATORs */
    template<typename S>
    void SerializeScriptCode(S &s) const {
        CScript::const_iterator it = scriptCode.begin();
        CScript::const_iterator itBegin = it;
        opcodetype opcode;
        unsigned int nCodeSeparators = 0;
        while (scriptCode.GetOp(it, opcode)) {
            if (opcode == OP_CODESEPARATOR)
                nCodeSeparators++;
        }
        ::WriteCompactSize(s, scriptCode.size() - nCodeSeparators);
        it = itBegin;
        while (scriptCode.GetOp(it, opcode)) {
            if (opcode == OP_CODESEPARATOR) {
                s.write((char*)&itBegin[0], it-itBegin-1);
                itBegin = it;
            }
        }
        if (itBegin != scriptCode.end())
            s.write((char*)&itBegin[0], it-itBegin);
    }

    /** Serialize an input of txTo */
    template<typename S>
    void SerializeInput(S &s, unsigned int nInput) const {
        // In case of SIGHASH_ANYONECANPAY, only the input being signed is serialized
        if (fAnyoneCanPay)
            nInput = nIn;
        // Serialize the prevout
        ::Serialize(s, txTo.vin[nInput].prevout);
        // Serialize the script
        if (nInput != nIn)
            // Blank out other inputs' signatures
            ::Serialize(s, CScriptBase());
        else
            SerializeScriptCode(s);
        // Serialize the nSequence
        if (nInput != nIn && (fHashSingle || fHashNone))
            // let the others update at will
            ::Serialize(s, (int)0);
        else
            ::Serialize(s, txTo.vin[nInput].nSequence);
        // Serialize the asset issuance object
        if (!txTo.vin[nInput].assetIssuance.IsNull())
            ::Serialize(s, txTo.vin[nInput].assetIssuance);
    }

    /** Serialize an output of txTo */
    template<typename S>
    void SerializeOutput(S &s, unsigned int nOutput) const {
        if (fHashSingle && nOutput != nIn)
            // Do not lock-in the txout payee at other indices as txin
            ::Serialize(s, CTxOut());
        else
            ::Serialize(s, txTo.vout[nOutput]);
    }

    /** Serialize txTo */
    template<typename S>
    void Serialize(S &s) const {
        // Serialize nVersion
        ::Serialize(s, txTo.nVersion);
        // Serialize vin
        unsigned int nInputs = fAnyoneCanPay ? 1 : txTo.vin.size();
        ::WriteCompactSize(s, nInputs);
        for (unsigned int nInput = 0; nInput < nInputs; nInput++)
             SerializeInput(s, nInput);
        // Serialize vout
        unsigned int nOutputs = fHashNone ? 0 : (fHashSingle ? nIn+1 : txTo.vout.size());
        ::WriteCompactSize(s, nOutputs);
        for (unsigned int nOutput = 0; nOutput < nOutputs; nOutput++)
             SerializeOutput(s, nOutput);
        // Serialize nLockTime
        ::Serialize(s, txTo.nLockTime);
    }
};

uint256 GetPrevoutHash(const CTransaction& txTo) {
    CHashWriter ss(SER_GETHASH, 0);
    for (unsigned int n = 0; n < txTo.vin.size(); n++) {
        ss << txTo.vin[n].prevout;
    }
    return ss.GetHash();
}

uint256 GetSequenceHash(const CTransaction& txTo) {
    CHashWriter ss(SER_GETHASH, 0);
    for (unsigned int n = 0; n < txTo.vin.size(); n++) {
        ss << txTo.vin[n].nSequence;
    }
    return ss.GetHash();
}

uint256 GetIssuanceHash(const CTransaction& txTo) {
    CHashWriter ss(SER_GETHASH, 0);
    for (unsigned int n = 0; n < txTo.vin.size(); n++) {
        if (txTo.vin[n].assetIssuance.IsNull())
            ss << (unsigned char)0;
        else
            ss << txTo.vin[n].assetIssuance;
    }
    return ss.GetHash();
}

uint256 GetOutputsHash(const CTransaction& txTo) {
    CHashWriter ss(SER_GETHASH, 0);
    for (unsigned int n = 0; n < txTo.vout.size(); n++) {
        ss << txTo.vout[n];
    }
    return ss.GetHash();
}

} // anon namespace

PrecomputedTransactionData::PrecomputedTransactionData(const CTransaction& txTo)
{
    hashPrevouts = GetPrevoutHash(txTo);
    hashSequence = GetSequenceHash(txTo);
    hashIssuance = GetIssuanceHash(txTo);
    hashOutputs = GetOutputsHash(txTo);
}

uint256 SignatureHash(const CScript& scriptCode, const CTransaction& txTo, unsigned int nIn, int nHashType, const CConfidentialValue& amount, SigVersion sigversion, const PrecomputedTransactionData* cache)
{
    if (sigversion == SIGVERSION_WITNESS_V0) {
        uint256 hashPrevouts;
        uint256 hashSequence;
        uint256 hashIssuance;
        uint256 hashOutputs;

        if (!(nHashType & SIGHASH_ANYONECANPAY)) {
            hashPrevouts = cache ? cache->hashPrevouts : GetPrevoutHash(txTo);
        }

        if (!(nHashType & SIGHASH_ANYONECANPAY) && (nHashType & 0x1f) != SIGHASH_SINGLE && (nHashType & 0x1f) != SIGHASH_NONE) {
            hashSequence = cache ? cache->hashSequence : GetSequenceHash(txTo);
        }

        if (!(nHashType & SIGHASH_ANYONECANPAY)) {
            hashIssuance = cache ? cache->hashIssuance : GetIssuanceHash(txTo);
        }

        if ((nHashType & 0x1f) != SIGHASH_SINGLE && (nHashType & 0x1f) != SIGHASH_NONE) {
            hashOutputs = cache ? cache->hashOutputs : GetOutputsHash(txTo);
        } else if ((nHashType & 0x1f) == SIGHASH_SINGLE && nIn < txTo.vout.size()) {
            CHashWriter ss(SER_GETHASH, 0);
            ss << txTo.vout[nIn];
            hashOutputs = ss.GetHash();
        }

        CHashWriter ss(SER_GETHASH, 0);
        // Version
        ss << txTo.nVersion;
        // Input prevouts/nSequence (none/all, depending on flags)
        ss << hashPrevouts;
        ss << hashSequence;
        ss << hashIssuance;
        // The input being signed (replacing the scriptSig with scriptCode + amount)
        // The prevout may already be contained in hashPrevout, and the nSequence
        // may already be contain in hashSequence.
        ss << txTo.vin[nIn].prevout;
        ss << static_cast<const CScriptBase&>(scriptCode);
        ss << amount;
        ss << txTo.vin[nIn].nSequence;
        if (!txTo.vin[nIn].assetIssuance.IsNull())
            ss << txTo.vin[nIn].assetIssuance;
        // Outputs (none/one/all, depending on flags)
        ss << hashOutputs;
        // Locktime
        ss << txTo.nLockTime;
        // Sighash type
        ss << nHashType;

        return ss.GetHash();
    }

    static const uint256 one(uint256S("0000000000000000000000000000000000000000000000000000000000000001"));
    if (nIn >= txTo.vin.size()) {
        //  nIn out of range
        return one;
    }

    // Check for invalid use of SIGHASH_SINGLE
    if ((nHashType & 0x1f) == SIGHASH_SINGLE) {
        if (nIn >= txTo.vout.size()) {
            //  nOut out of range
            return one;
        }
    }

    // Wrapper to serialize only the necessary parts of the transaction being signed
    CTransactionSignatureSerializer txTmp(txTo, scriptCode, nIn, nHashType);

    // Serialize and hash
    CHashWriter ss(SER_GETHASH, 0);
    ss << txTmp << nHashType;
    return ss.GetHash();
}

CTxOut BaseSignatureChecker::GetOutputOffsetFromCurrent(const int offset) const
{
    return CTxOut();
}

COutPoint BaseSignatureChecker::GetPrevOut() const
{
    return COutPoint();
}

bool TransactionNoWithdrawsSignatureChecker::VerifySignature(const std::vector<unsigned char>& vchSig, const CPubKey& pubkey, const uint256& sighash) const
{
    return pubkey.Verify(sighash, vchSig);
}

bool TransactionNoWithdrawsSignatureChecker::CheckSig(const vector<unsigned char>& vchSigIn, const vector<unsigned char>& vchPubKey, const CScript& scriptCode, SigVersion sigversion) const
{
    CPubKey pubkey(vchPubKey);
    if (!pubkey.IsValid())
        return false;

    // Hash type is one byte tacked on to the end of the signature
    vector<unsigned char> vchSig(vchSigIn);
    if (vchSig.empty())
        return false;
    int nHashType = vchSig.back();
    vchSig.pop_back();

    uint256 sighash = SignatureHash(scriptCode, *txTo, nIn, nHashType, amount, sigversion, this->txdata);

    if (!VerifySignature(vchSig, pubkey, sighash))
        return false;

    return true;
}

bool TransactionNoWithdrawsSignatureChecker::CheckLockTime(const CScriptNum& nLockTime) const
{
    // There are two kinds of nLockTime: lock-by-blockheight
    // and lock-by-blocktime, distinguished by whether
    // nLockTime < LOCKTIME_THRESHOLD.
    //
    // We want to compare apples to apples, so fail the script
    // unless the type of nLockTime being tested is the same as
    // the nLockTime in the transaction.
    if (!(
        (txTo->nLockTime <  LOCKTIME_THRESHOLD && nLockTime <  LOCKTIME_THRESHOLD) ||
        (txTo->nLockTime >= LOCKTIME_THRESHOLD && nLockTime >= LOCKTIME_THRESHOLD)
    ))
        return false;

    // Now that we know we're comparing apples-to-apples, the
    // comparison is a simple numeric one.
    if (nLockTime > (int64_t)txTo->nLockTime)
        return false;

    // Finally the nLockTime feature can be disabled and thus
    // CHECKLOCKTIMEVERIFY bypassed if every txin has been
    // finalized by setting nSequence to maxint. The
    // transaction would be allowed into the blockchain, making
    // the opcode ineffective.
    //
    // Testing if this vin is not final is sufficient to
    // prevent this condition. Alternatively we could test all
    // inputs, but testing just this input minimizes the data
    // required to prove correct CHECKLOCKTIMEVERIFY execution.
    if (CTxIn::SEQUENCE_FINAL == txTo->vin[nIn].nSequence)
        return false;

    return true;
}

bool TransactionNoWithdrawsSignatureChecker::CheckSequence(const CScriptNum& nSequence) const
{
    // Relative lock times are supported by comparing the passed
    // in operand to the sequence number of the input.
    const int64_t txToSequence = (int64_t)txTo->vin[nIn].nSequence;

    // Fail if the transaction's version number is not set high
    // enough to trigger BIP 68 rules.
    if (static_cast<uint32_t>(txTo->nVersion) < 2)
        return false;

    // Sequence numbers with their most significant bit set are not
    // consensus constrained. Testing that the transaction's sequence
    // number do not have this bit set prevents using this property
    // to get around a CHECKSEQUENCEVERIFY check.
    if (txToSequence & CTxIn::SEQUENCE_LOCKTIME_DISABLE_FLAG)
        return false;

    // Mask off any bits that do not have consensus-enforced meaning
    // before doing the integer comparisons
    const uint32_t nLockTimeMask = CTxIn::SEQUENCE_LOCKTIME_TYPE_FLAG | CTxIn::SEQUENCE_LOCKTIME_MASK;
    const int64_t txToSequenceMasked = txToSequence & nLockTimeMask;
    const CScriptNum nSequenceMasked = nSequence & nLockTimeMask;

    // There are two kinds of nSequence: lock-by-blockheight
    // and lock-by-blocktime, distinguished by whether
    // nSequenceMasked < CTxIn::SEQUENCE_LOCKTIME_TYPE_FLAG.
    //
    // We want to compare apples to apples, so fail the script
    // unless the type of nSequenceMasked being tested is the same as
    // the nSequenceMasked in the transaction.
    if (!(
        (txToSequenceMasked <  CTxIn::SEQUENCE_LOCKTIME_TYPE_FLAG && nSequenceMasked <  CTxIn::SEQUENCE_LOCKTIME_TYPE_FLAG) ||
        (txToSequenceMasked >= CTxIn::SEQUENCE_LOCKTIME_TYPE_FLAG && nSequenceMasked >= CTxIn::SEQUENCE_LOCKTIME_TYPE_FLAG)
    )) {
        return false;
    }

    // Now that we know we're comparing apples-to-apples, the
    // comparison is a simple numeric one.
    if (nSequenceMasked > txToSequenceMasked)
        return false;

    return true;
}

CTxOut TransactionSignatureChecker::GetOutputOffsetFromCurrent(const int offset) const
{
    assert(int(nIn) >= 0 && int(txTo->vout.size()) > 0);
    if (int(nIn) + offset < 0 || int(txTo->vout.size()) <= int(nIn) + offset)
        return CTxOut();
    return txTo->vout[int(nIn) + offset];
}

COutPoint TransactionSignatureChecker::GetPrevOut() const
{
    return txTo->vin[nIn].prevout;
}

CConfidentialValue TransactionSignatureChecker::GetValueIn() const
{
    return amount;
}

CConfidentialValue TransactionSignatureChecker::GetValueInPrevIn() const
{
    return amountPreviousInput;
}

bool TransactionSignatureChecker::IsConfirmedBitcoinBlock(const uint256& genesishash, const uint256& hash, bool fConservativeConfirmationRequirements) const
{
#ifndef BITCOIN_SCRIPT_NO_CALLRPC
    return ::IsConfirmedBitcoinBlock(genesishash, hash, fConservativeConfirmationRequirements ? 10 : 8);
#else
    return true;
#endif
}

static bool VerifyWitnessProgram(const CScriptWitness& witness, int witversion, const std::vector<unsigned char>& program, unsigned int flags, const BaseSignatureChecker& checker, ScriptError* serror)
{
    vector<vector<unsigned char> > stack;
    CScript scriptPubKey;

    if (witversion == 0) {
        if (program.size() == 32) {
            // Version 0 segregated witness program: SHA256(CScript) inside the program, CScript + inputs in witness
            if (witness.stack.size() == 0) {
                return set_error(serror, SCRIPT_ERR_WITNESS_PROGRAM_WITNESS_EMPTY);
            }
            scriptPubKey = CScript(witness.stack.back().begin(), witness.stack.back().end());
            stack = std::vector<std::vector<unsigned char> >(witness.stack.begin(), witness.stack.end() - 1);
            uint256 hashScriptPubKey;
            CSHA256().Write(&scriptPubKey[0], scriptPubKey.size()).Finalize(hashScriptPubKey.begin());
            if (memcmp(hashScriptPubKey.begin(), &program[0], 32)) {
                return set_error(serror, SCRIPT_ERR_WITNESS_PROGRAM_MISMATCH);
            }
        } else if (program.size() == 20) {
            // Special case for pay-to-pubkeyhash; signature + pubkey in witness
            if (witness.stack.size() != 2) {
                return set_error(serror, SCRIPT_ERR_WITNESS_PROGRAM_MISMATCH); // 2 items in witness
            }
            scriptPubKey << OP_DUP << OP_HASH160 << program << OP_EQUALVERIFY << OP_CHECKSIG;
            stack = witness.stack;
        } else {
            return set_error(serror, SCRIPT_ERR_WITNESS_PROGRAM_WRONG_LENGTH);
        }
    } else if (flags & SCRIPT_VERIFY_DISCOURAGE_UPGRADABLE_WITNESS_PROGRAM) {
        return set_error(serror, SCRIPT_ERR_DISCOURAGE_UPGRADABLE_WITNESS_PROGRAM);
    } else {
        // Higher version witness scripts return true for future softfork compatibility
        return set_success(serror);
    }

    // Disallow stack item size > MAX_SCRIPT_ELEMENT_SIZE in witness stack
    for (unsigned int i = 0; i < stack.size(); i++) {
        if (stack.at(i).size() > MAX_SCRIPT_ELEMENT_SIZE)
            return set_error(serror, SCRIPT_ERR_PUSH_SIZE);
    }

    if (!EvalScript(stack, scriptPubKey, flags, checker, SIGVERSION_WITNESS_V0, serror)) {
        return false;
    }

    // Scripts inside witness implicitly require cleanstack behaviour
    if (stack.size() != 1)
        return set_error(serror, SCRIPT_ERR_EVAL_FALSE);
    if (!CastToBool(stack.back()))
        return set_error(serror, SCRIPT_ERR_EVAL_FALSE);
    return true;
}

bool VerifyScript(const CScript& scriptSig, const CScript& scriptPubKey, const CScriptWitness* witness, unsigned int flags, const BaseSignatureChecker& checker, ScriptError* serror)
{
    static const CScriptWitness emptyWitness;
    if (witness == NULL) {
        witness = &emptyWitness;
    }
    bool hadWitness = false;

    set_error(serror, SCRIPT_ERR_UNKNOWN_ERROR);

    if ((flags & SCRIPT_VERIFY_SIGPUSHONLY) != 0 && !scriptSig.IsPushOnly()) {
        return set_error(serror, SCRIPT_ERR_SIG_PUSHONLY);
    }

    // If the scriptPubKey is not in exactly the withdrawlock format we expect,
    // we will not execute WITHDRAW-related opcodes (treating them as NOPs)
    // Additionally, if the scriptPubKey is a withdraw lock, the scriptSig must
    // be push only.
    if ((flags & SCRIPT_VERIFY_WITHDRAW) != 0) {
        if (scriptPubKey.IsWithdrawLock()) {
            if (!scriptSig.IsPushOnly())
                return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_FORMAT);
        } else
            flags &= ~SCRIPT_VERIFY_WITHDRAW;
    }

    vector<vector<unsigned char> > stack, stackCopy;
    if (!EvalScript(stack, scriptSig, flags, checker, SIGVERSION_BASE, serror))
        // serror is set
        return false;
    if (flags & SCRIPT_VERIFY_P2SH)
        stackCopy = stack;
    if (!EvalScript(stack, scriptPubKey, flags, checker, SIGVERSION_BASE, serror))
        // serror is set
        return false;
    if (stack.empty())
        return set_error(serror, SCRIPT_ERR_EVAL_FALSE);
    if (CastToBool(stack.back()) == false)
        return set_error(serror, SCRIPT_ERR_EVAL_FALSE);

    // Bare witness programs
    int witnessversion;
    std::vector<unsigned char> witnessprogram;
    if (flags & SCRIPT_VERIFY_WITNESS) {
        if (scriptPubKey.IsWitnessProgram(witnessversion, witnessprogram)) {
            hadWitness = true;
            if (scriptSig.size() != 0) {
                // The scriptSig must be _exactly_ CScript(), otherwise we reintroduce malleability.
                return set_error(serror, SCRIPT_ERR_WITNESS_MALLEATED);
            }
            if (!VerifyWitnessProgram(*witness, witnessversion, witnessprogram, flags, checker, serror)) {
                return false;
            }
            // Bypass the cleanstack check at the end. The actual stack is obviously not clean
            // for witness programs.
            stack.resize(1);
        }
    }

    // Additional validation for spend-to-script-hash transactions:
    if ((flags & SCRIPT_VERIFY_P2SH) && scriptPubKey.IsPayToScriptHash())
    {
        // scriptSig must be literals-only or validation fails
        if (!scriptSig.IsPushOnly())
            return set_error(serror, SCRIPT_ERR_SIG_PUSHONLY);

        // Restore stack.
        swap(stack, stackCopy);

        // stack cannot be empty here, because if it was the
        // P2SH  HASH <> EQUAL  scriptPubKey would be evaluated with
        // an empty stack and the EvalScript above would return false.
        assert(!stack.empty());

        const valtype& pubKeySerialized = stack.back();
        CScript pubKey2(pubKeySerialized.begin(), pubKeySerialized.end());
        popstack(stack);

        if (!EvalScript(stack, pubKey2, flags, checker, SIGVERSION_BASE, serror))
            // serror is set
            return false;
        if (stack.empty())
            return set_error(serror, SCRIPT_ERR_EVAL_FALSE);
        if (!CastToBool(stack.back()))
            return set_error(serror, SCRIPT_ERR_EVAL_FALSE);

        // P2SH witness program
        if (flags & SCRIPT_VERIFY_WITNESS) {
            if (pubKey2.IsWitnessProgram(witnessversion, witnessprogram)) {
                hadWitness = true;
                if (scriptSig != CScript() << std::vector<unsigned char>(pubKey2.begin(), pubKey2.end())) {
                    // The scriptSig must be _exactly_ a single push of the redeemScript. Otherwise we
                    // reintroduce malleability.
                    return set_error(serror, SCRIPT_ERR_WITNESS_MALLEATED_P2SH);
                }
                if (!VerifyWitnessProgram(*witness, witnessversion, witnessprogram, flags, checker, serror)) {
                    return false;
                }
                // Bypass the cleanstack check at the end. The actual stack is obviously not clean
                // for witness programs.
                stack.resize(1);
            }
        }
    }

    // The CLEANSTACK check is only performed after potential P2SH evaluation,
    // as the non-P2SH evaluation of a P2SH script will obviously not result in
    // a clean stack (the P2SH inputs remain). The same holds for witness evaluation.
    if ((flags & SCRIPT_VERIFY_CLEANSTACK) != 0) {
        // Disallow CLEANSTACK without P2SH, as otherwise a switch CLEANSTACK->P2SH+CLEANSTACK
        // would be possible, which is not a softfork (and P2SH should be one).
        assert((flags & SCRIPT_VERIFY_P2SH) != 0);
        assert((flags & SCRIPT_VERIFY_WITNESS) != 0);
        if (stack.size() != 1 && (flags & SCRIPT_VERIFY_WITHDRAW) == 0) {
            return set_error(serror, SCRIPT_ERR_CLEANSTACK);
        }
    }

    if (flags & SCRIPT_VERIFY_WITNESS) {
        // We can't check for correct unexpected witness data if P2SH was off, so require
        // that WITNESS implies P2SH. Otherwise, going from WITNESS->P2SH+WITNESS would be
        // possible, which is not a softfork.
        assert((flags & SCRIPT_VERIFY_P2SH) != 0);
        if (!hadWitness && !witness->IsNull()) {
            return set_error(serror, SCRIPT_ERR_WITNESS_UNEXPECTED);
        }
    }

    return set_success(serror);
}

size_t static WitnessSigOps(int witversion, const std::vector<unsigned char>& witprogram, const CScriptWitness& witness, int flags)
{
    if (witversion == 0) {
        if (witprogram.size() == 20)
            return 1;

        if (witprogram.size() == 32 && witness.stack.size() > 0) {
            CScript subscript(witness.stack.back().begin(), witness.stack.back().end());
            return subscript.GetSigOpCount(true);
        }
    }

    // Future flags may be implemented here.
    return 0;
}

size_t CountWitnessSigOps(const CScript& scriptSig, const CScript& scriptPubKey, const CScriptWitness* witness, unsigned int flags)
{
    static const CScriptWitness witnessEmpty;

    if ((flags & SCRIPT_VERIFY_WITNESS) == 0) {
        return 0;
    }
    assert((flags & SCRIPT_VERIFY_P2SH) != 0);

    int witnessversion;
    std::vector<unsigned char> witnessprogram;
    if (scriptPubKey.IsWitnessProgram(witnessversion, witnessprogram)) {
        return WitnessSigOps(witnessversion, witnessprogram, witness ? *witness : witnessEmpty, flags);
    }

    if (scriptPubKey.IsPayToScriptHash() && scriptSig.IsPushOnly()) {
        CScript::const_iterator pc = scriptSig.begin();
        vector<unsigned char> data;
        while (pc < scriptSig.end()) {
            opcodetype opcode;
            scriptSig.GetOp(pc, opcode, data);
        }
        CScript subscript(data.begin(), data.end());
        if (subscript.IsWitnessProgram(witnessversion, witnessprogram)) {
            return WitnessSigOps(witnessversion, witnessprogram, witness ? *witness : witnessEmpty, flags);
        }
    }

    return 0;
}
