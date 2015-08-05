// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2014 The Bitcoin developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "interpreter.h"

#include <secp256k1.h>

#define FEDERATED_PEG_SIDECHAIN_ONLY
#ifdef FEDERATED_PEG_SIDECHAIN_ONLY
#include "callrpc.h"
#endif

#include "primitives/transaction.h"
#include "crypto/ripemd160.h"
#include "crypto/sha1.h"
#include "crypto/sha256.h"
#include "crypto/hmac_sha256.h"
#include "eccryptoverify.h"
#include "merkleblock.h"
#include "pow.h"
#include "pubkey.h"
#include "script/script.h"
#include "script/standard.h"
#include "streams.h"
#include "uint256.h"
#include "utilstrencodings.h"
#include "util.h"

using namespace std;

typedef vector<unsigned char> valtype;

//! anonymous namespace
namespace {

static secp256k1_context_t* secp256k1_context = NULL;

class CSecp256k1Init {
public:
    CSecp256k1Init() {
        assert(secp256k1_context == NULL);

        secp256k1_context_t *ctx = secp256k1_context_create(SECP256K1_CONTEXT_VERIFY);
        assert(ctx != NULL);

        secp256k1_context = ctx;
    }

    ~CSecp256k1Init() {
        secp256k1_context_t *ctx = secp256k1_context;
        secp256k1_context = NULL;

        if (ctx) {
            secp256k1_context_destroy(ctx);
        }
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
        throw runtime_error("popstack() : stack empty");
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

bool static IsDefinedHashtypeSignature(const valtype &vchSig) {
    if (vchSig.size() == 0) {
        return false;
    }
    unsigned char nHashType = vchSig[vchSig.size() - 1] & (~(SIGHASH_ANYONECANPAY));
    if (nHashType < SIGHASH_ALL || nHashType > SIGHASH_SINGLE)
        return false;

    return true;
}

bool static CheckSignatureEncoding(const valtype &vchSig, unsigned int flags, ScriptError* serror) {
    // Empty signature. Allowed to provide a compact way
    // to provide an invalid signature for use with CHECK(MULTI)SIG
    if (vchSig.size() == 0) {
        return true;
    }
    if ((flags & SCRIPT_VERIFY_STRICTENC) != 0 && !IsDefinedHashtypeSignature(vchSig)) {
        return set_error(serror, SCRIPT_ERR_SIG_HASHTYPE);
    }
    return true;
}

bool static CheckPubKeyEncoding(const valtype &vchSig, unsigned int flags, ScriptError* serror) {
    if ((flags & SCRIPT_VERIFY_STRICTENC) != 0 && !IsCompressedOrUncompressedPubKey(vchSig)) {
        return set_error(serror, SCRIPT_ERR_PUBKEYTYPE);
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

bool EvalScript(vector<vector<unsigned char> >& stack, const CScript& script, unsigned int flags, const BaseSignatureChecker& checker, ScriptError* serror)
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
    if (script.size() > 10000)
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
            if (opcode > OP_16 && ++nOpCount > 201)
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

                    // Note that unlike CHECKLOCKTIMEVERIFY we do not need to
                    // accept 5-byte bignums since any value greater than or
                    // equal to SEQUENCE_THRESHOLD (= 1 << 31) will be rejected
                    // anyway. This limitation just happens to coincide with
                    // CScriptNum's default 4-byte limit with an explicit sign
                    // bit.
                    //
                    // This means there is a maximum relative lock time of 52
                    // years, even though the nSequence field in transactions
                    // themselves is uint32_t and could allow a relative lock
                    // time of up to 120 years.
                    const CScriptNum nInvSequence(stacktop(-1), fRequireMinimal);

                    // In the rare event that the argument may be < 0 due to
                    // some arithmetic being done first, you can always use
                    // 0 MAX CHECKSEQUENCEVERIFY.
                    if (nInvSequence < 0)
                        return set_error(serror, SCRIPT_ERR_NEGATIVE_LOCKTIME);

                    // Actually compare the specified inverse sequence number
                    // with the input.
                    if (!checker.CheckLockTime(nInvSequence, true))
                        return set_error(serror, SCRIPT_ERR_UNSATISFIED_LOCKTIME);

                    break;
                }

                case OP_NOP1:
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

                        // start + length cannot overflow because of the restrictions immediately above
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

                    if (vch1.size() + full_bytes > MAX_SCRIPT_ELEMENT_SIZE)
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
                        CRIPEMD160().Write(begin_ptr(vch), vch.size()).Finalize(begin_ptr(vchHash));
                    else if (opcode == OP_SHA1)
                        CSHA1().Write(begin_ptr(vch), vch.size()).Finalize(begin_ptr(vchHash));
                    else if (opcode == OP_SHA256)
                        CSHA256().Write(begin_ptr(vch), vch.size()).Finalize(begin_ptr(vchHash));
                    else if (opcode == OP_HASH160)
                        CHash160().Write(begin_ptr(vch), vch.size()).Finalize(begin_ptr(vchHash));
                    else if (opcode == OP_HASH256)
                        CHash256().Write(begin_ptr(vch), vch.size()).Finalize(begin_ptr(vchHash));
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

                    // Drop the signature, since there's no way for a signature to sign itself
                    scriptCode.FindAndDelete(CScript(vchSig));

                    bool fSuccess = false;

                    if (!CheckSignatureEncoding(vchSig, flags, serror) || !CheckPubKeyEncoding(vchPubKey, flags, serror)) {
                        //serror is set
                        return false;
                    }

                    fSuccess = checker.CheckSig(vchSig, vchPubKey, scriptCode);

                    popstack(stack);
                    popstack(stack);
                    stack.push_back(fSuccess ? vchTrue : vchFalse);

                    if (opcode == OP_CHECKSIGVERIFY)
                        popstack(stack);

                    if (!fSuccess)
                        return set_error(serror, SCRIPT_ERR_CHECKSIGVERIFY);
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
                    if (nKeysCount < 0 || nKeysCount > 20)
                        return set_error(serror, SCRIPT_ERR_PUBKEY_COUNT);
                    nOpCount += nKeysCount;
                    if (nOpCount > 201)
                        return set_error(serror, SCRIPT_ERR_OP_COUNT);
                    int ikey = ++i;
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

                    // Drop the signatures, since there's no way for a signature to sign itself
                    for (int k = 0; k < nSigsCount; k++)
                    {
                        valtype& vchSig = stacktop(-isig-k);
                        scriptCode.FindAndDelete(CScript(vchSig));
                    }

                    bool fSuccess = true;
                    while (fSuccess && nSigsCount > 0)
                    {
                        valtype& vchSig    = stacktop(-isig);
                        valtype& vchPubKey = stacktop(-ikey);

                        // Note how this makes the exact order of pubkey/signature evaluation
                        // distinguishable by CHECKMULTISIG NOT if the STRICTENC flag is set.
                        // See the script_(in)valid tests for details.
                        if (!CheckSignatureEncoding(vchSig, flags, serror) || !CheckPubKeyEncoding(vchPubKey, flags, serror)) {
                            // serror is set
                            return false;
                        }

                        // Check signature
                        bool fOk = checker.CheckSig(vchSig, vchPubKey, scriptCode);

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
                    while (i-- > 1)
                        popstack(stack);

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
                        popstack(stack);

                    if (!fSuccess)
                        return set_error(serror, SCRIPT_ERR_CHECKMULTISIGVERIFY);
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

                    if (!CheckSignatureEncoding(vchSig, flags, serror) || !CheckPubKeyEncoding(vchPubKey, flags, serror)) {
                        //serror is set
                        return false;
                    }

                    valtype vchHash(32);
                    CSHA256().Write(begin_ptr(vchData), vchData.size()).Finalize(begin_ptr(vchHash));
                    uint256 hash(vchHash);

                    CPubKey pubkey(vchPubKey);
                    bool fSuccess = pubkey.Verify(hash, vchSig);

                    popstack(stack);
                    popstack(stack);
                    popstack(stack);
                    stack.push_back(fSuccess ? vchTrue : vchFalse);
                    if (opcode == OP_CHECKSIGFROMSTACKVERIFY)
                        popstack(stack);

                    if (!fSuccess)
                        return set_error(serror, SCRIPT_ERR_CHECKSIGVERIFY);
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
                    hasher.Write(begin_ptr(vchSeed), vchSeed.size());
                    do {
                        if (nHashIndex >= 3) {
                            //TODO this isn't endian safe
                            CSHA256(hasher).Write((const unsigned char*)&nCounter, sizeof(nCounter)).Finalize(begin_ptr(vchHash));
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

                //TODO: Need strict size limits on txn so that you cant be overly-large and break ds. reorg proofs
                case OP_WITHDRAWPROOFVERIFY:
                {
                    // In the make-withdraw case, reads the following from the stack:
                    // 1. HASH160(<...>) script which is used to extend checks
                    // 2. genesis block hash of the chain the withdraw is coming from
#ifndef FEDERATED_PEG_SIDECHAIN_ONLY
                    // TODO: 3. The compressed SPV proof
#endif
                    // 4. the coinbase tx within the locking block
                    // 5. the index within the locking tx's outputs we are claiming
                    // 6. the locking tx itself
                    // 7. the merkle block structure which contains the block in which
                    //    the locking transaction is present
#ifdef FEDERATED_PEG_SIDECHAIN_ONLY
                    // 8. The contract which we are expected to send coins to
#endif
                    // 8. The scriptSig used to satisfy the <...> script
                    // 9. <...> script which is used to extend checks
                    //
                    // In the combine-outputs case, reads the following from the stack:
                    // 1. HASH160(<...>) script which is used to extend checks
                    // 2. genesis block hash of the chain the withdraw is coming from

                    if (flags & SCRIPT_VERIFY_WITHDRAW) {
                        if (stack.size() < 10 && stack.size() != 2)
                            return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);

                        const valtype &vsecondScriptPubKeyHash = stacktop(-1);
                        if (vsecondScriptPubKeyHash.size() != 20)
                            return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_FORMAT);
                        const valtype &vgenesisHash = stacktop(-2);
                        if (vgenesisHash.size() != 32)
                            return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_FORMAT);

                        assert(checker.GetValueIn() != -1); // Not using a NoWithdrawSignatureChecker

                        if (stack.size() == 2) { // increasing value of locked coins
                            if (!checker.GetValueIn().IsAmount())
                                return set_error(serror, SCRIPT_ERR_WITHDRAW_VALUES_HIDDEN);
                            CAmount minValue = checker.GetValueIn().GetAmount();
                            CTxOut newOutput = checker.GetOutputOffsetFromCurrent(0);
                            if (newOutput.IsNull()) {
                                newOutput = checker.GetOutputOffsetFromCurrent(-1);
                                if (!checker.GetValueInPrevIn().IsAmount())
                                    return set_error(serror, SCRIPT_ERR_WITHDRAW_VALUES_HIDDEN);
                                minValue += checker.GetValueInPrevIn().GetAmount();
                            }
                            if (!newOutput.nValue.IsAmount())
                                return set_error(serror, SCRIPT_ERR_WITHDRAW_VALUES_HIDDEN);
                            if (newOutput.scriptPubKey != script || newOutput.nValue.GetAmount() < minValue)
                                return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_OUTPUT);
                        } else { // stack.size() == 10...ie regular withdraw
                            int stackReadPos = -3;
#ifndef FEDERATED_PEG_SIDECHAIN_ONLY
                            valtype vspvProof;
                            if (!WithdrawProofReadStackItem(stack, fRequireMinimal, &stackReadPos, vspvProof))
                                return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);
#endif

                            valtype vlockCoinbaseTx;
                            if (!WithdrawProofReadStackItem(stack, fRequireMinimal, &stackReadPos, vlockCoinbaseTx))
                                return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);

                            if (stack.size() < size_t(-stackReadPos))
                                return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);
                            const valtype &vlockTxOutIndex = stacktop(stackReadPos--);

                            valtype vlockTx;
                            if (!WithdrawProofReadStackItem(stack, fRequireMinimal, &stackReadPos, vlockTx))
                                return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);

                            valtype vmerkleBlock;
                            if (!WithdrawProofReadStackItem(stack, fRequireMinimal, &stackReadPos, vmerkleBlock))
                                return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);
#ifdef FEDERATED_PEG_SIDECHAIN_ONLY
                            if (stack.size() < size_t(-stackReadPos))
                                return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);
                            valtype vcontract = std::vector<unsigned char>(stacktop(stackReadPos--));
#endif
                            if (stack.size() < size_t(-stackReadPos))
                                return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);
                            const valtype &vsecondScriptSig = stacktop(stackReadPos--);
                            if (stack.size() < size_t(-stackReadPos))
                                return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);
                            const valtype &vsecondScriptPubKey = stacktop(stackReadPos--);

                            uint256 genesishash(vgenesisHash);

                            try {
                                CMerkleBlock merkleBlock;
                                merkleBlock.header.SetBitcoinBlock();
                                CDataStream merkleBlockStream(vmerkleBlock, SER_NETWORK, PROTOCOL_VERSION);
                                merkleBlockStream >> merkleBlock;
                                if (!merkleBlockStream.empty() || !CheckBitcoinProof(merkleBlock.header))
                                    return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_BLOCK);

                                vector<uint256> txHashes;
                                if (merkleBlock.txn.ExtractMatches(txHashes) != merkleBlock.header.hashMerkleRoot || txHashes.size() != 2)
                                    return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_BLOCK);

                                // We disallow returns from the genesis block, allowing sidechains to
                                // make genesis outputs spendable with a 21m initially-locked-to-btc
                                // distributing transaction.
                                if (merkleBlock.header.GetHash() == genesishash)
                                    return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_BLOCK);

#ifndef FEDERATED_PEG_SIDECHAIN_ONLY
                                //TODO: Check the SPV proof here (must point to genesishash, contain merkleBlock.header.GetHash())
#endif

                                CTransaction locktx;
                                CDataStream locktxStream(vlockTx, SER_NETWORK, PROTOCOL_VERSION | SERIALIZE_VERSION_MASK_BITCOIN_TX);
                                locktxStream >> locktx;
                                if (!locktxStream.empty())
                                    return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_LOCKTX);

                                int nlocktxOut = CScriptNum(vlockTxOutIndex, fRequireMinimal).getint();
                                if (nlocktxOut < 0 || (unsigned int)nlocktxOut >= locktx.vout.size())
                                    return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_LOCKTX);

                                if (locktx.GetBitcoinHash() != txHashes[1])
                                    return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_LOCKTX);

                                CTransaction coinbasetx;
                                CDataStream coinbasetxStream(vlockCoinbaseTx, SER_NETWORK, PROTOCOL_VERSION | SERIALIZE_VERSION_MASK_BITCOIN_TX);
                                coinbasetxStream >> coinbasetx;
                                if (!coinbasetxStream.empty())
                                    return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_BLOCK);

                                if (coinbasetx.GetBitcoinHash() != txHashes[0] || !coinbasetx.IsCoinBase())
                                    return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_BLOCK);
                                valtype vcoinbaseHeight;
                                CScript::const_iterator coinbasepc = coinbasetx.vin[0].scriptSig.begin();
                                opcodetype opcodeTmp;
                                if (!coinbasetx.vin[0].scriptSig.GetOp(coinbasepc, opcodeTmp, vcoinbaseHeight) || vcoinbaseHeight.size() < 1)
                                    return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_BLOCK);
                                int nLockHeight = CScriptNum(vcoinbaseHeight, fRequireMinimal).getint();

#ifdef FEDERATED_PEG_SIDECHAIN_ONLY
                                if (vcontract.size() != 40)
                                    return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_FORMAT);

                                // Duplicated in chainparams.cpp
                                CScript scriptDestination(CScript() << OP_5 << ParseHex("0269992fb441ae56968e5b77d46a3e53b69f136444ae65a94041fc937bdb28d933") << ParseHex("021df31471281d4478df85bfce08a10aab82601dca949a79950f8ddf7002bd915a") << ParseHex("02174c82021492c2c6dfcbfa4187d10d38bed06afb7fdcd72c880179fddd641ea1") << ParseHex("033f96e43d72c33327b6a4631ccaa6ea07f0b106c88b9dc71c9000bb6044d5e88a") << ParseHex("0313d8748790f2a86fb524579b46ce3c68fedd58d2a738716249a9f7d5458a15c2") << ParseHex("030b632eeb079eb83648886122a04c7bf6d98ab5dfb94cf353ee3e9382a4c2fab0") << ParseHex("02fb54a7fcaa73c307cfd70f3fa66a2e4247a71858ca731396343ad30c7c4009ce") << OP_7 << OP_CHECKMULTISIG);
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
                                            unsigned char *pub_start = &(*(sdpc - 33));
                                            CHMAC_SHA256(pub_start, 33).Write(&vcontract[0], 40).Finalize(tweak);
                                            // If someone creates a tweak that makes this fail, they broke SHA256
                                            secp256k1_pubkey_t pubkey;
                                            int pubkeylen = 33;
                                            assert(secp256k1_ec_pubkey_parse(secp256k1_context, &pubkey, pub_start, 33));
                                            assert(secp256k1_ec_pubkey_tweak_add(secp256k1_context, &pubkey, tweak) != 0);
                                            assert(secp256k1_ec_pubkey_serialize(secp256k1_context, pub_start, &pubkeylen, &pubkey, 1));
                                        }
                                    }
                                }

                                CScriptID expectedP2SH(scriptDestination);
                                if (locktx.vout[nlocktxOut].scriptPubKey != GetScriptForDestination(expectedP2SH))
                                    return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_OUTPUT);

                                vcontract.erase(vcontract.begin() + 4, vcontract.begin() + 20); // Remove the nonce from the contract before further processing
#else
                                const CScript &lockingScriptPubKey = locktx.vout[nlocktxOut].scriptPubKey;
                                //TODO: Make script checker expose GenesisBlockHash
                                if (!lockingScriptPubKey.IsWithdrawLock(checker.GenesisBlockHash(), true, true))
                                    return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_FORMAT);
                                valtype vcontract;
                                CScript::const_iterator locktxpc = lockingScriptPubKey.begin();
                                assert(lockingScriptPubKey.GetOp(locktxpc, opcodeTmp, vcontract));
                                if (vcontract.size() != 24)
                                    return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_FORMAT);
#endif
                                assert(vcontract.size() == 24);
                                if (vcontract[0] != 'P' || vcontract[1] != '2' || vcontract[2] != 'S' || vcontract[3] != 'H')
                                    return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_FORMAT);

                                if (!locktx.vout[nlocktxOut].nValue.IsAmount())
                                    return set_error(serror, SCRIPT_ERR_WITHDRAW_VALUES_HIDDEN);
                                CAmount withdrawVal = locktx.vout[nlocktxOut].nValue.GetAmount();
                                const CTxOut newLockOutput = checker.GetOutputOffsetFromCurrent(1);
                                if (!newLockOutput.nValue.IsAmount() || !checker.GetValueIn().IsAmount())
                                    return set_error(serror, SCRIPT_ERR_WITHDRAW_VALUES_HIDDEN);
                                if (newLockOutput.scriptPubKey != script || newLockOutput.nValue.GetAmount() < checker.GetValueIn().GetAmount() - withdrawVal)
                                    return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_OUTPUT);

                                const CTxOut withdrawOutput = checker.GetOutputOffsetFromCurrent(0);
                                if (!withdrawOutput.nValue.IsAmount())
                                    return set_error(serror, SCRIPT_ERR_WITHDRAW_VALUES_HIDDEN);
                                if (withdrawOutput.nValue.GetAmount() < withdrawVal)
                                    return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_OUTPUT);

                                uint256 locktxHash = locktx.GetBitcoinHash();
                                std::vector<unsigned char> vlocktxHash(locktxHash.begin(), locktxHash.end());
                                CScript expectedWithdrawScriptPubKeyStart = CScript() << OP_IF << nLockHeight
                                    << std::vector<unsigned char>(vlocktxHash.rbegin(), vlocktxHash.rend()) << nlocktxOut
#ifndef FEDERATED_PEG_SIDECHAIN_ONLY
                                    << 42 // (TODO: Measure of work from genesis to proof tip)
#endif
                                    << CScriptNum(withdrawOutput.nValue.GetAmount() - withdrawVal) // Fraud bounty
                                    << vsecondScriptPubKeyHash << vgenesisHash << OP_REORGPROOFVERIFY << OP_ELSE;
                                // << lockTime << OP_CHECKSEQUENCEVERIFY << OP_DROP << OP_HASH160
                                // << std::vector<unsigned char>(vcontract.begin() + 4, vcontract.begin() + 24) << OP_EQUAL << OP_ENDIF;
                                if (withdrawOutput.scriptPubKey.size() < expectedWithdrawScriptPubKeyStart.size() ||
                                        memcmp(&withdrawOutput.scriptPubKey[0], &expectedWithdrawScriptPubKeyStart[0], expectedWithdrawScriptPubKeyStart.size()) != 0)
                                    return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_OUTPUT);
                                CScript::const_iterator withdrawOutputpc = withdrawOutput.scriptPubKey.begin() + expectedWithdrawScriptPubKeyStart.size();
                                valtype vlockTime;
                                if (!withdrawOutput.scriptPubKey.GetOp(withdrawOutputpc, opcodeTmp, vlockTime))
                                    return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_OUTPUT);
                                int nWithdrawLockTime = CScriptNum(vlockTime, fRequireMinimal).getint();
                                if ((unsigned int)nWithdrawLockTime >= LOCKTIME_THRESHOLD || nWithdrawLockTime < 1)
                                    return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_LOCKTIME);

                                if (!withdrawOutput.scriptPubKey.GetOp(withdrawOutputpc, opcodeTmp, vlockTime) || opcodeTmp != OP_CHECKSEQUENCEVERIFY)
                                    return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_OUTPUT);
                                if (!withdrawOutput.scriptPubKey.GetOp(withdrawOutputpc, opcodeTmp, vlockTime) || opcodeTmp != OP_DROP)
                                    return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_OUTPUT);
                                if (!withdrawOutput.scriptPubKey.GetOp(withdrawOutputpc, opcodeTmp, vlockTime) || opcodeTmp != OP_HASH160)
                                    return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_OUTPUT);
                                if (!withdrawOutput.scriptPubKey.GetOp(withdrawOutputpc, opcodeTmp, vlockTime) || vlockTime != std::vector<unsigned char>(vcontract.begin() + 4, vcontract.begin() + 24))
                                    return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_OUTPUT);
                                if (!withdrawOutput.scriptPubKey.GetOp(withdrawOutputpc, opcodeTmp, vlockTime) || opcodeTmp != OP_EQUAL)
                                    return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_OUTPUT);
                                if (!withdrawOutput.scriptPubKey.GetOp(withdrawOutputpc, opcodeTmp, vlockTime) || opcodeTmp != OP_ENDIF)
                                    return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_OUTPUT);
                                if (withdrawOutput.scriptPubKey.GetOp(withdrawOutputpc, opcodeTmp, vlockTime))
                                    return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_OUTPUT);

                                valtype vsecondScriptPubKeyHashCmp(20);
                                CHash160().Write(begin_ptr(vsecondScriptPubKey), vsecondScriptPubKey.size()).Finalize(begin_ptr(vsecondScriptPubKeyHashCmp));
                                if (vsecondScriptPubKeyHash.size() != 20 || vsecondScriptPubKeyHashCmp != vsecondScriptPubKeyHash)
                                    return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_FORMAT);

                                vector<vector<unsigned char> > withdrawStack;
                                if (!EvalScript(withdrawStack, CScript(vsecondScriptSig), flags & ~SCRIPT_VERIFY_WITHDRAW, checker, serror))
                                    return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_SECONDSCRIPT);
                                // Push:
                                // 1. fee of this transaction (int64)
                                // 2. Fraud bounty (int64)
                                // 3. relative locktime
                                // 4. <1> indicating we are checking a withdraw proof
                                withdrawStack.push_back(CScriptNum(checker.GetTransactionFee()).getvch());
                                withdrawStack.push_back(CScriptNum(withdrawOutput.nValue.GetAmount() - withdrawVal).getvch());
                                withdrawStack.push_back(vlockTime);
                                withdrawStack.push_back(std::vector<unsigned char>(1, 1));
#ifndef FEDERATED_PEG_SIDECHAIN_ONLY
                                //TODO: Push a bunch of other info onto the withdrawStack about the SPV proof
#endif
                                if (!EvalScript(withdrawStack, CScript(vsecondScriptPubKey), flags & ~SCRIPT_VERIFY_WITHDRAW, checker, serror))
                                    return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_SECONDSCRIPT);
                                if (withdrawStack.empty() || CastToBool(withdrawStack.back()) == false)
                                    return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_SECONDSCRIPT);

#ifdef FEDERATED_PEG_SIDECHAIN_ONLY
                                if (!GetBoolArg("-blindtrust", true) && !checker.IsConfirmedBitcoinBlock(merkleBlock.header.GetHash(), flags & SCRIPT_VERIFY_INCREASE_CONFIRMATIONS_REQUIRED))
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

                case OP_REORGPROOFVERIFY:
                {
                    if (flags & SCRIPT_VERIFY_WITHDRAW) {
                        // Reads the following from the stack:
                        // 1. Genesis block hash
                        // 2. HASH160(<...>) script which is used to extend checks
                        // 3. Fraud bounty value (64-bit CScriptNum!)
#ifndef FEDERATED_PEG_SIDECHAIN_ONLY
                        // 4. Work used to create original proof
#endif
                        // 5. lock transaction output spent
                        // 6. lock transaction hash
                        // 7. lock transaction block height
                        // 8. proof type
                        int stackReadPos = -1;
                        if (stack.size() < 8)
                            return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);

                        assert(checker.GetValueIn() != -1); // Not using a NoWithdrawSignatureChecker

                        const valtype &vgenesisHash = stacktop(stackReadPos--);
                        if (vgenesisHash.size() != 32)
                            return set_error(serror, SCRIPT_ERR_REORG_VERIFY_FORMAT);

                        const valtype &vsecondScriptPubKeyHash = stacktop(stackReadPos--);
                        if (vsecondScriptPubKeyHash.size() != 20)
                            return set_error(serror, SCRIPT_ERR_REORG_VERIFY_FORMAT);

                        const valtype &vfraudBountyValue = stacktop(stackReadPos--);
#ifndef FEDERATED_PEG_SIDECHAIN_ONLY
                        const valtype &voriginalProofWork = stacktop(stackReadPos--);
#endif
                        int nlockTxOutIndex = CScriptNum(stacktop(stackReadPos--), fRequireMinimal).getint();
                        const valtype &vlockTxHashStack = stacktop(stackReadPos--);
                        if (vlockTxHashStack.size() != 32)
                            return set_error(serror, SCRIPT_ERR_REORG_VERIFY_FORMAT);
                        valtype vlockTxHash;
                        vlockTxHash.resize(32);
                        std::reverse_copy(vlockTxHashStack.begin(), vlockTxHashStack.end(), vlockTxHash.begin());

                        const valtype &vlockBlockHeight = stacktop(stackReadPos--);
                        int proofType = CScriptNum(stacktop(stackReadPos--), fRequireMinimal).getint();
                        if (proofType == 1) { // Double-spent withdraw
                            // We need to have complete proof that two transactions double-spent each other:
                            // So we read the following from the stack:
                            // 9. witness hash of the tx we are proving against (ie our input tx)
                            // 10. merkle block with tx we are proving against (ie our input tx)
                            // 11. the full transaction of the original withdraw
                            // 12. the input index in the transaction above which shows the double-spend
                            // 13. the transaction which is spent in the above input
                            // 14. merkle block containing the original withdraw tx, required only if they are not in the same block
                            if (stack.size() < size_t(-(stackReadPos)))
                                return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);
                            valtype vInputTxWitnessHash = stacktop(stackReadPos--);
                            if (vInputTxWitnessHash.size() != 32)
                                return set_error(serror, SCRIPT_ERR_REORG_VERIFY_FORMAT);

                            valtype vmerkleBlockInputTx;
                            if (!WithdrawProofReadStackItem(stack, fRequireMinimal, &stackReadPos, vmerkleBlockInputTx))
                                return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);

                            valtype voriginalWithdrawTx;
                            if (!WithdrawProofReadStackItem(stack, fRequireMinimal, &stackReadPos, voriginalWithdrawTx))
                                return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);

                            valtype voriginalWithdrawTxInIndex;
                            if (!WithdrawProofReadStackItem(stack, fRequireMinimal, &stackReadPos, voriginalWithdrawTxInIndex))
                                return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);

                            valtype voriginalWithdrawOutputTx;
                            if (!WithdrawProofReadStackItem(stack, fRequireMinimal, &stackReadPos, voriginalWithdrawOutputTx))
                                return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);

                            try {
                                CMerkleBlock merkleBlockInputTx;
                                CDataStream merkleBlockInputTxStream(vmerkleBlockInputTx, SER_NETWORK, PROTOCOL_VERSION);
                                merkleBlockInputTxStream >> merkleBlockInputTx;
                                if (!merkleBlockInputTxStream.empty() || !CheckProof(merkleBlockInputTx.header))
                                    return set_error(serror, SCRIPT_ERR_REORG_VERIFY_FRAUD_BLOCK);

                                vector<uint256> inputTxHashes;
                                if (merkleBlockInputTx.txn.ExtractMatches(inputTxHashes) != merkleBlockInputTx.header.hashMerkleRoot)
                                    return set_error(serror, SCRIPT_ERR_REORG_VERIFY_FRAUD_BLOCK);
                                if (inputTxHashes.size() != 1 && inputTxHashes.size() != 2)
                                    return set_error(serror, SCRIPT_ERR_REORG_VERIFY_FRAUD_BLOCK);

                                uint256 inputTxWitnessHash(vInputTxWitnessHash);
                                uint256 inputTxFullHash(checker.GetPrevOut().hash);
                                CHash256 hasher;
                                hasher.Write(inputTxFullHash.begin(), inputTxFullHash.size());
                                hasher.Write(inputTxWitnessHash.begin(), inputTxWitnessHash.size());
                                hasher.Finalize(inputTxFullHash.begin());

                                if (inputTxHashes[0] != inputTxFullHash)
                                    return set_error(serror, SCRIPT_ERR_REORG_VERIFY_FRAUD_BLOCK);

                                CTransaction originalWithdrawTx;
                                CDataStream originalWithdrawTxStream(voriginalWithdrawTx, SER_NETWORK, PROTOCOL_VERSION);
                                originalWithdrawTxStream >> originalWithdrawTx;
                                if (!originalWithdrawTxStream.empty())
                                    return set_error(serror, SCRIPT_ERR_REORG_VERIFY_FRAUD_ORIG_TX);

                                CMerkleBlock merkleBlockOriginalWithdrawTx;
                                vector<uint256> originalWithdrawHashes;
                                if (inputTxHashes.size() == 1) {
                                    valtype vmerkleBlockOriginalWithdrawTx;
                                    if (!WithdrawProofReadStackItem(stack, fRequireMinimal, &stackReadPos, vmerkleBlockOriginalWithdrawTx))
                                        return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);

                                    CDataStream merkleBlockOriginalWithdrawTxStream(vmerkleBlockOriginalWithdrawTx, SER_NETWORK, PROTOCOL_VERSION);
                                    merkleBlockOriginalWithdrawTxStream >> merkleBlockOriginalWithdrawTx;
                                    if (!merkleBlockOriginalWithdrawTxStream.empty() || !CheckProof(merkleBlockOriginalWithdrawTx.header))
                                        return set_error(serror, SCRIPT_ERR_REORG_VERIFY_FRAUD_ORIG_BLOCK);

                                    if (merkleBlockOriginalWithdrawTx.txn.ExtractMatches(originalWithdrawHashes) != merkleBlockOriginalWithdrawTx.header.hashMerkleRoot)
                                        return set_error(serror, SCRIPT_ERR_REORG_VERIFY_FRAUD_ORIG_BLOCK);
                                    if (originalWithdrawHashes.size() != 1 || merkleBlockOriginalWithdrawTx.header.GetHash() == merkleBlockInputTx.header.GetHash())
                                        return set_error(serror, SCRIPT_ERR_REORG_VERIFY_FRAUD_ORIG_BLOCK);

                                    if (originalWithdrawHashes[0] != originalWithdrawTx.GetFullHash())
                                        return set_error(serror, SCRIPT_ERR_REORG_VERIFY_FRAUD_ORIG_BLOCK);
                                } else if (inputTxHashes[1] != originalWithdrawTx.GetFullHash())
                                    return set_error(serror, SCRIPT_ERR_REORG_VERIFY_FRAUD_BLOCK);

                                int noriginalWithdrawTxIn = CScriptNum(voriginalWithdrawTxInIndex, fRequireMinimal).getint();
                                if (noriginalWithdrawTxIn < 0 || (unsigned int)noriginalWithdrawTxIn >= originalWithdrawTx.vin.size())
                                    return set_error(serror, SCRIPT_ERR_REORG_VERIFY_FRAUD_ORIG_TX);

                                const CTxIn& originalWithdrawTxInput = originalWithdrawTx.vin[noriginalWithdrawTxIn];

                                CTransaction originalWithdrawOutputTx;
                                CDataStream originalWithdrawOutputTxStream(voriginalWithdrawOutputTx, SER_NETWORK, PROTOCOL_VERSION);
                                originalWithdrawOutputTxStream >> originalWithdrawOutputTx;
                                if (!originalWithdrawOutputTxStream.empty() || originalWithdrawTxInput.prevout.hash != originalWithdrawOutputTx.GetHash())
                                    return set_error(serror, SCRIPT_ERR_REORG_VERIFY_FRAUD_ORIG_TX);
                                if (originalWithdrawOutputTx.vout.size() <= originalWithdrawTxInput.prevout.n)
                                    return set_error(serror, SCRIPT_ERR_REORG_VERIFY_FRAUD_ORIG_TX);

                                const CTxOut& originalWithdrawOutputTxOut = originalWithdrawOutputTx.vout[originalWithdrawTxInput.prevout.n];

                                if (!originalWithdrawOutputTxOut.scriptPubKey.IsWithdrawLock(0) || !originalWithdrawTxInput.scriptSig.IsWithdrawProof())
                                    return set_error(serror, SCRIPT_ERR_REORG_VERIFY_FRAUD_ORIG_TX);

                                COutPoint withdrawSpent = originalWithdrawTxInput.scriptSig.GetWithdrawSpent();
                                uint256 withdrawGenesisHash = originalWithdrawOutputTxOut.scriptPubKey.GetWithdrawLockGenesisHash();
                                if (withdrawGenesisHash != uint256(vgenesisHash) || withdrawSpent.hash != uint256(vlockTxHash) || withdrawSpent.n != uint32_t(nlockTxOutIndex) || nlockTxOutIndex < 0)
                                    return set_error(serror, SCRIPT_ERR_REORG_VERIFY_FRAUD_ORIG_TX);

                                const CTxOut newLockOutput = checker.GetOutputOffsetFromCurrent(0);
                                if (newLockOutput.scriptPubKey != (CScript() << vgenesisHash << vsecondScriptPubKeyHash << OP_WITHDRAWPROOFVERIFY))
                                    return set_error(serror, SCRIPT_ERR_REORG_VERIFY_FRAUD_OUTPUT);
                                CAmount fraudBounty = CScriptNum(vfraudBountyValue, fRequireMinimal, 8).getint64();
                                if (!newLockOutput.nValue.IsAmount() || !checker.GetValueIn().IsAmount())
                                    return set_error(serror, SCRIPT_ERR_REORG_VALUES_HIDDEN);
                                if (newLockOutput.nValue.GetAmount() < checker.GetValueIn().GetAmount() - fraudBounty)
                                    return set_error(serror, SCRIPT_ERR_REORG_VERIFY_FRAUD_OUTPUT);

                                //TODO: if (!checker.IsInBlockTreeAboveMe(merkleBlock.header.GetHash()))
                                //TODO:     return set_error(serror, SCRIPT_ERR_REORG_VERIFY);
                            } catch (std::exception& e) {
                                return set_error(serror, SCRIPT_ERR_REORG_VERIFY_FORMAT);
                            }
#ifndef FEDERATED_PEG_SIDECHAIN_ONLY
                        } else if (proofType == 2) { // Longer SPV chain
                            // Reads the following from the stack:
                            // 8. SPV Proof
                            // 9. <...> script which is used to extend checks
                            // 10. The scriptSig used to satisfy the <...> script
                            //TODO
#endif
                        } else
                            return set_error(serror, SCRIPT_ERR_REORG_VERIFY_FORMAT);
                    } // else...OP_NOP4
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
    const CTransaction &txTo;  //! reference to the spending transaction (the one being serialized)
    const CScript &scriptCode; //! output script being consumed
    const CTxOutValue &nValue; //! output value being spent
    const unsigned int nIn;    //! input index of txTo being signed
    const bool fAnyoneCanPay;  //! whether the hashtype has the SIGHASH_ANYONECANPAY flag set
    const bool fHashSingle;    //! whether the hashtype is SIGHASH_SINGLE
    const bool fHashNone;      //! whether the hashtype is SIGHASH_NONE

public:
    CTransactionSignatureSerializer(const CTransaction &txToIn, const CScript &scriptCodeIn, const CTxOutValue &nValueIn, unsigned int nInIn, int nHashTypeIn) :
        txTo(txToIn), scriptCode(scriptCodeIn), nValue(nValueIn), nIn(nInIn),
        fAnyoneCanPay(!!(nHashTypeIn & SIGHASH_ANYONECANPAY)),
        fHashSingle((nHashTypeIn & 0x1f) == SIGHASH_SINGLE),
        fHashNone((nHashTypeIn & 0x1f) == SIGHASH_NONE) {}

    /** Serialize the passed scriptCode, skipping OP_CODESEPARATORs */
    template<typename S>
    void SerializeScriptCode(S &s, int nType, int nVersion) const {
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
    void SerializeInput(S &s, unsigned int nInput, int nType, int nVersion) const {
        // In case of SIGHASH_ANYONECANPAY, only the input being signed is serialized
        if (fAnyoneCanPay)
            nInput = nIn;
        // Serialize the prevout
        ::Serialize(s, txTo.vin[nInput].prevout, nType, nVersion);

        // Serialize the output value
        ::Serialize(s, nValue, nType, nVersion);

        // Serialize the script
        if (nInput != nIn)
            // Blank out other inputs' signatures
            ::Serialize(s, CScript(), nType, nVersion);
        else
            SerializeScriptCode(s, nType, nVersion);
        // Serialize the nSequence
        if (nInput != nIn && (fHashSingle || fHashNone))
            // let the others update at will
            ::Serialize(s, (int)0, nType, nVersion);
        else
            ::Serialize(s, txTo.vin[nInput].nSequence, nType, nVersion);
    }

    /** Serialize an output of txTo */
    template<typename S>
    void SerializeOutput(S &s, unsigned int nOutput, int nType, int nVersion) const {
        if (fHashSingle && nOutput != nIn)
            // Do not lock-in the txout payee at other indices as txin
            ::Serialize(s, CTxOut(), nType, nVersion | SERIALIZE_VERSION_MASK_PREHASH);
        else
            ::Serialize(s, txTo.vout[nOutput], nType, nVersion | SERIALIZE_VERSION_MASK_PREHASH);
    }

    /** Serialize txTo */
    template<typename S>
    void Serialize(S &s, int nType, int nVersion) const {
        // Serialize nVersion
        ::Serialize(s, txTo.nVersion, nType, nVersion);
        // Serialize vin
        unsigned int nInputs = fAnyoneCanPay ? 1 : txTo.vin.size();
        ::WriteCompactSize(s, nInputs);
        for (unsigned int nInput = 0; nInput < nInputs; nInput++)
             SerializeInput(s, nInput, nType, nVersion);
        // Serialize vout
        unsigned int nOutputs = fHashNone ? 0 : (fHashSingle ? nIn+1 : txTo.vout.size());
        ::WriteCompactSize(s, nOutputs);
        for (unsigned int nOutput = 0; nOutput < nOutputs; nOutput++)
             SerializeOutput(s, nOutput, nType, nVersion);
        // Serialize nLockTime
        ::Serialize(s, txTo.nLockTime, nType, nVersion);
    }
};

} // anon namespace

uint256 SignatureHash(const CScript& scriptCode, const CTxOutValue& nAmount, const CTransaction& txTo, unsigned int nIn, int nHashType)
{
    if (nIn >= txTo.vin.size()) {
        //  nIn out of range
        return 1;
    }

    // Check for invalid use of SIGHASH_SINGLE
    if ((nHashType & 0x1f) == SIGHASH_SINGLE) {
        if (nIn >= txTo.vout.size()) {
            //  nOut out of range
            return 1;
        }
    }

    // Wrapper to serialize only the necessary parts of the transaction being signed
    CTransactionSignatureSerializer txTmp(txTo, scriptCode, nAmount, nIn, nHashType);

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

bool TransactionNoWithdrawsSignatureChecker::CheckSig(const vector<unsigned char>& vchSigIn, const vector<unsigned char>& vchPubKey, const CScript& scriptCode) const
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

    uint256 sighash = SignatureHash(scriptCode, GetValueIn(), *txTo, nIn, nHashType);

    if (!VerifySignature(vchSig, pubkey, sighash))
        return false;

    return true;
}

bool TransactionNoWithdrawsSignatureChecker::CheckLockTime(const CScriptNum& nLockTime, bool fSequence) const
{
    // Relative lock times are supported by comparing the passed
    // in lock time to the sequence number of the input. All other
    // logic is the same, all that differs is what we are comparing
    // the lock time to.
    int64_t txToLockTime;
    if (fSequence) {
        txToLockTime = (int64_t)~txTo->vin[nIn].nSequence;
        if (txToLockTime >= SEQUENCE_THRESHOLD)
            return false;
    } else {
        txToLockTime = (int64_t)txTo->nLockTime;
    }

    // There are two types of nLockTime: lock-by-blockheight
    // and lock-by-blocktime, distinguished by whether
    // nLockTime < LOCKTIME_THRESHOLD.
    //
    // We want to compare apples to apples, so fail the script
    // unless the type of nLockTime being tested is the same as
    // the nLockTime in the transaction.
    if (!(
        (txToLockTime <  LOCKTIME_THRESHOLD && nLockTime <  LOCKTIME_THRESHOLD) ||
        (txToLockTime >= LOCKTIME_THRESHOLD && nLockTime >= LOCKTIME_THRESHOLD)
    ))
        return false;

    // Now that we know we're comparing apples-to-apples, the
    // comparison is a simple numeric one.
    if (nLockTime > txToLockTime)
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
    if (!fSequence && !~txTo->vin[nIn].nSequence)
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

CTxOutValue TransactionNoWithdrawsSignatureChecker::GetValueIn() const
{
    return nInValue;
}

CAmount TransactionSignatureChecker::GetTransactionFee() const
{
    return nTransactionFee;
}

CTxOutValue TransactionSignatureChecker::GetValueInPrevIn() const
{
    return nInMinusOneValue;
}

#ifdef FEDERATED_PEG_SIDECHAIN_ONLY
bool TransactionSignatureChecker::IsConfirmedBitcoinBlock(const uint256& hash, bool fConservativeConfirmationRequirements) const
{
    return ::IsConfirmedBitcoinBlock(hash, fConservativeConfirmationRequirements ? 10 : 8);
}
#endif

bool VerifyScript(const CScript& scriptSig, const CScript& scriptPubKey, unsigned int flags, const BaseSignatureChecker& checker, ScriptError* serror)
{
    set_error(serror, SCRIPT_ERR_UNKNOWN_ERROR);

    if ((flags & SCRIPT_VERIFY_SIGPUSHONLY) != 0 && !scriptSig.IsPushOnly()) {
        return set_error(serror, SCRIPT_ERR_SIG_PUSHONLY);
    }

    // If the scriptPubKey is not in exactly the withdrawlock format we expect,
    // we will not execute WITHDRAW-related opcodes (treating them as NOPs)
    // Additionally, if the scriptPubKey is a withdraw lock, the scriptSig must
    // be exactly a withdraw proof (push only, in the right format), otherwise
    // it would either not be valid, or confuse the processing of double-spend
    // fraud proofs later.
    if ((flags & SCRIPT_VERIFY_WITHDRAW) != 0) {
        if (scriptPubKey.IsWithdrawLock(0)) {
            if (!scriptSig.IsWithdrawProof())
                return set_error(serror, SCRIPT_ERR_WITHDRAW_VERIFY_FORMAT);
        } else if (!scriptPubKey.IsWithdrawOutput())
            flags &= ~SCRIPT_VERIFY_WITHDRAW;
    }

    vector<vector<unsigned char> > stack, stackCopy;
    if (!EvalScript(stack, scriptSig, flags, checker, serror))
        // serror is set
        return false;
    if (flags & SCRIPT_VERIFY_P2SH)
        stackCopy = stack;
    if (!EvalScript(stack, scriptPubKey, flags, checker, serror))
        // serror is set
        return false;
    if (stack.empty())
        return set_error(serror, SCRIPT_ERR_EVAL_FALSE);

    if (CastToBool(stack.back()) == false)
        return set_error(serror, SCRIPT_ERR_EVAL_FALSE);

    bool checkP2SH = false;
    // Additional P2SH setup for withdraw outputs
    if ((flags & SCRIPT_VERIFY_WITHDRAW) != 0 && scriptPubKey.IsWithdrawOutput())
    {
        // stackCopy cannot be empty here, because if it was the
        // OP_IF that starts off the scriptPubKey would have failed
        assert(!stackCopy.empty());

        // If the stackCopy top is true, then we ran the
        // OP_REORGPROOFVERIFY branch, and do not need P2SH validation
        if (CastToBool(stackCopy[stackCopy.size() - 1]))
            return set_success(serror);

        popstack(stackCopy);

        if (stackCopy.empty())
            return set_error(serror, SCRIPT_ERR_INVALID_STACK_OPERATION);

        checkP2SH = true;
    }

    checkP2SH |= (flags & SCRIPT_VERIFY_P2SH) && scriptPubKey.IsPayToScriptHash();

    // Additional validation for spend-to-script-hash transactions:
    if (checkP2SH)
    {
        // scriptSig must be literals-only or validation fails
        if (!scriptSig.IsPushOnly())
            return set_error(serror, SCRIPT_ERR_SIG_PUSHONLY);

        // stackCopy cannot be empty here, because if it was the
        // P2SH  HASH <> EQUAL  scriptPubKey would be evaluated with
        // an empty stack and the EvalScript above would return false.
        assert(!stackCopy.empty());

        const valtype& pubKeySerialized = stackCopy.back();
        CScript pubKey2(pubKeySerialized.begin(), pubKeySerialized.end());
        popstack(stackCopy);

        if (!EvalScript(stackCopy, pubKey2, flags, checker, serror))
            // serror is set
            return false;
        if (stackCopy.empty())
            return set_error(serror, SCRIPT_ERR_EVAL_FALSE);
        if (!CastToBool(stackCopy.back()))
            return set_error(serror, SCRIPT_ERR_EVAL_FALSE);
        else
            return set_success(serror);
    }

    return set_success(serror);
}
