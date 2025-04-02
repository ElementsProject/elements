// Copyright (c) 2017-2022 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_RPC_UTIL_H
#define BITCOIN_RPC_UTIL_H

#include <node/transaction.h>
#include <outputtype.h>
#include <protocol.h>
#include <pubkey.h>
#include <rpc/protocol.h>
#include <rpc/request.h>
#include <script/script.h>
#include <script/sign.h>
#include <script/standard.h>
#include <univalue.h>
#include <util/check.h>

#include <string>
#include <variant>
#include <vector>

static constexpr bool DEFAULT_RPC_DOC_CHECK{
#ifdef RPC_DOC_CHECK
    true
#else
    false
#endif
};

/**
 * String used to describe UNIX epoch time in documentation, factored out to a
 * constant for consistency.
 */
extern const std::string UNIX_EPOCH_TIME;

/**
 * Example bech32 addresses for the RPCExamples help documentation. They are intentionally
 * invalid to prevent accidental transactions by users.
 */
extern const std::string EXAMPLE_ADDRESS[2];

class FillableSigningProvider;
class CPubKey;
class CScript;
struct Sections;

/**
 * Gets all existing output types formatted for RPC help sections.
 *
 * @return Comma separated string representing output type names.
 */
std::string GetAllOutputTypes();

/** Wrapper for UniValue::VType, which includes typeAny:
 * Used to denote don't care type. */
struct UniValueType {
    UniValueType(UniValue::VType _type) : typeAny(false), type(_type) {}
    UniValueType() : typeAny(true) {}
    bool typeAny;
    UniValue::VType type;
};

/**
 * Type-check one argument; throws JSONRPCError if wrong type given.
 */
void RPCTypeCheckArgument(const UniValue& value, const UniValueType& typeExpected);

/*
  Check for expected keys/value types in an Object.
*/
void RPCTypeCheckObj(const UniValue& o,
    const std::map<std::string, UniValueType>& typesExpected,
    bool fAllowNull = false,
    bool fStrict = false);

/**
 * Utilities: convert hex-encoded Values
 * (throws error if not hex).
 */
uint256 ParseHashV(const UniValue& v, std::string strName);
uint256 ParseHashO(const UniValue& o, std::string strKey);
std::vector<unsigned char> ParseHexV(const UniValue& v, std::string strName);
std::vector<unsigned char> ParseHexO(const UniValue& o, std::string strKey);

/**
 * Validate and return a CAmount from a UniValue number or string.
 *
 * @param[in] value     UniValue number or string to parse.
 * @param[in] decimals  Number of significant digits (default: 8).
 * @returns a CAmount if the various checks pass.
 */
CAmount AmountFromValue(const UniValue& value, bool check_range = true, int decimals = 8);

using RPCArgList = std::vector<std::pair<std::string, UniValue>>;
std::string HelpExampleCli(const std::string& methodname, const std::string& args);
std::string HelpExampleCliNamed(const std::string& methodname, const RPCArgList& args);
std::string HelpExampleRpc(const std::string& methodname, const std::string& args);
std::string HelpExampleRpcNamed(const std::string& methodname, const RPCArgList& args);

CPubKey HexToPubKey(const std::string& hex_in);
CPubKey AddrToPubKey(const FillableSigningProvider& keystore, const std::string& addr_in);
CTxDestination AddAndGetMultisigDestination(const int required, const std::vector<CPubKey>& pubkeys, OutputType type, FillableSigningProvider& keystore, CScript& script_out);

UniValue DescribeAddress(const CTxDestination& dest);
UniValue DescribeBlindAddress(const CTxDestination& dest);
CPubKey GetDestinationBlindingKey(const CTxDestination& dest);
bool IsBlindDestination(const CTxDestination& dest);

UniValue AmountMapToUniv(const CAmountMap& balanceOrig, std::string strasset);

//! Parse a confirm target option and raise an RPC error if it is invalid.
unsigned int ParseConfirmTarget(const UniValue& value, unsigned int max_target);

RPCErrorCode RPCErrorFromTransactionError(TransactionError terr);
UniValue JSONRPCTransactionError(TransactionError terr, const std::string& err_string = "");

//! Parse a JSON range specified as int64, or [int64, int64]
std::pair<int64_t, int64_t> ParseDescriptorRange(const UniValue& value);

/** Evaluate a descriptor given as a string, or as a {"desc":...,"range":...} object, with default range of 1000. */
std::vector<CScript> EvalDescriptorStringOrObject(const UniValue& scanobject, FlatSigningProvider& provider);

/** Returns, given services flags, a list of humanly readable (known) network services */
UniValue GetServicesNames(ServiceFlags services);

/**
 * Serializing JSON objects depends on the outer type. Only arrays and
 * dictionaries can be nested in json. The top-level outer type is "NONE".
 */
enum class OuterType {
    ARR,
    OBJ,
    NONE, // Only set on first recursion
};

struct RPCArgOptions {
    bool skip_type_check{false};
    std::string oneline_description{};   //!< Should be empty unless it is supposed to override the auto-generated summary line
    std::vector<std::string> type_str{}; //!< Should be empty unless it is supposed to override the auto-generated type strings. Vector length is either 0 or 2, m_opts.type_str.at(0) will override the type of the value in a key-value pair, m_opts.type_str.at(1) will override the type in the argument description.
    bool hidden{false};                  //!< For testing only
};

struct RPCArg {
    enum class Type {
        OBJ,
        ARR,
        STR,
        NUM,
        BOOL,
        OBJ_USER_KEYS, //!< Special type where the user must set the keys e.g. to define multiple addresses; as opposed to e.g. an options object where the keys are predefined
        AMOUNT,        //!< Special type representing a floating point amount (can be either NUM or STR)
        STR_HEX,       //!< Special type that is a STR with only hex chars
        RANGE,         //!< Special type that is a NUM or [NUM,NUM]
    };

    enum class Optional {
        /** Required arg */
        NO,
        /**
         * Optional arg that is a named argument and has a default value of
         * `null`. When possible, the default value should be specified.
         */
        OMITTED_NAMED_ARG,
        /**
         * Optional argument with default value omitted because they are
         * implicitly clear. That is, elements in an array or object may not
         * exist by default.
         * When possible, the default value should be specified.
         */
        OMITTED,
    };
    using DefaultHint = std::string;
    using Default = UniValue;
    using Fallback = std::variant<Optional, /* hint for default value */ DefaultHint, /* default constant value */ Default>;

    const std::string m_names; //!< The name of the arg (can be empty for inner args, can contain multiple aliases separated by | for named request arguments)
    const Type m_type;
    const std::vector<RPCArg> m_inner; //!< Only used for arrays or dicts
    const Fallback m_fallback;
    const std::string m_description;
    const RPCArgOptions m_opts;

    RPCArg(
        const std::string name,
        const Type type,
        const Fallback fallback,
        const std::string description,
        RPCArgOptions opts = {})
        : m_names{std::move(name)},
          m_type{std::move(type)},
          m_fallback{std::move(fallback)},
          m_description{std::move(description)},
          m_opts{std::move(opts)}
    {
        CHECK_NONFATAL(type != Type::ARR && type != Type::OBJ && type != Type::OBJ_USER_KEYS);
    }

    RPCArg(
        const std::string name,
        const Type type,
        const Fallback fallback,
        const std::string description,
        const std::vector<RPCArg> inner,
        RPCArgOptions opts = {})
        : m_names{std::move(name)},
          m_type{std::move(type)},
          m_inner{std::move(inner)},
          m_fallback{std::move(fallback)},
          m_description{std::move(description)},
          m_opts{std::move(opts)}
    {
        CHECK_NONFATAL(type == Type::ARR || type == Type::OBJ || type == Type::OBJ_USER_KEYS);
    }

    bool IsOptional() const;

    /** Check whether the request JSON type matches. */
    void MatchesType(const UniValue& request) const;

    /** Return the first of all aliases */
    std::string GetFirstName() const;

    /** Return the name, throws when there are aliases */
    std::string GetName() const;

    /**
     * Return the type string of the argument.
     * Set oneline to allow it to be overridden by a custom oneline type string (m_opts.oneline_description).
     */
    std::string ToString(bool oneline) const;
    /**
     * Return the type string of the argument when it is in an object (dict).
     * Set oneline to get the oneline representation (less whitespace)
     */
    std::string ToStringObj(bool oneline) const;
    /**
     * Return the description string, including the argument type and whether
     * the argument is required.
     */
    std::string ToDescriptionString() const;
};

struct RPCResult {
    enum class Type {
        OBJ,
        ARR,
        STR,
        NUM,
        BOOL,
        NONE,
        ANY,        //!< Special type to disable type checks (for testing only)
        STR_AMOUNT, //!< Special string to represent a floating point amount
        STR_HEX,    //!< Special string with only hex chars
        OBJ_DYN,    //!< Special dictionary with keys that are not literals
        ARR_FIXED,  //!< Special array that has a fixed number of entries
        NUM_TIME,   //!< Special numeric to denote unix epoch time
        ELISION,    //!< Special type to denote elision (...)
    };

    const Type m_type;
    const std::string m_key_name;         //!< Only used for dicts
    const std::vector<RPCResult> m_inner; //!< Only used for arrays or dicts
    const bool m_optional;
    const bool m_skip_type_check;
    const std::string m_description;
    const std::string m_cond;

    RPCResult(
        const std::string cond,
        const Type type,
        const std::string m_key_name,
        const bool optional,
        const std::string description,
        const std::vector<RPCResult> inner = {})
        : m_type{std::move(type)},
          m_key_name{std::move(m_key_name)},
          m_inner{std::move(inner)},
          m_optional{optional},
          m_skip_type_check{false},
          m_description{std::move(description)},
          m_cond{std::move(cond)}
    {
        CHECK_NONFATAL(!m_cond.empty());
        CheckInnerDoc();
    }

    RPCResult(
        const std::string cond,
        const Type type,
        const std::string m_key_name,
        const std::string description,
        const std::vector<RPCResult> inner = {})
        : RPCResult{cond, type, m_key_name, false, description, inner} {}

    RPCResult(
        const Type type,
        const std::string m_key_name,
        const bool optional,
        const std::string description,
        const std::vector<RPCResult> inner = {},
        bool skip_type_check = false)
        : m_type{std::move(type)},
          m_key_name{std::move(m_key_name)},
          m_inner{std::move(inner)},
          m_optional{optional},
          m_skip_type_check{skip_type_check},
          m_description{std::move(description)},
          m_cond{}
    {
        CheckInnerDoc();
    }

    RPCResult(
        const Type type,
        const std::string m_key_name,
        const std::string description,
        const std::vector<RPCResult> inner = {},
        bool skip_type_check = false)
        : RPCResult{type, m_key_name, false, description, inner, skip_type_check} {}

    /** Append the sections of the result. */
    void ToSections(Sections& sections, OuterType outer_type = OuterType::NONE, const int current_indent = 0) const;
    /** Return the type string of the result when it is in an object (dict). */
    std::string ToStringObj() const;
    /** Return the description string, including the result type. */
    std::string ToDescriptionString() const;
    /** Check whether the result JSON type matches. */
    bool MatchesType(const UniValue& result) const;

private:
    void CheckInnerDoc() const;
};

struct RPCResults {
    const std::vector<RPCResult> m_results;

    RPCResults(RPCResult result)
        : m_results{{result}}
    {
    }

    RPCResults(std::initializer_list<RPCResult> results)
        : m_results{results}
    {
    }

    /**
     * Return the description string.
     */
    std::string ToDescriptionString() const;
};

struct RPCExamples {
    const std::string m_examples;
    explicit RPCExamples(
        std::string examples)
        : m_examples(std::move(examples))
    {
    }
    std::string ToDescriptionString() const;
};

class RPCHelpMan
{
public:
    RPCHelpMan(std::string name, std::string description, std::vector<RPCArg> args, RPCResults results, RPCExamples examples);
    using RPCMethodImpl = std::function<UniValue(const RPCHelpMan&, const JSONRPCRequest&)>;
    RPCHelpMan(std::string name, std::string description, std::vector<RPCArg> args, RPCResults results, RPCExamples examples, RPCMethodImpl fun);

    UniValue HandleRequest(const JSONRPCRequest& request) const;
    std::string ToString() const;
    /** Return the named args that need to be converted from string to another JSON type */
    UniValue GetArgMap() const;
    /** If the supplied number of args is neither too small nor too high */
    bool IsValidNumArgs(size_t num_args) const;
    std::vector<std::string> GetArgNames() const;

    const std::string m_name;

private:
    const RPCMethodImpl m_fun;
    const std::string m_description;
    const std::vector<RPCArg> m_args;
    const RPCResults m_results;
    const RPCExamples m_examples;
};

#endif // BITCOIN_RPC_UTIL_H
