#include "callrpc.h"
#include "chainparamsbase.h"
#include "util.h"
#include "utilstrencodings.h"

using namespace std;
using namespace boost;
using namespace boost::asio;
using namespace json_spirit;

#define _(x) std::string(x) /* Keep the _() around in case gettext or such will be used later to translate non-UI */

Object CallRPC(const string& strMethod, const Array& params, string port)
{
    if (mapArgs["-rpcuser"] == "" && mapArgs["-rpcpassword"] == "")
        throw runtime_error(strprintf(
            _("You must set rpcpassword=<password> in the configuration file:\n%s\n"
              "If the file does not exist, create it with owner-readable-only file permissions."),
                GetConfigFile().string().c_str()));

    // Connect to localhost
    bool fUseSSL = GetBoolArg("-rpcssl", false);
    asio::io_service io_service;
    ssl::context context(io_service, ssl::context::sslv23);
    context.set_options(ssl::context::no_sslv2 | ssl::context::no_sslv3);
    asio::ssl::stream<asio::ip::tcp::socket> sslStream(io_service, context);
    SSLIOStreamDevice<asio::ip::tcp> d(sslStream, fUseSSL);
    iostreams::stream< SSLIOStreamDevice<asio::ip::tcp> > stream(d);

    if (port == "")
        port = GetArg("-rpcport", itostr(BaseParams().RPCPort()));
    const bool fConnected = d.connect(GetArg("-rpcconnect", "127.0.0.1"), port);
    if (!fConnected)
        throw CConnectionFailed("couldn't connect to server");

    // HTTP basic authentication
    string strUserPass64 = EncodeBase64(mapArgs["-rpcuser"] + ":" + mapArgs["-rpcpassword"]);
    map<string, string> mapRequestHeaders;
    mapRequestHeaders["Authorization"] = string("Basic ") + strUserPass64;

    // Send request
    string strRequest = JSONRPCRequest(strMethod, params, 1);
    string strPost = HTTPPost(strRequest, mapRequestHeaders);
    stream << strPost << std::flush;

    // Receive HTTP reply status
    int nProto = 0;
    int nStatus = ReadHTTPStatus(stream, nProto);

    // Receive HTTP reply message headers and body
    map<string, string> mapHeaders;
    string strReply;
    ReadHTTPMessage(stream, mapHeaders, strReply, nProto, std::numeric_limits<size_t>::max());

    if (nStatus == HTTP_UNAUTHORIZED)
        throw runtime_error("incorrect rpcuser or rpcpassword (authorization failed)");
    else if (nStatus >= 400 && nStatus != HTTP_BAD_REQUEST && nStatus != HTTP_NOT_FOUND && nStatus != HTTP_INTERNAL_SERVER_ERROR)
        throw runtime_error(strprintf("server returned HTTP error %d", nStatus));
    else if (strReply.empty())
        throw runtime_error("no response from server");

    // Parse reply
    Value valReply;
    if (!read_string(strReply, valReply))
        throw runtime_error("couldn't parse reply from server");
    const Object& reply = valReply.get_obj();
    if (reply.empty())
        throw runtime_error("expected reply to have result, error and id properties");

    return reply;
}

bool IsConfirmedBitcoinBlock(const uint256& hash, int nMinConfirmationDepth)
{
    try {
        Array params;
        params.push_back(hash.GetHex());
        Object reply = CallRPC("getblock", params, GetArg("-rpcconnectport", "18332"));
        if (find_value(reply, "error").type() != null_type)
            return false;
        Value result = find_value(reply, "result");
        if (result.type() != obj_type)
            return false;
        result = find_value(result.get_obj(), "confirmations");
        return result.type() == int_type && result.get_int64() >= nMinConfirmationDepth;
    } catch (CConnectionFailed& e) {
        LogPrintf("ERROR: Lost connection to alphad RPC, you will want to restart after fixing this!\n");
        return false;
    } catch (...) {
        LogPrintf("ERROR: Failure connecting to alphad RPC, you will want to restart after fixing this!\n");
        return false;
    }
    return true;
}
