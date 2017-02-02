#include "chainparamsbase.h"
#include "callrpc.h"
#include "util.h"
#include "utilstrencodings.h"
#include "rpc/protocol.h"

#include <event2/event.h>
#include <event2/http.h>
#include <event2/buffer.h>
#include <event2/keyvalq_struct.h>

using namespace std;

/** Reply structure for request_done to fill in */
struct HTTPReply
{
    int status;
    std::string body;
};

static void http_request_done(struct evhttp_request *req, void *ctx)
{
    HTTPReply *reply = static_cast<HTTPReply*>(ctx);

    if (req == NULL) {
        /* If req is NULL, it means an error occurred while connecting, but
         * I'm not sure how to find out which one. We also don't really care.
         */
        reply->status = 0;
        return;
    }

    reply->status = evhttp_request_get_response_code(req);

    struct evbuffer *buf = evhttp_request_get_input_buffer(req);
    if (buf)
    {
        size_t size = evbuffer_get_length(buf);
        const char *data = (const char*)evbuffer_pullup(buf, size);
        if (data)
            reply->body = std::string(data, size);
        evbuffer_drain(buf, size);
    }
}

UniValue CallRPC(const string& strMethod, const UniValue& params, bool connectToMainchain)
{
    std::string strhost = "-rpcconnect";
    std::string strport = "-rpcport";
    std::string struser = "-rpcuser";
    std::string strpassword = "-rpcpassword";

    int port = GetArg(strport, BaseParams().RPCPort());

    if (connectToMainchain) {
        strhost = "-mainchainhost";
        strport = "-mainchainrpcport";
        strpassword = "-mainchainrpcpassword";
        struser = "-mainchainrpcuser";
        port = GetArg(strport, BaseParams().MainchainRPCPort());
    }

    std::string host = GetArg(strhost, DEFAULT_RPCHOST);
    // Create event base
    struct event_base *base = event_base_new(); // TODO RAII
    if (!base)
        throw runtime_error("cannot create event_base");

    // Synchronously look up hostname
    struct evhttp_connection *evcon = evhttp_connection_base_new(base, NULL, host.c_str(), port); // TODO RAII
    if (evcon == NULL)
        throw runtime_error("create connection failed");
    evhttp_connection_set_timeout(evcon, GetArg("-rpcclienttimeout", DEFAULT_HTTP_CLIENT_TIMEOUT));

    HTTPReply response;
    struct evhttp_request *req = evhttp_request_new(http_request_done, (void*)&response); // TODO RAII
    if (req == NULL)
        throw runtime_error("create http request failed");

    // Get credentials
    std::string strRPCUserColonPass;
    if (mapArgs[strpassword] == "") {

        // Try fall back to cookie-based authentication if no password is provided
        if (!connectToMainchain && !GetAuthCookie(&strRPCUserColonPass)) {
            throw runtime_error(strprintf(
                _("Could not locate RPC credentials. No authentication cookie could be found, and no rpcpassword is set in the configuration file (%s)"),
                    GetConfigFile().string().c_str()));
        }

        // Try fall back to cookie-based authentication if no password is provided
        if (connectToMainchain && !GetMainchainAuthCookie(&strRPCUserColonPass)) {
            throw runtime_error(strprintf(
                _("Could not locate mainchain RPC credentials. No authentication cookie could be found, and no mainchainrpcpassword is set in the configuration file (%s)"),
                    GetConfigFile().string().c_str()));

        }
    } else {
        if (struser == "")
            throw runtime_error(
                 _("Could not locate mainchain RPC credentials. No authentication cookie could be found, and no mainchainrpcuser is set in the configuration file"));
        else
            strRPCUserColonPass = mapArgs[struser] + ":" + mapArgs[strpassword];
    }

    struct evkeyvalq *output_headers = evhttp_request_get_output_headers(req);
    assert(output_headers);
    evhttp_add_header(output_headers, "Host", host.c_str());
    evhttp_add_header(output_headers, "Connection", "close");
    evhttp_add_header(output_headers, "Authorization", (std::string("Basic ") + EncodeBase64(strRPCUserColonPass)).c_str());

    // Attach request data
    std::string strRequest = JSONRPCRequest(strMethod, params, 1);
    struct evbuffer * output_buffer = evhttp_request_get_output_buffer(req);
    assert(output_buffer);
    evbuffer_add(output_buffer, strRequest.data(), strRequest.size());

    int r = evhttp_make_request(evcon, req, EVHTTP_REQ_POST, "/");
    if (r != 0) {
        evhttp_connection_free(evcon);
        event_base_free(base);
        throw CConnectionFailed("send http request failed");
    }

    event_base_dispatch(base);
    evhttp_connection_free(evcon);
    event_base_free(base);

    if (response.status == 0)
        throw CConnectionFailed("couldn't connect to server (make sure daemon is running and you are using the right rpc port)");
    else if (response.status == HTTP_UNAUTHORIZED)
        if (connectToMainchain)
            throw runtime_error("incorrect mainchainrpcuser or mainchainrpcpassword (authorization failed)");
        else
            throw runtime_error("incorrect rpcuser or rpcpassword (authorization failed)");
    else if (response.status >= 400 && response.status != HTTP_BAD_REQUEST && response.status != HTTP_NOT_FOUND && response.status != HTTP_INTERNAL_SERVER_ERROR)
        throw runtime_error(strprintf("server returned HTTP error %d", response.status));
    else if (response.body.empty())
        throw runtime_error("no response from server");

    // Parse reply
    UniValue valReply(UniValue::VSTR);
    if (!valReply.read(response.body))
        throw runtime_error("couldn't parse reply from server");
    const UniValue& reply = valReply.get_obj();
    if (reply.empty())
        throw runtime_error("expected reply to have result, error and id properties");

    return reply;
}

bool IsConfirmedBitcoinBlock(const uint256& genesishash, const uint256& hash, int nMinConfirmationDepth)
{

    try {
        UniValue params(UniValue::VARR);
        params.push_back(UniValue(0));
        UniValue reply = CallRPC("getblockhash", params, true);
        if (!find_value(reply, "error").isNull())
            return false;
        UniValue result = find_value(reply, "result");
        if (!result.isStr())
            return false;
        if (result.get_str() != genesishash.GetHex())
            return false;

        params = UniValue(UniValue::VARR);
        params.push_back(hash.GetHex());
        reply = CallRPC("getblock", params, true);
        if (!find_value(reply, "error").isNull())
            return false;
        result = find_value(reply, "result");
        if (!result.isObject())
            return false;
        result = find_value(result.get_obj(), "confirmations");
        return result.isNum() && result.get_int64() >= nMinConfirmationDepth;
    } catch (CConnectionFailed& e) {
        LogPrintf("ERROR: Lost connection to bitcoind RPC, you will want to restart after fixing this!\n");
        return false;
    } catch (...) {
        LogPrintf("ERROR: Failure connecting to bitcoind RPC, you will want to restart after fixing this!\n");
        return false;
    }
    return true;
}
