#include "chainparamsbase.h"
#include "callrpc.h"
#include "util.h"
#include "utilstrencodings.h"
#include "rpc/protocol.h"

#include "support/events.h"

#include "rpc/client.h"

#include <event2/buffer.h>
#include <event2/keyvalq_struct.h>

/** Reply structure for request_done to fill in */
struct HTTPReply
{
    HTTPReply(): status(0), error(-1) {}

    int status;
    int error;
    std::string body;
};

const char *http_errorstring(int code)
{
    switch(code) {
#if LIBEVENT_VERSION_NUMBER >= 0x02010300
    case EVREQ_HTTP_TIMEOUT:
        return "timeout reached";
    case EVREQ_HTTP_EOF:
        return "EOF reached";
    case EVREQ_HTTP_INVALID_HEADER:
        return "error while reading header, or invalid header";
    case EVREQ_HTTP_BUFFER_ERROR:
        return "error encountered while reading or writing";
    case EVREQ_HTTP_REQUEST_CANCEL:
        return "request was canceled";
    case EVREQ_HTTP_DATA_TOO_LONG:
        return "response body is larger than allowed";
#endif
    default:
        return "unknown";
    }
}

static void http_request_done(struct evhttp_request *req, void *ctx)
{
    HTTPReply *reply = static_cast<HTTPReply*>(ctx);

    if (req == NULL) {
        /* If req is NULL, it means an error occurred while connecting: the
         * error code will have been passed to http_error_cb.
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

#if LIBEVENT_VERSION_NUMBER >= 0x02010300
static void http_error_cb(enum evhttp_request_error err, void *ctx)
{
    HTTPReply *reply = static_cast<HTTPReply*>(ctx);
    reply->error = err;
}
#endif

UniValue CallRPC(const std::string& strMethod, const UniValue& params, bool connectToMainchain)
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

    std::string host = GetArg(strhost, DEFAULT_RPCCONNECT);
    // Obtain event base
    raii_event_base base = obtain_event_base();

    // Synchronously look up hostname
    raii_evhttp_connection evcon = obtain_evhttp_connection_base(base.get(), host, port);
    evhttp_connection_set_timeout(evcon.get(), GetArg("-rpcclienttimeout", DEFAULT_HTTP_CLIENT_TIMEOUT));

    HTTPReply response;
    raii_evhttp_request req = obtain_evhttp_request(http_request_done, (void*)&response);
    if (req == NULL)
        throw std::runtime_error("create http request failed");
#if LIBEVENT_VERSION_NUMBER >= 0x02010300
    evhttp_request_set_error_cb(req.get(), http_error_cb);
#endif

    // Get credentials
    std::string strRPCUserColonPass;
    if (GetArg("-rpcpassword", "") == "") {

        // Try fall back to cookie-based authentication if no password is provided
        if (!connectToMainchain && !GetAuthCookie(&strRPCUserColonPass)) {
            throw std::runtime_error(strprintf(
                _("Could not locate RPC credentials. No authentication cookie could be found, and no rpcpassword is set in the configuration file (%s)"),
                    GetConfigFile(GetArg("-conf", BITCOIN_CONF_FILENAME)).string().c_str()));
        }

        // Try fall back to cookie-based authentication if no password is provided
        if (connectToMainchain && !GetMainchainAuthCookie(&strRPCUserColonPass)) {
            throw std::runtime_error(strprintf(
                _("Could not locate mainchain RPC credentials. No authentication cookie could be found, and no mainchainrpcpassword is set in the configuration file (%s)"),
                    GetConfigFile(GetArg("-conf", BITCOIN_CONF_FILENAME)).string().c_str()));

        }
    } else {
        if (struser == "")
            throw std::runtime_error(
                 _("Could not locate mainchain RPC credentials. No authentication cookie could be found, and no mainchainrpcuser is set in the configuration file"));
        else
            strRPCUserColonPass = GetArg(struser, "") + ":" + GetArg(strpassword, "");
    }

    struct evkeyvalq* output_headers = evhttp_request_get_output_headers(req.get());
    assert(output_headers);
    evhttp_add_header(output_headers, "Host", host.c_str());
    evhttp_add_header(output_headers, "Connection", "close");
    evhttp_add_header(output_headers, "Authorization", (std::string("Basic ") + EncodeBase64(strRPCUserColonPass)).c_str());

    // Attach request data
    std::string strRequest = JSONRPCRequestObj(strMethod, params, 1).write() + "\n";
    struct evbuffer* output_buffer = evhttp_request_get_output_buffer(req.get());
    assert(output_buffer);
    evbuffer_add(output_buffer, strRequest.data(), strRequest.size());

    int r = evhttp_make_request(evcon.get(), req.get(), EVHTTP_REQ_POST, "/");
    req.release(); // ownership moved to evcon in above call
    if (r != 0) {
        throw CConnectionFailed("send http request failed");
    }

    event_base_dispatch(base.get());

    if (response.status == 0)
        throw CConnectionFailed(strprintf("couldn't connect to server: %s (code %d)\n(make sure server is running and you are connecting to the correct RPC port)", http_errorstring(response.error), response.error));
    else if (response.status == HTTP_UNAUTHORIZED)
        if (connectToMainchain)
            throw std::runtime_error("incorrect mainchainrpcuser or mainchainrpcpassword (authorization failed)");
        else
            throw std::runtime_error("incorrect rpcuser or rpcpassword (authorization failed)");
    else if (response.status >= 400 && response.status != HTTP_BAD_REQUEST && response.status != HTTP_NOT_FOUND && response.status != HTTP_INTERNAL_SERVER_ERROR)
        throw std::runtime_error(strprintf("server returned HTTP error %d", response.status));
    else if (response.body.empty())
        throw std::runtime_error("no response from server");

    // Parse reply
    UniValue valReply(UniValue::VSTR);
    if (!valReply.read(response.body))
        throw std::runtime_error("couldn't parse reply from server");
    const UniValue& reply = valReply.get_obj();
    if (reply.empty())
        throw std::runtime_error("expected reply to have result, error and id properties");

    return reply;
}

bool IsConfirmedBitcoinBlock(const uint256& hash, int nMinConfirmationDepth)
{
    try {
        UniValue params(UniValue::VARR);
        params.push_back(hash.GetHex());
        UniValue reply = CallRPC("getblockheader", params, true);
        if (!find_value(reply, "error").isNull())
            return false;
        UniValue result = find_value(reply, "result");
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
