"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.CdpHTTPResponse = void 0;
const HTTPResponse_js_1 = require("../api/HTTPResponse.js");
const Errors_js_1 = require("../common/Errors.js");
const SecurityDetails_js_1 = require("../common/SecurityDetails.js");
const Deferred_js_1 = require("../util/Deferred.js");
const encoding_js_1 = require("../util/encoding.js");
/**
 * @internal
 */
class CdpHTTPResponse extends HTTPResponse_js_1.HTTPResponse {
    #request;
    #contentPromise = null;
    #bodyLoadedDeferred = Deferred_js_1.Deferred.create();
    #remoteAddress;
    #status;
    #statusText;
    #fromDiskCache;
    #fromServiceWorker;
    #headers = {};
    #securityDetails;
    #timing;
    constructor(request, responsePayload, extraInfo) {
        super();
        this.#request = request;
        this.#remoteAddress = {
            ip: responsePayload.remoteIPAddress,
            port: responsePayload.remotePort,
        };
        this.#statusText =
            this.#parseStatusTextFromExtraInfo(extraInfo) ||
                responsePayload.statusText;
        this.#fromDiskCache = !!responsePayload.fromDiskCache;
        this.#fromServiceWorker = !!responsePayload.fromServiceWorker;
        this.#status = extraInfo ? extraInfo.statusCode : responsePayload.status;
        const headers = extraInfo ? extraInfo.headers : responsePayload.headers;
        for (const [key, value] of Object.entries(headers)) {
            this.#headers[key.toLowerCase()] = value;
        }
        this.#securityDetails = responsePayload.securityDetails
            ? new SecurityDetails_js_1.SecurityDetails(responsePayload.securityDetails)
            : null;
        this.#timing = responsePayload.timing || null;
    }
    #parseStatusTextFromExtraInfo(extraInfo) {
        if (!extraInfo || !extraInfo.headersText) {
            return;
        }
        const firstLine = extraInfo.headersText.split('\r', 1)[0];
        if (!firstLine || firstLine.length > 1_000) {
            return;
        }
        const match = firstLine.match(/[^ ]* [^ ]* (.*)/);
        if (!match) {
            return;
        }
        const statusText = match[1];
        if (!statusText) {
            return;
        }
        return statusText;
    }
    _resolveBody(err) {
        if (err) {
            return this.#bodyLoadedDeferred.reject(err);
        }
        return this.#bodyLoadedDeferred.resolve();
    }
    remoteAddress() {
        return this.#remoteAddress;
    }
    url() {
        return this.#request.url();
    }
    status() {
        return this.#status;
    }
    statusText() {
        return this.#statusText;
    }
    headers() {
        return this.#headers;
    }
    securityDetails() {
        return this.#securityDetails;
    }
    timing() {
        return this.#timing;
    }
    content() {
        if (!this.#contentPromise) {
            this.#contentPromise = this.#bodyLoadedDeferred
                .valueOrThrow()
                .then(async () => {
                try {
                    // Use CDPSession from corresponding request to retrieve body, as it's client
                    // might have been updated (e.g. for an adopted OOPIF).
                    const response = await this.#request.client.send('Network.getResponseBody', {
                        requestId: this.#request.id,
                    });
                    return (0, encoding_js_1.stringToTypedArray)(response.body, response.base64Encoded);
                }
                catch (error) {
                    if (error instanceof Errors_js_1.ProtocolError &&
                        error.originalMessage ===
                            'No resource with given identifier found') {
                        throw new Errors_js_1.ProtocolError('Could not load response body for this request. This might happen if the request is a preflight request.');
                    }
                    throw error;
                }
            });
        }
        return this.#contentPromise;
    }
    request() {
        return this.#request;
    }
    fromCache() {
        return this.#fromDiskCache || this.#request._fromMemoryCache;
    }
    fromServiceWorker() {
        return this.#fromServiceWorker;
    }
    frame() {
        return this.#request.frame();
    }
}
exports.CdpHTTPResponse = CdpHTTPResponse;
//# sourceMappingURL=HTTPResponse.js.map