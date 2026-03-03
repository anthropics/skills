"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
exports.getUri = exports.isValidProtocol = exports.protocols = void 0;
const debug_1 = __importDefault(require("debug"));
// Built-in protocols
const data_1 = require("./data");
const file_1 = require("./file");
const ftp_1 = require("./ftp");
const http_1 = require("./http");
const https_1 = require("./https");
const debug = (0, debug_1.default)('get-uri');
exports.protocols = {
    data: data_1.data,
    file: file_1.file,
    ftp: ftp_1.ftp,
    http: http_1.http,
    https: https_1.https,
};
const VALID_PROTOCOLS = new Set(Object.keys(exports.protocols));
function isValidProtocol(p) {
    return VALID_PROTOCOLS.has(p);
}
exports.isValidProtocol = isValidProtocol;
/**
 * Async function that returns a `stream.Readable` instance that will output
 * the contents of the given URI.
 *
 * For caching purposes, you can pass in a `stream` instance from a previous
 * `getUri()` call as a `cache: stream` option, and if the destination has
 * not changed since the last time the endpoint was retrieved then the callback
 * will be invoked with an Error object with `code` set to "ENOTMODIFIED" and
 * `null` for the "stream" instance argument. In this case, you can skip
 * retrieving the file again and continue to use the previous payload.
 *
 * @param {String} uri URI to retrieve
 * @param {Object} opts optional "options" object
 * @api public
 */
async function getUri(uri, opts) {
    debug('getUri(%o)', uri);
    if (!uri) {
        throw new TypeError('Must pass in a URI to "getUri()"');
    }
    const url = typeof uri === 'string' ? new URL(uri) : uri;
    // Strip trailing `:`
    const protocol = url.protocol.replace(/:$/, '');
    if (!isValidProtocol(protocol)) {
        throw new TypeError(`Unsupported protocol "${protocol}" specified in URI: "${uri}"`);
    }
    const getter = exports.protocols[protocol];
    return getter(url, opts);
}
exports.getUri = getUri;
//# sourceMappingURL=index.js.map