"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
exports.data = void 0;
const debug_1 = __importDefault(require("debug"));
const stream_1 = require("stream");
const crypto_1 = require("crypto");
const data_uri_to_buffer_1 = require("data-uri-to-buffer");
const notmodified_1 = __importDefault(require("./notmodified"));
const debug = (0, debug_1.default)('get-uri:data');
class DataReadable extends stream_1.Readable {
    constructor(hash, buf) {
        super();
        this.push(buf);
        this.push(null);
        this.hash = hash;
    }
}
/**
 * Returns a Readable stream from a "data:" URI.
 */
const data = async ({ href: uri }, { cache } = {}) => {
    // need to create a SHA1 hash of the URI string, for cacheability checks
    // in future `getUri()` calls with the same data URI passed in.
    const shasum = (0, crypto_1.createHash)('sha1');
    shasum.update(uri);
    const hash = shasum.digest('hex');
    debug('generated SHA1 hash for "data:" URI: %o', hash);
    // check if the cache is the same "data:" URI that was previously passed in.
    if (cache?.hash === hash) {
        debug('got matching cache SHA1 hash: %o', hash);
        throw new notmodified_1.default();
    }
    else {
        debug('creating Readable stream from "data:" URI buffer');
        const { buffer } = (0, data_uri_to_buffer_1.dataUriToBuffer)(uri);
        return new DataReadable(hash, Buffer.from(buffer));
    }
};
exports.data = data;
//# sourceMappingURL=data.js.map