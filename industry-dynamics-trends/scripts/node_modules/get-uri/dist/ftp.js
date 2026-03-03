"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
exports.ftp = void 0;
const basic_ftp_1 = require("basic-ftp");
const stream_1 = require("stream");
const path_1 = require("path");
const debug_1 = __importDefault(require("debug"));
const notfound_1 = __importDefault(require("./notfound"));
const notmodified_1 = __importDefault(require("./notmodified"));
const debug = (0, debug_1.default)('get-uri:ftp');
/**
 * Returns a Readable stream from an "ftp:" URI.
 */
const ftp = async (url, opts = {}) => {
    const { cache } = opts;
    const filepath = decodeURIComponent(url.pathname);
    let lastModified;
    if (!filepath) {
        throw new TypeError('No "pathname"!');
    }
    const client = new basic_ftp_1.Client();
    try {
        const host = url.hostname || url.host || 'localhost';
        const port = parseInt(url.port || '0', 10) || 21;
        const user = url.username
            ? decodeURIComponent(url.username)
            : undefined;
        const password = url.password
            ? decodeURIComponent(url.password)
            : undefined;
        await client.access({
            host,
            port,
            user,
            password,
            ...opts,
        });
        // first we have to figure out the Last Modified date.
        // try the MDTM command first, which is an optional extension command.
        try {
            lastModified = await client.lastMod(filepath);
        }
        catch (err) {
            // handle the "file not found" error code
            if (err.code === 550) {
                throw new notfound_1.default();
            }
        }
        if (!lastModified) {
            // Try to get the last modified date via the LIST command (uses
            // more bandwidth, but is more compatible with older FTP servers
            const list = await client.list((0, path_1.dirname)(filepath));
            // attempt to find the "entry" with a matching "name"
            const name = (0, path_1.basename)(filepath);
            const entry = list.find((e) => e.name === name);
            if (entry) {
                lastModified = entry.modifiedAt;
            }
        }
        if (lastModified) {
            if (isNotModified()) {
                throw new notmodified_1.default();
            }
        }
        else {
            throw new notfound_1.default();
        }
        const stream = new stream_1.PassThrough();
        const rs = stream;
        client.downloadTo(stream, filepath).then((result) => {
            debug(result.message);
            client.close();
        });
        rs.lastModified = lastModified;
        return rs;
    }
    catch (err) {
        client.close();
        throw err;
    }
    // called when `lastModified` is set, and a "cache" stream was provided
    function isNotModified() {
        if (cache?.lastModified && lastModified) {
            return +cache.lastModified === +lastModified;
        }
        return false;
    }
};
exports.ftp = ftp;
//# sourceMappingURL=ftp.js.map