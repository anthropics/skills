"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
exports.file = void 0;
const debug_1 = __importDefault(require("debug"));
const fs_1 = require("fs");
const notfound_1 = __importDefault(require("./notfound"));
const notmodified_1 = __importDefault(require("./notmodified"));
const url_1 = require("url");
const debug = (0, debug_1.default)('get-uri:file');
/**
 * Returns a `fs.ReadStream` instance from a "file:" URI.
 */
const file = async ({ href: uri }, opts = {}) => {
    const { cache, flags = 'r', mode = 438, // =0666
     } = opts;
    try {
        // Convert URI → Path
        const filepath = (0, url_1.fileURLToPath)(uri);
        debug('Normalized pathname: %o', filepath);
        // `open()` first to get a file descriptor and ensure that the file
        // exists.
        const fdHandle = await fs_1.promises.open(filepath, flags, mode);
        // extract the numeric file descriptor
        const fd = fdHandle.fd;
        // store the stat object for the cache.
        const stat = await fdHandle.stat();
        // if a `cache` was provided, check if the file has not been modified
        if (cache && cache.stat && stat && isNotModified(cache.stat, stat)) {
            await fdHandle.close();
            throw new notmodified_1.default();
        }
        // `fs.ReadStream` takes care of calling `fs.close()` on the
        // fd after it's done reading
        const rs = (0, fs_1.createReadStream)(filepath, {
            autoClose: true,
            ...opts,
            fd,
        });
        rs.stat = stat;
        return rs;
    }
    catch (err) {
        if (err.code === 'ENOENT') {
            throw new notfound_1.default();
        }
        throw err;
    }
};
exports.file = file;
// returns `true` if the `mtime` of the 2 stat objects are equal
function isNotModified(prev, curr) {
    return +prev.mtime === +curr.mtime;
}
//# sourceMappingURL=file.js.map