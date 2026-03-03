"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
const util_1 = require("./util");
/**
 * Resolves the given DNS hostname into an IP address, and returns it in the dot
 * separated format as a string.
 *
 * Example:
 *
 * ``` js
 * dnsResolve("home.netscape.com")
 *   // returns the string "198.95.249.79".
 * ```
 *
 * @param {String} host hostname to resolve
 * @return {String} resolved IP address
 */
async function dnsResolve(host) {
    const family = 4;
    try {
        const r = await (0, util_1.dnsLookup)(host, { family });
        if (typeof r === 'string') {
            return r;
        }
    }
    catch (err) {
        // @ignore
    }
    return null;
}
exports.default = dnsResolve;
//# sourceMappingURL=dnsResolve.js.map