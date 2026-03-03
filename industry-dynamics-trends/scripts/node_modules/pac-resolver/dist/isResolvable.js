"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
const util_1 = require("./util");
/**
 * Tries to resolve the hostname. Returns true if succeeds.
 *
 * @param {String} host is the hostname from the URL.
 * @return {Boolean}
 */
async function isResolvable(host) {
    const family = 4;
    try {
        if (await (0, util_1.dnsLookup)(host, { family })) {
            return true;
        }
    }
    catch (err) {
        // ignore
    }
    return false;
}
exports.default = isResolvable;
//# sourceMappingURL=isResolvable.js.map