"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
/**
 * Returns the number (integer) of DNS domain levels (number of dots) in the
 * hostname.
 *
 * Examples:
 *
 * ``` js
 * dnsDomainLevels("www")
 *   // returns 0.
 * dnsDomainLevels("www.netscape.com")
 *   // returns 2.
 * ```
 *
 * @param {String} host is the hostname from the URL.
 * @return {Number} number of domain levels
 */
function dnsDomainLevels(host) {
    const match = String(host).match(/\./g);
    let levels = 0;
    if (match) {
        levels = match.length;
    }
    return levels;
}
exports.default = dnsDomainLevels;
//# sourceMappingURL=dnsDomainLevels.js.map