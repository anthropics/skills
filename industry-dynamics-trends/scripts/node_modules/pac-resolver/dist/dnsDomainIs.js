"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
/**
 * Returns true iff the domain of hostname matches.
 *
 * Examples:
 *
 * ``` js
 * dnsDomainIs("www.netscape.com", ".netscape.com")
 *   // is true.
 *
 * dnsDomainIs("www", ".netscape.com")
 *   // is false.
 *
 * dnsDomainIs("www.mcom.com", ".netscape.com")
 *   // is false.
 * ```
 *
 *
 * @param {String} host is the hostname from the URL.
 * @param {String} domain is the domain name to test the hostname against.
 * @return {Boolean} true iff the domain of the hostname matches.
 */
function dnsDomainIs(host, domain) {
    host = String(host);
    domain = String(domain);
    return host.substr(domain.length * -1) === domain;
}
exports.default = dnsDomainIs;
//# sourceMappingURL=dnsDomainIs.js.map