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
export default function dnsDomainIs(host: string, domain: string): boolean;
//# sourceMappingURL=dnsDomainIs.d.ts.map