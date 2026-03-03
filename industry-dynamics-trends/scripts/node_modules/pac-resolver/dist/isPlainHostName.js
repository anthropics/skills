"use strict";
/**
 * True iff there is no domain name in the hostname (no dots).
 *
 * Examples:
 *
 * ``` js
 * isPlainHostName("www")
 *   // is true.
 *
 * isPlainHostName("www.netscape.com")
 *   // is false.
 * ```
 *
 * @param {String} host The hostname from the URL (excluding port number).
 * @return {Boolean}
 */
Object.defineProperty(exports, "__esModule", { value: true });
function isPlainHostName(host) {
    return !/\./.test(host);
}
exports.default = isPlainHostName;
//# sourceMappingURL=isPlainHostName.js.map