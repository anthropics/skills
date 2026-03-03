"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.isGMT = exports.dnsLookup = void 0;
const dns_1 = require("dns");
function dnsLookup(host, opts) {
    return new Promise((resolve, reject) => {
        (0, dns_1.lookup)(host, opts, (err, res) => {
            if (err) {
                reject(err);
            }
            else {
                resolve(res);
            }
        });
    });
}
exports.dnsLookup = dnsLookup;
function isGMT(v) {
    return v === 'GMT';
}
exports.isGMT = isGMT;
//# sourceMappingURL=util.js.map