"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.describeTLS = describeTLS;
exports.describeAddress = describeAddress;
exports.upgradeSocket = upgradeSocket;
exports.ipIsPrivateV4Address = ipIsPrivateV4Address;
const tls_1 = require("tls");
/**
 * Returns a string describing the encryption on a given socket instance.
 */
function describeTLS(socket) {
    if (socket instanceof tls_1.TLSSocket) {
        const protocol = socket.getProtocol();
        return protocol ? protocol : "Server socket or disconnected client socket";
    }
    return "No encryption";
}
/**
 * Returns a string describing the remote address of a socket.
 */
function describeAddress(socket) {
    if (socket.remoteFamily === "IPv6") {
        return `[${socket.remoteAddress}]:${socket.remotePort}`;
    }
    return `${socket.remoteAddress}:${socket.remotePort}`;
}
/**
 * Upgrade a socket connection with TLS.
 */
function upgradeSocket(socket, options) {
    return new Promise((resolve, reject) => {
        const tlsOptions = Object.assign({}, options, {
            socket
        });
        const tlsSocket = (0, tls_1.connect)(tlsOptions, () => {
            const expectCertificate = tlsOptions.rejectUnauthorized !== false;
            if (expectCertificate && !tlsSocket.authorized) {
                reject(tlsSocket.authorizationError);
            }
            else {
                // Remove error listener added below.
                tlsSocket.removeAllListeners("error");
                resolve(tlsSocket);
            }
        }).once("error", error => {
            reject(error);
        });
    });
}
/**
 * Returns true if an IP is a private address according to https://tools.ietf.org/html/rfc1918#section-3.
 * This will handle IPv4-mapped IPv6 addresses correctly but return false for all other IPv6 addresses.
 *
 * @param ip  The IP as a string, e.g. "192.168.0.1"
 */
function ipIsPrivateV4Address(ip = "") {
    // Handle IPv4-mapped IPv6 addresses like ::ffff:192.168.0.1
    if (ip.startsWith("::ffff:")) {
        ip = ip.substr(7); // Strip ::ffff: prefix
    }
    const octets = ip.split(".").map(o => parseInt(o, 10));
    return octets[0] === 10 // 10.0.0.0 - 10.255.255.255
        || (octets[0] === 172 && octets[1] >= 16 && octets[1] <= 31) // 172.16.0.0 - 172.31.255.255
        || (octets[0] === 192 && octets[1] === 168) // 192.168.0.0 - 192.168.255.255
        || ip === "127.0.0.1";
}
