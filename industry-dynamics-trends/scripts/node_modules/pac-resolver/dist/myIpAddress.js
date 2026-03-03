"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
const ip_1 = require("./ip");
const net_1 = __importDefault(require("net"));
/**
 * Returns the IP address of the host that the Navigator is running on, as
 * a string in the dot-separated integer format.
 *
 * Example:
 *
 * ``` js
 * myIpAddress()
 *   // would return the string "198.95.249.79" if you were running the
 *   // Navigator on that host.
 * ```
 *
 * @return {String} external IP address
 */
async function myIpAddress() {
    return new Promise((resolve, reject) => {
        // 8.8.8.8:53 is "Google Public DNS":
        // https://developers.google.com/speed/public-dns/
        const socket = net_1.default.connect({ host: '8.8.8.8', port: 53 });
        const onError = () => {
            // if we fail to access Google DNS (as in firewall blocks access),
            // fallback to querying IP locally
            resolve(ip_1.ip.address());
        };
        socket.once('error', onError);
        socket.once('connect', () => {
            socket.removeListener('error', onError);
            const addr = socket.address();
            socket.destroy();
            if (typeof addr === 'string') {
                resolve(addr);
            }
            else if (addr.address) {
                resolve(addr.address);
            }
            else {
                reject(new Error('Expected a `string`'));
            }
        });
    });
}
exports.default = myIpAddress;
//# sourceMappingURL=myIpAddress.js.map