"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
exports.ip = void 0;
const os_1 = __importDefault(require("os"));
exports.ip = {
    address() {
        const interfaces = os_1.default.networkInterfaces();
        // Default to `ipv4`
        const family = normalizeFamily();
        const all = Object.values(interfaces).map((addrs = []) => {
            const addresses = addrs.filter((details) => {
                const detailsFamily = normalizeFamily(details.family);
                if (detailsFamily !== family || exports.ip.isLoopback(details.address)) {
                    return false;
                }
                return true;
            });
            return addresses.length ? addresses[0].address : undefined;
        }).filter(Boolean);
        return !all.length ? exports.ip.loopback(family) : all[0];
    },
    isLoopback(addr) {
        return /^(::f{4}:)?127\.([0-9]{1,3})\.([0-9]{1,3})\.([0-9]{1,3})/
            .test(addr)
            || /^fe80::1$/.test(addr)
            || /^::1$/.test(addr)
            || /^::$/.test(addr);
    },
    loopback(family) {
        // Default to `ipv4`
        family = normalizeFamily(family);
        if (family !== 'ipv4' && family !== 'ipv6') {
            throw new Error('family must be ipv4 or ipv6');
        }
        return family === 'ipv4' ? '127.0.0.1' : 'fe80::1';
    }
};
function normalizeFamily(family) {
    if (family === 4) {
        return 'ipv4';
    }
    if (family === 6) {
        return 'ipv6';
    }
    return family ? family.toLowerCase() : 'ipv4';
}
//# sourceMappingURL=ip.js.map