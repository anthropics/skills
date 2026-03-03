"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
exports.sandbox = exports.createPacResolver = void 0;
const degenerator_1 = require("degenerator");
/**
 * Built-in PAC functions.
 */
const dateRange_1 = __importDefault(require("./dateRange"));
const dnsDomainIs_1 = __importDefault(require("./dnsDomainIs"));
const dnsDomainLevels_1 = __importDefault(require("./dnsDomainLevels"));
const dnsResolve_1 = __importDefault(require("./dnsResolve"));
const isInNet_1 = __importDefault(require("./isInNet"));
const isPlainHostName_1 = __importDefault(require("./isPlainHostName"));
const isResolvable_1 = __importDefault(require("./isResolvable"));
const localHostOrDomainIs_1 = __importDefault(require("./localHostOrDomainIs"));
const myIpAddress_1 = __importDefault(require("./myIpAddress"));
const shExpMatch_1 = __importDefault(require("./shExpMatch"));
const timeRange_1 = __importDefault(require("./timeRange"));
const weekdayRange_1 = __importDefault(require("./weekdayRange"));
/**
 * Returns an asynchronous `FindProxyForURL()` function
 * from the given JS string (from a PAC file).
 */
function createPacResolver(qjs, _str, _opts = {}) {
    const str = Buffer.isBuffer(_str) ? _str.toString('utf8') : _str;
    // The sandbox to use for the `vm` context.
    const context = {
        ...exports.sandbox,
        ..._opts.sandbox,
    };
    // Construct the array of async function names to add `await` calls to.
    const names = Object.keys(context).filter((k) => isAsyncFunction(context[k]));
    const opts = {
        filename: 'proxy.pac',
        names,
        ..._opts,
        sandbox: context,
    };
    // Compile the JS `FindProxyForURL()` function into an async function.
    const resolver = (0, degenerator_1.compile)(qjs, str, 'FindProxyForURL', opts);
    function FindProxyForURL(url, _host) {
        const urlObj = typeof url === 'string' ? new URL(url) : url;
        const host = _host || urlObj.hostname;
        if (!host) {
            throw new TypeError('Could not determine `host`');
        }
        return resolver(urlObj.href, host);
    }
    Object.defineProperty(FindProxyForURL, 'toString', {
        value: () => resolver.toString(),
        enumerable: false,
    });
    return FindProxyForURL;
}
exports.createPacResolver = createPacResolver;
exports.sandbox = Object.freeze({
    alert: (message = '') => console.log('%s', message),
    dateRange: dateRange_1.default,
    dnsDomainIs: dnsDomainIs_1.default,
    dnsDomainLevels: dnsDomainLevels_1.default,
    dnsResolve: dnsResolve_1.default,
    isInNet: isInNet_1.default,
    isPlainHostName: isPlainHostName_1.default,
    isResolvable: isResolvable_1.default,
    localHostOrDomainIs: localHostOrDomainIs_1.default,
    myIpAddress: myIpAddress_1.default,
    shExpMatch: shExpMatch_1.default,
    timeRange: timeRange_1.default,
    weekdayRange: weekdayRange_1.default,
});
// eslint-disable-next-line @typescript-eslint/no-explicit-any
function isAsyncFunction(v) {
    if (typeof v !== 'function')
        return false;
    // Native `AsyncFunction`
    if (v.constructor.name === 'AsyncFunction')
        return true;
    // TypeScript compiled
    if (String(v).indexOf('__awaiter(') !== -1)
        return true;
    // Legacy behavior - set `async` property on the function
    return Boolean(v.async);
}
//# sourceMappingURL=index.js.map