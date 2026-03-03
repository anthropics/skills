"use strict";
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __setModuleDefault = (this && this.__setModuleDefault) || (Object.create ? (function(o, v) {
    Object.defineProperty(o, "default", { enumerable: true, value: v });
}) : function(o, v) {
    o["default"] = v;
});
var __importStar = (this && this.__importStar) || function (mod) {
    if (mod && mod.__esModule) return mod;
    var result = {};
    if (mod != null) for (var k in mod) if (k !== "default" && Object.prototype.hasOwnProperty.call(mod, k)) __createBinding(result, mod, k);
    __setModuleDefault(result, mod);
    return result;
};
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
exports.ProxyAgent = exports.proxies = void 0;
const http = __importStar(require("http"));
const https = __importStar(require("https"));
const url_1 = require("url");
const lru_cache_1 = __importDefault(require("lru-cache"));
const agent_base_1 = require("agent-base");
const debug_1 = __importDefault(require("debug"));
const proxy_from_env_1 = require("proxy-from-env");
const debug = (0, debug_1.default)('proxy-agent');
/**
 * Shorthands for built-in supported types.
 * Lazily loaded since some of these imports can be quite expensive
 * (in particular, pac-proxy-agent).
 */
const wellKnownAgents = {
    http: async () => (await Promise.resolve().then(() => __importStar(require('http-proxy-agent')))).HttpProxyAgent,
    https: async () => (await Promise.resolve().then(() => __importStar(require('https-proxy-agent')))).HttpsProxyAgent,
    socks: async () => (await Promise.resolve().then(() => __importStar(require('socks-proxy-agent')))).SocksProxyAgent,
    pac: async () => (await Promise.resolve().then(() => __importStar(require('pac-proxy-agent')))).PacProxyAgent,
};
/**
 * Supported proxy types.
 */
exports.proxies = {
    http: [wellKnownAgents.http, wellKnownAgents.https],
    https: [wellKnownAgents.http, wellKnownAgents.https],
    socks: [wellKnownAgents.socks, wellKnownAgents.socks],
    socks4: [wellKnownAgents.socks, wellKnownAgents.socks],
    socks4a: [wellKnownAgents.socks, wellKnownAgents.socks],
    socks5: [wellKnownAgents.socks, wellKnownAgents.socks],
    socks5h: [wellKnownAgents.socks, wellKnownAgents.socks],
    'pac+data': [wellKnownAgents.pac, wellKnownAgents.pac],
    'pac+file': [wellKnownAgents.pac, wellKnownAgents.pac],
    'pac+ftp': [wellKnownAgents.pac, wellKnownAgents.pac],
    'pac+http': [wellKnownAgents.pac, wellKnownAgents.pac],
    'pac+https': [wellKnownAgents.pac, wellKnownAgents.pac],
};
function isValidProtocol(v) {
    return Object.keys(exports.proxies).includes(v);
}
/**
 * Uses the appropriate `Agent` subclass based off of the "proxy"
 * environment variables that are currently set.
 *
 * An LRU cache is used, to prevent unnecessary creation of proxy
 * `http.Agent` instances.
 */
class ProxyAgent extends agent_base_1.Agent {
    constructor(opts) {
        super(opts);
        /**
         * Cache for `Agent` instances.
         */
        this.cache = new lru_cache_1.default({
            max: 20,
            dispose: (agent) => agent.destroy(),
        });
        debug('Creating new ProxyAgent instance: %o', opts);
        this.connectOpts = opts;
        this.httpAgent = opts?.httpAgent || new http.Agent(opts);
        this.httpsAgent =
            opts?.httpsAgent || new https.Agent(opts);
        this.getProxyForUrl = opts?.getProxyForUrl || proxy_from_env_1.getProxyForUrl;
    }
    async connect(req, opts) {
        const { secureEndpoint } = opts;
        const isWebSocket = req.getHeader('upgrade') === 'websocket';
        const protocol = secureEndpoint
            ? isWebSocket
                ? 'wss:'
                : 'https:'
            : isWebSocket
                ? 'ws:'
                : 'http:';
        const host = req.getHeader('host');
        const url = new url_1.URL(req.path, `${protocol}//${host}`).href;
        const proxy = await this.getProxyForUrl(url, req);
        if (!proxy) {
            debug('Proxy not enabled for URL: %o', url);
            return secureEndpoint ? this.httpsAgent : this.httpAgent;
        }
        debug('Request URL: %o', url);
        debug('Proxy URL: %o', proxy);
        // attempt to get a cached `http.Agent` instance first
        const cacheKey = `${protocol}+${proxy}`;
        let agent = this.cache.get(cacheKey);
        if (!agent) {
            const proxyUrl = new url_1.URL(proxy);
            const proxyProto = proxyUrl.protocol.replace(':', '');
            if (!isValidProtocol(proxyProto)) {
                throw new Error(`Unsupported protocol for proxy URL: ${proxy}`);
            }
            const ctor = await exports.proxies[proxyProto][secureEndpoint || isWebSocket ? 1 : 0]();
            agent = new ctor(proxy, this.connectOpts);
            this.cache.set(cacheKey, agent);
        }
        else {
            debug('Cache hit for proxy URL: %o', proxy);
        }
        return agent;
    }
    destroy() {
        for (const agent of this.cache.values()) {
            agent.destroy();
        }
        super.destroy();
    }
}
exports.ProxyAgent = ProxyAgent;
//# sourceMappingURL=index.js.map