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
exports.PacProxyAgent = void 0;
const net = __importStar(require("net"));
const tls = __importStar(require("tls"));
const crypto = __importStar(require("crypto"));
const events_1 = require("events");
const debug_1 = __importDefault(require("debug"));
const url_1 = require("url");
const agent_base_1 = require("agent-base");
const get_uri_1 = require("get-uri");
const pac_resolver_1 = require("pac-resolver");
const quickjs_emscripten_1 = require("@tootallnate/quickjs-emscripten");
const debug = (0, debug_1.default)('pac-proxy-agent');
const setServernameFromNonIpHost = (options) => {
    if (options.servername === undefined &&
        options.host &&
        !net.isIP(options.host)) {
        return {
            ...options,
            servername: options.host,
        };
    }
    return options;
};
/**
 * The `PacProxyAgent` class.
 *
 * A few different "protocol" modes are supported (supported protocols are
 * backed by the `get-uri` module):
 *
 *   - "pac+data", "data" - refers to an embedded "data:" URI
 *   - "pac+file", "file" - refers to a local file
 *   - "pac+ftp", "ftp" - refers to a file located on an FTP server
 *   - "pac+http", "http" - refers to an HTTP endpoint
 *   - "pac+https", "https" - refers to an HTTPS endpoint
 */
class PacProxyAgent extends agent_base_1.Agent {
    constructor(uri, opts) {
        super(opts);
        this.clearResolverPromise = () => {
            this.resolverPromise = undefined;
        };
        // Strip the "pac+" prefix
        const uriStr = typeof uri === 'string' ? uri : uri.href;
        this.uri = new url_1.URL(uriStr.replace(/^pac\+/i, ''));
        debug('Creating PacProxyAgent with URI %o', this.uri.href);
        // @ts-expect-error Not sure why TS is complaining here…
        this.opts = { ...opts };
        this.cache = undefined;
        this.resolver = undefined;
        this.resolverHash = '';
        this.resolverPromise = undefined;
        // For `PacResolver`
        if (!this.opts.filename) {
            this.opts.filename = this.uri.href;
        }
    }
    /**
     * Loads the PAC proxy file from the source if necessary, and returns
     * a generated `FindProxyForURL()` resolver function to use.
     */
    getResolver() {
        if (!this.resolverPromise) {
            this.resolverPromise = this.loadResolver();
            this.resolverPromise.then(this.clearResolverPromise, this.clearResolverPromise);
        }
        return this.resolverPromise;
    }
    async loadResolver() {
        try {
            // (Re)load the contents of the PAC file URI
            const [qjs, code] = await Promise.all([
                (0, quickjs_emscripten_1.getQuickJS)(),
                this.loadPacFile(),
            ]);
            // Create a sha1 hash of the JS code
            const hash = crypto.createHash('sha1').update(code).digest('hex');
            if (this.resolver && this.resolverHash === hash) {
                debug('Same sha1 hash for code - contents have not changed, reusing previous proxy resolver');
                return this.resolver;
            }
            // Cache the resolver
            debug('Creating new proxy resolver instance');
            this.resolver = (0, pac_resolver_1.createPacResolver)(qjs, code, this.opts);
            // Store that sha1 hash for future comparison purposes
            this.resolverHash = hash;
            return this.resolver;
        }
        catch (err) {
            if (this.resolver &&
                err.code === 'ENOTMODIFIED') {
                debug('Got ENOTMODIFIED response, reusing previous proxy resolver');
                return this.resolver;
            }
            throw err;
        }
    }
    /**
     * Loads the contents of the PAC proxy file.
     *
     * @api private
     */
    async loadPacFile() {
        debug('Loading PAC file: %o', this.uri);
        const rs = await (0, get_uri_1.getUri)(this.uri, { ...this.opts, cache: this.cache });
        debug('Got `Readable` instance for URI');
        this.cache = rs;
        const buf = await (0, agent_base_1.toBuffer)(rs);
        debug('Read %o byte PAC file from URI', buf.length);
        return buf.toString('utf8');
    }
    /**
     * Called when the node-core HTTP client library is creating a new HTTP request.
     */
    async connect(req, opts) {
        const { secureEndpoint } = opts;
        const isWebSocket = req.getHeader('upgrade') === 'websocket';
        // First, get a generated `FindProxyForURL()` function,
        // either cached or retrieved from the source
        const resolver = await this.getResolver();
        // Calculate the `url` parameter
        const protocol = secureEndpoint ? 'https:' : 'http:';
        const host = opts.host && net.isIPv6(opts.host) ? `[${opts.host}]` : opts.host;
        const defaultPort = secureEndpoint ? 443 : 80;
        const url = Object.assign(new url_1.URL(req.path, `${protocol}//${host}`), defaultPort ? undefined : { port: opts.port });
        debug('url: %s', url);
        let result = await resolver(url);
        // Default to "DIRECT" if a falsey value was returned (or nothing)
        if (!result) {
            result = 'DIRECT';
        }
        const proxies = String(result)
            .trim()
            .split(/\s*;\s*/g)
            .filter(Boolean);
        if (this.opts.fallbackToDirect && !proxies.includes('DIRECT')) {
            proxies.push('DIRECT');
        }
        for (const proxy of proxies) {
            let agent = null;
            let socket = null;
            const [type, target] = proxy.split(/\s+/);
            debug('Attempting to use proxy: %o', proxy);
            if (type === 'DIRECT') {
                // Direct connection to the destination endpoint
                if (secureEndpoint) {
                    socket = tls.connect(setServernameFromNonIpHost(opts));
                }
                else {
                    socket = net.connect(opts);
                }
            }
            else if (type === 'SOCKS' || type === 'SOCKS5') {
                // Use a SOCKSv5h proxy
                const { SocksProxyAgent } = await Promise.resolve().then(() => __importStar(require('socks-proxy-agent')));
                agent = new SocksProxyAgent(`socks://${target}`, this.opts);
            }
            else if (type === 'SOCKS4') {
                // Use a SOCKSv4a proxy
                const { SocksProxyAgent } = await Promise.resolve().then(() => __importStar(require('socks-proxy-agent')));
                agent = new SocksProxyAgent(`socks4a://${target}`, this.opts);
            }
            else if (type === 'PROXY' ||
                type === 'HTTP' ||
                type === 'HTTPS') {
                // Use an HTTP or HTTPS proxy
                // http://dev.chromium.org/developers/design-documents/secure-web-proxy
                const proxyURL = `${type === 'HTTPS' ? 'https' : 'http'}://${target}`;
                if (secureEndpoint || isWebSocket) {
                    const { HttpsProxyAgent } = await Promise.resolve().then(() => __importStar(require('https-proxy-agent')));
                    agent = new HttpsProxyAgent(proxyURL, this.opts);
                }
                else {
                    const { HttpProxyAgent } = await Promise.resolve().then(() => __importStar(require('http-proxy-agent')));
                    agent = new HttpProxyAgent(proxyURL, this.opts);
                }
            }
            try {
                if (socket) {
                    // "DIRECT" connection, wait for connection confirmation
                    await (0, events_1.once)(socket, 'connect');
                    req.emit('proxy', { proxy, socket });
                    return socket;
                }
                if (agent) {
                    const s = await agent.connect(req, opts);
                    if (!(s instanceof net.Socket)) {
                        throw new Error('Expected a `net.Socket` to be returned from agent');
                    }
                    req.emit('proxy', { proxy, socket: s });
                    return s;
                }
                throw new Error(`Could not determine proxy type for: ${proxy}`);
            }
            catch (err) {
                debug('Got error for proxy %o: %o', proxy, err);
                req.emit('proxy', { proxy, error: err });
            }
        }
        throw new Error(`Failed to establish a socket connection to proxies: ${JSON.stringify(proxies)}`);
    }
}
PacProxyAgent.protocols = [
    'pac+data',
    'pac+file',
    'pac+ftp',
    'pac+http',
    'pac+https',
];
exports.PacProxyAgent = PacProxyAgent;
//# sourceMappingURL=index.js.map