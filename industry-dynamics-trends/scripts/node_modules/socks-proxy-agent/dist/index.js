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
exports.SocksProxyAgent = void 0;
const socks_1 = require("socks");
const agent_base_1 = require("agent-base");
const debug_1 = __importDefault(require("debug"));
const dns = __importStar(require("dns"));
const net = __importStar(require("net"));
const tls = __importStar(require("tls"));
const url_1 = require("url");
const debug = (0, debug_1.default)('socks-proxy-agent');
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
function parseSocksURL(url) {
    let lookup = false;
    let type = 5;
    const host = url.hostname;
    // From RFC 1928, Section 3: https://tools.ietf.org/html/rfc1928#section-3
    // "The SOCKS service is conventionally located on TCP port 1080"
    const port = parseInt(url.port, 10) || 1080;
    // figure out if we want socks v4 or v5, based on the "protocol" used.
    // Defaults to 5.
    switch (url.protocol.replace(':', '')) {
        case 'socks4':
            lookup = true;
            type = 4;
            break;
        // pass through
        case 'socks4a':
            type = 4;
            break;
        case 'socks5':
            lookup = true;
            type = 5;
            break;
        // pass through
        case 'socks': // no version specified, default to 5h
            type = 5;
            break;
        case 'socks5h':
            type = 5;
            break;
        default:
            throw new TypeError(`A "socks" protocol must be specified! Got: ${String(url.protocol)}`);
    }
    const proxy = {
        host,
        port,
        type,
    };
    if (url.username) {
        Object.defineProperty(proxy, 'userId', {
            value: decodeURIComponent(url.username),
            enumerable: false,
        });
    }
    if (url.password != null) {
        Object.defineProperty(proxy, 'password', {
            value: decodeURIComponent(url.password),
            enumerable: false,
        });
    }
    return { lookup, proxy };
}
class SocksProxyAgent extends agent_base_1.Agent {
    constructor(uri, opts) {
        super(opts);
        const url = typeof uri === 'string' ? new url_1.URL(uri) : uri;
        const { proxy, lookup } = parseSocksURL(url);
        this.shouldLookup = lookup;
        this.proxy = proxy;
        this.timeout = opts?.timeout ?? null;
        this.socketOptions = opts?.socketOptions ?? null;
    }
    /**
     * Initiates a SOCKS connection to the specified SOCKS proxy server,
     * which in turn connects to the specified remote host and port.
     */
    async connect(req, opts) {
        const { shouldLookup, proxy, timeout } = this;
        if (!opts.host) {
            throw new Error('No `host` defined!');
        }
        let { host } = opts;
        const { port, lookup: lookupFn = dns.lookup } = opts;
        if (shouldLookup) {
            // Client-side DNS resolution for "4" and "5" socks proxy versions.
            host = await new Promise((resolve, reject) => {
                // Use the request's custom lookup, if one was configured:
                lookupFn(host, {}, (err, res) => {
                    if (err) {
                        reject(err);
                    }
                    else {
                        resolve(res);
                    }
                });
            });
        }
        const socksOpts = {
            proxy,
            destination: {
                host,
                port: typeof port === 'number' ? port : parseInt(port, 10),
            },
            command: 'connect',
            timeout: timeout ?? undefined,
            // @ts-expect-error the type supplied by socks for socket_options is wider
            // than necessary since socks will always override the host and port
            socket_options: this.socketOptions ?? undefined,
        };
        const cleanup = (tlsSocket) => {
            req.destroy();
            socket.destroy();
            if (tlsSocket)
                tlsSocket.destroy();
        };
        debug('Creating socks proxy connection: %o', socksOpts);
        const { socket } = await socks_1.SocksClient.createConnection(socksOpts);
        debug('Successfully created socks proxy connection');
        if (timeout !== null) {
            socket.setTimeout(timeout);
            socket.on('timeout', () => cleanup());
        }
        if (opts.secureEndpoint) {
            // The proxy is connecting to a TLS server, so upgrade
            // this socket connection to a TLS connection.
            debug('Upgrading socket connection to TLS');
            const tlsSocket = tls.connect({
                ...omit(setServernameFromNonIpHost(opts), 'host', 'path', 'port'),
                socket,
            });
            tlsSocket.once('error', (error) => {
                debug('Socket TLS error', error.message);
                cleanup(tlsSocket);
            });
            return tlsSocket;
        }
        return socket;
    }
}
SocksProxyAgent.protocols = [
    'socks',
    'socks4',
    'socks4a',
    'socks5',
    'socks5h',
];
exports.SocksProxyAgent = SocksProxyAgent;
function omit(obj, ...keys) {
    const ret = {};
    let key;
    for (key in obj) {
        if (!keys.includes(key)) {
            ret[key] = obj[key];
        }
    }
    return ret;
}
//# sourceMappingURL=index.js.map