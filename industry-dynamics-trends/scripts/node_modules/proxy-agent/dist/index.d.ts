/// <reference types="node" />
import * as http from 'http';
import LRUCache from 'lru-cache';
import { Agent, AgentConnectOpts } from 'agent-base';
import type { PacProxyAgent, PacProxyAgentOptions } from 'pac-proxy-agent';
import type { HttpProxyAgent, HttpProxyAgentOptions } from 'http-proxy-agent';
import type { HttpsProxyAgent, HttpsProxyAgentOptions } from 'https-proxy-agent';
import type { SocksProxyAgent, SocksProxyAgentOptions } from 'socks-proxy-agent';
type ValidProtocol = (typeof HttpProxyAgent.protocols)[number] | (typeof HttpsProxyAgent.protocols)[number] | (typeof SocksProxyAgent.protocols)[number] | (typeof PacProxyAgent.protocols)[number];
type AgentConstructor = new (proxy: string, proxyAgentOptions?: ProxyAgentOptions) => Agent;
type GetProxyForUrlCallback = (url: string, req: http.ClientRequest) => string | Promise<string>;
/**
 * Supported proxy types.
 */
export declare const proxies: {
    [P in ValidProtocol]: [
        () => Promise<AgentConstructor>,
        () => Promise<AgentConstructor>
    ];
};
export type ProxyAgentOptions = HttpProxyAgentOptions<''> & HttpsProxyAgentOptions<''> & SocksProxyAgentOptions & PacProxyAgentOptions<''> & {
    /**
     * Default `http.Agent` instance to use when no proxy is
     * configured for a request. Defaults to a new `http.Agent()`
     * instance with the proxy agent options passed in.
     */
    httpAgent?: http.Agent;
    /**
     * Default `http.Agent` instance to use when no proxy is
     * configured for a request. Defaults to a new `https.Agent()`
     * instance with the proxy agent options passed in.
     */
    httpsAgent?: http.Agent;
    /**
     * A callback for dynamic provision of proxy for url.
     * Defaults to standard proxy environment variables,
     * see https://www.npmjs.com/package/proxy-from-env for details
     */
    getProxyForUrl?: GetProxyForUrlCallback;
};
/**
 * Uses the appropriate `Agent` subclass based off of the "proxy"
 * environment variables that are currently set.
 *
 * An LRU cache is used, to prevent unnecessary creation of proxy
 * `http.Agent` instances.
 */
export declare class ProxyAgent extends Agent {
    /**
     * Cache for `Agent` instances.
     */
    cache: LRUCache<string, Agent>;
    connectOpts?: ProxyAgentOptions;
    httpAgent: http.Agent;
    httpsAgent: http.Agent;
    getProxyForUrl: GetProxyForUrlCallback;
    constructor(opts?: ProxyAgentOptions);
    connect(req: http.ClientRequest, opts: AgentConnectOpts): Promise<http.Agent>;
    destroy(): void;
}
export {};
//# sourceMappingURL=index.d.ts.map