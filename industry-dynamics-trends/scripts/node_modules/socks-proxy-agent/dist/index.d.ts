/// <reference types="node" />
/// <reference types="node" />
/// <reference types="node" />
import { SocksProxy } from 'socks';
import { Agent, AgentConnectOpts } from 'agent-base';
import * as net from 'net';
import * as http from 'http';
import { URL } from 'url';
type SocksSocketOptions = Omit<net.TcpNetConnectOpts, 'port' | 'host'>;
export type SocksProxyAgentOptions = Omit<SocksProxy, 'ipaddress' | 'host' | 'port' | 'type' | 'userId' | 'password'> & {
    socketOptions?: SocksSocketOptions;
} & http.AgentOptions;
export declare class SocksProxyAgent extends Agent {
    static protocols: readonly ["socks", "socks4", "socks4a", "socks5", "socks5h"];
    readonly shouldLookup: boolean;
    readonly proxy: SocksProxy;
    timeout: number | null;
    socketOptions: SocksSocketOptions | null;
    constructor(uri: string | URL, opts?: SocksProxyAgentOptions);
    /**
     * Initiates a SOCKS connection to the specified SOCKS proxy server,
     * which in turn connects to the specified remote host and port.
     */
    connect(req: http.ClientRequest, opts: AgentConnectOpts): Promise<net.Socket>;
}
export {};
//# sourceMappingURL=index.d.ts.map