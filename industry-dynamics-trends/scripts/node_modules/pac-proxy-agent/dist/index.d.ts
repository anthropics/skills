/// <reference types="node" />
/// <reference types="node" />
/// <reference types="node" />
/// <reference types="node" />
import * as net from 'net';
import * as http from 'http';
import { Readable } from 'stream';
import { URL } from 'url';
import { Agent, AgentConnectOpts } from 'agent-base';
import type { HttpProxyAgentOptions } from 'http-proxy-agent';
import type { HttpsProxyAgentOptions } from 'https-proxy-agent';
import type { SocksProxyAgentOptions } from 'socks-proxy-agent';
import { protocols as gProtocols, ProtocolOpts as GetUriOptions } from 'get-uri';
import { FindProxyForURL, PacResolverOptions } from 'pac-resolver';
type Protocols = keyof typeof gProtocols;
type Protocol<T> = T extends `pac+${infer P}:${infer _}` ? P : T extends `${infer P}:${infer _}` ? P : never;
export type PacProxyAgentOptions<T> = http.AgentOptions & PacResolverOptions & GetUriOptions<`${Protocol<T>}:`> & HttpProxyAgentOptions<''> & HttpsProxyAgentOptions<''> & SocksProxyAgentOptions & {
    fallbackToDirect?: boolean;
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
export declare class PacProxyAgent<Uri extends string> extends Agent {
    static readonly protocols: `pac+${Protocols}`[];
    uri: URL;
    opts: PacProxyAgentOptions<Uri>;
    cache?: Readable;
    resolver?: FindProxyForURL;
    resolverHash: string;
    resolverPromise?: Promise<FindProxyForURL>;
    constructor(uri: Uri | URL, opts?: PacProxyAgentOptions<Uri>);
    private clearResolverPromise;
    /**
     * Loads the PAC proxy file from the source if necessary, and returns
     * a generated `FindProxyForURL()` resolver function to use.
     */
    getResolver(): Promise<FindProxyForURL>;
    private loadResolver;
    /**
     * Loads the contents of the PAC proxy file.
     *
     * @api private
     */
    private loadPacFile;
    /**
     * Called when the node-core HTTP client library is creating a new HTTP request.
     */
    connect(req: http.ClientRequest, opts: AgentConnectOpts): Promise<http.Agent | net.Socket>;
}
export {};
//# sourceMappingURL=index.d.ts.map