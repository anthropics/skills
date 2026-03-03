/// <reference types="node" />
/// <reference types="node" />
import { Readable } from 'stream';
type Protocol<T> = T extends `${infer Protocol}:${infer _}` ? Protocol : never;
export type GetUriProtocol<T> = (parsed: URL, opts?: T) => Promise<Readable>;
export declare const protocols: {
    data: GetUriProtocol<import("./data").DataOptions>;
    file: GetUriProtocol<import("./file").FileOptions>;
    ftp: GetUriProtocol<import("./ftp").FTPOptions>;
    http: GetUriProtocol<import("./http").HttpOptions>;
    https: GetUriProtocol<import("./http").HttpOptions>;
};
export type Protocols = typeof protocols;
export type ProtocolsOptions = {
    [P in keyof Protocols]: NonNullable<Parameters<Protocols[P]>[1]>;
};
export type ProtocolOpts<T> = {
    [P in keyof ProtocolsOptions]: Protocol<T> extends P ? ProtocolsOptions[P] : never;
}[keyof Protocols];
export declare function isValidProtocol(p: string): p is keyof Protocols;
/**
 * Async function that returns a `stream.Readable` instance that will output
 * the contents of the given URI.
 *
 * For caching purposes, you can pass in a `stream` instance from a previous
 * `getUri()` call as a `cache: stream` option, and if the destination has
 * not changed since the last time the endpoint was retrieved then the callback
 * will be invoked with an Error object with `code` set to "ENOTMODIFIED" and
 * `null` for the "stream" instance argument. In this case, you can skip
 * retrieving the file again and continue to use the previous payload.
 *
 * @param {String} uri URI to retrieve
 * @param {Object} opts optional "options" object
 * @api public
 */
export declare function getUri<Uri extends string>(uri: Uri | URL, opts?: ProtocolOpts<Uri>): Promise<Readable>;
export {};
