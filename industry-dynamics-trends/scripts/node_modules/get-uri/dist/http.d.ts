/// <reference types="node" />
/// <reference types="node" />
/// <reference types="node" />
/// <reference types="node" />
import http_ from 'http';
import https from 'https';
import { Readable } from 'stream';
import { GetUriProtocol } from '.';
type HttpOrHttpsModule = typeof http_ | typeof https;
export interface HttpReadableProps {
    date?: number;
    parsed?: URL;
    redirects?: HttpReadable[];
}
export interface HttpReadable extends Readable, HttpReadableProps {
}
export interface HttpIncomingMessage extends http_.IncomingMessage, HttpReadableProps {
}
export interface HttpOptions extends https.RequestOptions {
    cache?: HttpReadable;
    http?: HttpOrHttpsModule;
    redirects?: HttpReadable[];
    maxRedirects?: number;
}
/**
 * Returns a Readable stream from an "http:" URI.
 */
export declare const http: GetUriProtocol<HttpOptions>;
export {};
