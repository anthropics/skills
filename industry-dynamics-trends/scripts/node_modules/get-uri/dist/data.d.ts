/// <reference types="node" />
/// <reference types="node" />
import { Readable } from 'stream';
import { GetUriProtocol } from './';
declare class DataReadable extends Readable {
    hash?: string;
    constructor(hash: string, buf: Buffer);
}
export interface DataOptions {
    cache?: DataReadable;
}
/**
 * Returns a Readable stream from a "data:" URI.
 */
export declare const data: GetUriProtocol<DataOptions>;
export {};
