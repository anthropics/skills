/// <reference types="node" />
import { LookupAddress, LookupOptions } from 'dns';
import { GMT } from './index';
export declare function dnsLookup(host: string, opts: LookupOptions): Promise<string | LookupAddress[]>;
export declare function isGMT(v?: string): v is GMT;
//# sourceMappingURL=util.d.ts.map