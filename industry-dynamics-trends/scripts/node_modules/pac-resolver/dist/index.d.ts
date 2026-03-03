/// <reference types="node" />
/// <reference types="node" />
import { CompileOptions } from 'degenerator';
/**
 * Built-in PAC functions.
 */
import dateRange from './dateRange';
import dnsDomainIs from './dnsDomainIs';
import dnsDomainLevels from './dnsDomainLevels';
import dnsResolve from './dnsResolve';
import isInNet from './isInNet';
import isPlainHostName from './isPlainHostName';
import isResolvable from './isResolvable';
import localHostOrDomainIs from './localHostOrDomainIs';
import myIpAddress from './myIpAddress';
import shExpMatch from './shExpMatch';
import timeRange from './timeRange';
import weekdayRange from './weekdayRange';
import type { QuickJSWASMModule } from '@tootallnate/quickjs-emscripten';
/**
 * Returns an asynchronous `FindProxyForURL()` function
 * from the given JS string (from a PAC file).
 */
export declare function createPacResolver(qjs: QuickJSWASMModule, _str: string | Buffer, _opts?: PacResolverOptions): (url: string | URL, _host?: string) => Promise<string>;
export type GMT = 'GMT';
export type Hour = 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23;
export type Day = 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31;
export type Weekday = 'SUN' | 'MON' | 'TUE' | 'WED' | 'THU' | 'FRI' | 'SAT';
export type Month = 'JAN' | 'FEB' | 'MAR' | 'APR' | 'MAY' | 'JUN' | 'JUL' | 'AUG' | 'SEP' | 'OCT' | 'NOV' | 'DEC';
export type PacResolverOptions = CompileOptions;
export interface FindProxyForURLCallback {
    (err?: Error | null, result?: string): void;
}
export type FindProxyForURL = ReturnType<typeof createPacResolver>;
export declare const sandbox: Readonly<{
    alert: (message?: string) => void;
    dateRange: typeof dateRange;
    dnsDomainIs: typeof dnsDomainIs;
    dnsDomainLevels: typeof dnsDomainLevels;
    dnsResolve: typeof dnsResolve;
    isInNet: typeof isInNet;
    isPlainHostName: typeof isPlainHostName;
    isResolvable: typeof isResolvable;
    localHostOrDomainIs: typeof localHostOrDomainIs;
    myIpAddress: typeof myIpAddress;
    shExpMatch: typeof shExpMatch;
    timeRange: typeof timeRange;
    weekdayRange: typeof weekdayRange;
}>;
//# sourceMappingURL=index.d.ts.map