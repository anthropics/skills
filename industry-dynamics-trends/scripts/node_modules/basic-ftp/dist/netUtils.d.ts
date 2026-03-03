import { Socket } from "net";
import { ConnectionOptions, TLSSocket } from "tls";
/**
 * Returns a string describing the encryption on a given socket instance.
 */
export declare function describeTLS(socket: Socket | TLSSocket): string;
/**
 * Returns a string describing the remote address of a socket.
 */
export declare function describeAddress(socket: Socket): string;
/**
 * Upgrade a socket connection with TLS.
 */
export declare function upgradeSocket(socket: Socket, options: ConnectionOptions): Promise<TLSSocket>;
/**
 * Returns true if an IP is a private address according to https://tools.ietf.org/html/rfc1918#section-3.
 * This will handle IPv4-mapped IPv6 addresses correctly but return false for all other IPv6 addresses.
 *
 * @param ip  The IP as a string, e.g. "192.168.0.1"
 */
export declare function ipIsPrivateV4Address(ip?: string): boolean;
