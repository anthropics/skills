import { Writable, Readable } from "stream";
import { FTPContext, FTPResponse } from "./FtpContext";
import { ProgressTracker, ProgressType } from "./ProgressTracker";
export type UploadCommand = "STOR" | "APPE";
/**
 * Prepare a data socket using passive mode over IPv6.
 */
export declare function enterPassiveModeIPv6(ftp: FTPContext): Promise<FTPResponse>;
/**
 * Parse an EPSV response. Returns only the port as in EPSV the host of the control connection is used.
 */
export declare function parseEpsvResponse(message: string): number;
/**
 * Prepare a data socket using passive mode over IPv4.
 */
export declare function enterPassiveModeIPv4(ftp: FTPContext): Promise<FTPResponse>;
/**
 * Prepare a data socket using passive mode over IPv4. Ignore the IP provided by the PASV response,
 * and use the control host IP. This is the same behaviour as with the more modern variant EPSV. Use
 * this to fix issues around NAT or provide more security by preventing FTP bounce attacks.
 */
export declare function enterPassiveModeIPv4_forceControlHostIP(ftp: FTPContext): Promise<FTPResponse>;
/**
 * Parse a PASV response.
 */
export declare function parsePasvResponse(message: string): {
    host: string;
    port: number;
};
export declare function connectForPassiveTransfer(host: string, port: number, ftp: FTPContext): Promise<void>;
export interface TransferConfig {
    command: string;
    remotePath: string;
    type: ProgressType;
    ftp: FTPContext;
    tracker: ProgressTracker;
}
export declare function uploadFrom(source: Readable, config: TransferConfig): Promise<FTPResponse>;
export declare function downloadTo(destination: Writable, config: TransferConfig): Promise<FTPResponse>;
