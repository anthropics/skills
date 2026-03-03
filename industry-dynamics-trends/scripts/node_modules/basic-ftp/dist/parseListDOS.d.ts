import { FileInfo } from "./FileInfo";
/**
 * Returns true if a given line might be a DOS-style listing.
 *
 * - Example: `12-05-96  05:03PM       <DIR>          myDir`
 */
export declare function testLine(line: string): boolean;
/**
 * Parse a single line of a DOS-style directory listing.
 */
export declare function parseLine(line: string): FileInfo | undefined;
export declare function transformList(files: FileInfo[]): FileInfo[];
