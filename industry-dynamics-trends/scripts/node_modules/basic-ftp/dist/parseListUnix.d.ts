import { FileInfo } from "./FileInfo";
/**
 * Returns true if a given line might be a Unix-style listing.
 *
 * - Example: `-rw-r--r--+   1 patrick  staff   1057 Dec 11 14:35 test.txt`
 */
export declare function testLine(line: string): boolean;
/**
 * Parse a single line of a Unix-style directory listing.
 */
export declare function parseLine(line: string): FileInfo | undefined;
export declare function transformList(files: FileInfo[]): FileInfo[];
