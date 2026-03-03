export interface ParsedResponse {
    readonly messages: string[];
    readonly rest: string;
}
/**
 * Parse an FTP control response as a collection of messages. A message is a complete
 * single- or multiline response. A response can also contain multiple multiline responses
 * that will each be represented by a message. A response can also be incomplete
 * and be completed on the next incoming data chunk for which case this function also
 * describes a `rest`. This function converts all CRLF to LF.
 */
export declare function parseControlResponse(text: string): ParsedResponse;
export declare function isSingleLine(line: string): boolean;
export declare function isMultiline(line: string): boolean;
/**
 * Return true if an FTP return code describes a positive completion.
 */
export declare function positiveCompletion(code: number): boolean;
/**
 * Return true if an FTP return code describes a positive intermediate response.
 */
export declare function positiveIntermediate(code: number): boolean;
