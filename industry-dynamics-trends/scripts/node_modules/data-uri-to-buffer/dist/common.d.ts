export interface ParsedDataURI {
    type: string;
    typeFull: string;
    charset: string;
    buffer: ArrayBuffer;
}
export interface IBufferConversions {
    base64ToArrayBuffer(base64: string): ArrayBuffer;
    stringToBuffer(str: string): ArrayBuffer;
}
/**
 * Returns a `Buffer` instance from the given data URI `uri`.
 *
 * @param {String} uri Data URI to turn into a Buffer instance
 */
export declare const makeDataUriToBuffer: (convert: IBufferConversions) => (uri: string | URL) => ParsedDataURI;
//# sourceMappingURL=common.d.ts.map