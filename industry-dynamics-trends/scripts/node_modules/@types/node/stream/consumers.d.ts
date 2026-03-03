/**
 * The utility consumer functions provide common options for consuming
 * streams.
 * @since v16.7.0
 */
declare module "node:stream/consumers" {
    import { Blob, NonSharedBuffer } from "node:buffer";
    import { ReadableStream } from "node:stream/web";
    /**
     * @since v16.7.0
     * @returns Fulfills with an `ArrayBuffer` containing the full contents of the stream.
     */
    function arrayBuffer(stream: ReadableStream | NodeJS.ReadableStream | AsyncIterable<any>): Promise<ArrayBuffer>;
    /**
     * @since v16.7.0
     * @returns Fulfills with a `Blob` containing the full contents of the stream.
     */
    function blob(stream: ReadableStream | NodeJS.ReadableStream | AsyncIterable<any>): Promise<Blob>;
    /**
     * @since v16.7.0
     * @returns Fulfills with a `Buffer` containing the full contents of the stream.
     */
    function buffer(stream: ReadableStream | NodeJS.ReadableStream | AsyncIterable<any>): Promise<NonSharedBuffer>;
    /**
     * @since v16.7.0
     * @returns Fulfills with the contents of the stream parsed as a
     * UTF-8 encoded string that is then passed through `JSON.parse()`.
     */
    function json(stream: ReadableStream | NodeJS.ReadableStream | AsyncIterable<any>): Promise<unknown>;
    /**
     * @since v16.7.0
     * @returns Fulfills with the contents of the stream parsed as a UTF-8 encoded string.
     */
    function text(stream: ReadableStream | NodeJS.ReadableStream | AsyncIterable<any>): Promise<string>;
}
declare module "stream/consumers" {
    export * from "node:stream/consumers";
}
