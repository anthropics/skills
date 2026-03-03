/**
 * The `node:zlib` module provides compression functionality implemented using
 * Gzip, Deflate/Inflate, and Brotli.
 *
 * To access it:
 *
 * ```js
 * import zlib from 'node:zlib';
 * ```
 *
 * Compression and decompression are built around the Node.js
 * [Streams API](https://nodejs.org/docs/latest-v25.x/api/stream.html).
 *
 * Compressing or decompressing a stream (such as a file) can be accomplished by
 * piping the source stream through a `zlib` `Transform` stream into a destination
 * stream:
 *
 * ```js
 * import { createGzip } from 'node:zlib';
 * import { pipeline } from 'node:stream';
 * import {
 *   createReadStream,
 *   createWriteStream,
 * } from 'node:fs';
 *
 * const gzip = createGzip();
 * const source = createReadStream('input.txt');
 * const destination = createWriteStream('input.txt.gz');
 *
 * pipeline(source, gzip, destination, (err) => {
 *   if (err) {
 *     console.error('An error occurred:', err);
 *     process.exitCode = 1;
 *   }
 * });
 *
 * // Or, Promisified
 *
 * import { promisify } from 'node:util';
 * const pipe = promisify(pipeline);
 *
 * async function do_gzip(input, output) {
 *   const gzip = createGzip();
 *   const source = createReadStream(input);
 *   const destination = createWriteStream(output);
 *   await pipe(source, gzip, destination);
 * }
 *
 * do_gzip('input.txt', 'input.txt.gz')
 *   .catch((err) => {
 *     console.error('An error occurred:', err);
 *     process.exitCode = 1;
 *   });
 * ```
 *
 * It is also possible to compress or decompress data in a single step:
 *
 * ```js
 * import { deflate, unzip } from 'node:zlib';
 *
 * const input = '.................................';
 * deflate(input, (err, buffer) => {
 *   if (err) {
 *     console.error('An error occurred:', err);
 *     process.exitCode = 1;
 *   }
 *   console.log(buffer.toString('base64'));
 * });
 *
 * const buffer = Buffer.from('eJzT0yMAAGTvBe8=', 'base64');
 * unzip(buffer, (err, buffer) => {
 *   if (err) {
 *     console.error('An error occurred:', err);
 *     process.exitCode = 1;
 *   }
 *   console.log(buffer.toString());
 * });
 *
 * // Or, Promisified
 *
 * import { promisify } from 'node:util';
 * const do_unzip = promisify(unzip);
 *
 * do_unzip(buffer)
 *   .then((buf) => console.log(buf.toString()))
 *   .catch((err) => {
 *     console.error('An error occurred:', err);
 *     process.exitCode = 1;
 *   });
 * ```
 * @since v0.5.8
 * @see [source](https://github.com/nodejs/node/blob/v25.x/lib/zlib.js)
 */
declare module "node:zlib" {
    import { NonSharedBuffer } from "node:buffer";
    import * as stream from "node:stream";
    interface ZlibOptions {
        /**
         * @default constants.Z_NO_FLUSH
         */
        flush?: number | undefined;
        /**
         * @default constants.Z_FINISH
         */
        finishFlush?: number | undefined;
        /**
         * @default 16*1024
         */
        chunkSize?: number | undefined;
        windowBits?: number | undefined;
        level?: number | undefined; // compression only
        memLevel?: number | undefined; // compression only
        strategy?: number | undefined; // compression only
        dictionary?: NodeJS.ArrayBufferView | ArrayBuffer | undefined; // deflate/inflate only, empty dictionary by default
        /**
         * If `true`, returns an object with `buffer` and `engine`.
         */
        info?: boolean | undefined;
        /**
         * Limits output size when using convenience methods.
         * @default buffer.kMaxLength
         */
        maxOutputLength?: number | undefined;
    }
    interface BrotliOptions {
        /**
         * @default constants.BROTLI_OPERATION_PROCESS
         */
        flush?: number | undefined;
        /**
         * @default constants.BROTLI_OPERATION_FINISH
         */
        finishFlush?: number | undefined;
        /**
         * @default 16*1024
         */
        chunkSize?: number | undefined;
        params?:
            | {
                /**
                 * Each key is a `constants.BROTLI_*` constant.
                 */
                [key: number]: boolean | number;
            }
            | undefined;
        /**
         * Limits output size when using [convenience methods](https://nodejs.org/docs/latest-v25.x/api/zlib.html#convenience-methods).
         * @default buffer.kMaxLength
         */
        maxOutputLength?: number | undefined;
        /**
         * If `true`, returns an object with `buffer` and `engine`.
         */
        info?: boolean | undefined;
    }
    interface ZstdOptions {
        /**
         * @default constants.ZSTD_e_continue
         */
        flush?: number | undefined;
        /**
         * @default constants.ZSTD_e_end
         */
        finishFlush?: number | undefined;
        /**
         * @default 16 * 1024
         */
        chunkSize?: number | undefined;
        /**
         * Key-value object containing indexed
         * [Zstd parameters](https://nodejs.org/docs/latest-v25.x/api/zlib.html#zstd-constants).
         */
        params?: { [key: number]: number | boolean } | undefined;
        /**
         * Limits output size when using
         * [convenience methods](https://nodejs.org/docs/latest-v25.x/api/zlib.html#convenience-methods).
         * @default buffer.kMaxLength
         */
        maxOutputLength?: number | undefined;
        /**
         * If `true`, returns an object with `buffer` and `engine`.
         */
        info?: boolean | undefined;
        /**
         * Optional dictionary used to improve compression efficiency when compressing or decompressing data that
         * shares common patterns with the dictionary.
         * @since v24.6.0
         */
        dictionary?: NodeJS.ArrayBufferView | undefined;
    }
    interface Zlib {
        readonly bytesWritten: number;
        shell?: boolean | string | undefined;
        close(callback?: () => void): void;
        flush(kind?: number, callback?: () => void): void;
        flush(callback?: () => void): void;
    }
    interface ZlibParams {
        params(level: number, strategy: number, callback: () => void): void;
    }
    interface ZlibReset {
        reset(): void;
    }
    interface BrotliCompress extends stream.Transform, Zlib {}
    interface BrotliDecompress extends stream.Transform, Zlib {}
    interface Gzip extends stream.Transform, Zlib {}
    interface Gunzip extends stream.Transform, Zlib {}
    interface Deflate extends stream.Transform, Zlib, ZlibReset, ZlibParams {}
    interface Inflate extends stream.Transform, Zlib, ZlibReset {}
    interface DeflateRaw extends stream.Transform, Zlib, ZlibReset, ZlibParams {}
    interface InflateRaw extends stream.Transform, Zlib, ZlibReset {}
    interface Unzip extends stream.Transform, Zlib {}
    /**
     * @since v22.15.0
     * @experimental
     */
    interface ZstdCompress extends stream.Transform, Zlib {}
    /**
     * @since v22.15.0
     * @experimental
     */
    interface ZstdDecompress extends stream.Transform, Zlib {}
    /**
     * Computes a 32-bit [Cyclic Redundancy Check](https://en.wikipedia.org/wiki/Cyclic_redundancy_check) checksum of `data`.
     * If `value` is specified, it is used as the starting value of the checksum, otherwise, 0 is used as the starting value.
     * @param data When `data` is a string, it will be encoded as UTF-8 before being used for computation.
     * @param value An optional starting value. It must be a 32-bit unsigned integer. @default 0
     * @returns A 32-bit unsigned integer containing the checksum.
     * @since v22.2.0
     */
    function crc32(data: string | NodeJS.ArrayBufferView, value?: number): number;
    /**
     * Creates and returns a new `BrotliCompress` object.
     * @since v11.7.0, v10.16.0
     */
    function createBrotliCompress(options?: BrotliOptions): BrotliCompress;
    /**
     * Creates and returns a new `BrotliDecompress` object.
     * @since v11.7.0, v10.16.0
     */
    function createBrotliDecompress(options?: BrotliOptions): BrotliDecompress;
    /**
     * Creates and returns a new `Gzip` object.
     * See `example`.
     * @since v0.5.8
     */
    function createGzip(options?: ZlibOptions): Gzip;
    /**
     * Creates and returns a new `Gunzip` object.
     * @since v0.5.8
     */
    function createGunzip(options?: ZlibOptions): Gunzip;
    /**
     * Creates and returns a new `Deflate` object.
     * @since v0.5.8
     */
    function createDeflate(options?: ZlibOptions): Deflate;
    /**
     * Creates and returns a new `Inflate` object.
     * @since v0.5.8
     */
    function createInflate(options?: ZlibOptions): Inflate;
    /**
     * Creates and returns a new `DeflateRaw` object.
     *
     * An upgrade of zlib from 1.2.8 to 1.2.11 changed behavior when `windowBits` is set to 8 for raw deflate streams. zlib would automatically set `windowBits` to 9 if was initially set to 8. Newer
     * versions of zlib will throw an exception,
     * so Node.js restored the original behavior of upgrading a value of 8 to 9,
     * since passing `windowBits = 9` to zlib actually results in a compressed stream
     * that effectively uses an 8-bit window only.
     * @since v0.5.8
     */
    function createDeflateRaw(options?: ZlibOptions): DeflateRaw;
    /**
     * Creates and returns a new `InflateRaw` object.
     * @since v0.5.8
     */
    function createInflateRaw(options?: ZlibOptions): InflateRaw;
    /**
     * Creates and returns a new `Unzip` object.
     * @since v0.5.8
     */
    function createUnzip(options?: ZlibOptions): Unzip;
    /**
     * Creates and returns a new `ZstdCompress` object.
     * @since v22.15.0
     */
    function createZstdCompress(options?: ZstdOptions): ZstdCompress;
    /**
     * Creates and returns a new `ZstdDecompress` object.
     * @since v22.15.0
     */
    function createZstdDecompress(options?: ZstdOptions): ZstdDecompress;
    type InputType = string | ArrayBuffer | NodeJS.ArrayBufferView;
    type CompressCallback = (error: Error | null, result: NonSharedBuffer) => void;
    /**
     * @since v11.7.0, v10.16.0
     */
    function brotliCompress(buf: InputType, options: BrotliOptions, callback: CompressCallback): void;
    function brotliCompress(buf: InputType, callback: CompressCallback): void;
    namespace brotliCompress {
        function __promisify__(buffer: InputType, options?: BrotliOptions): Promise<NonSharedBuffer>;
    }
    /**
     * Compress a chunk of data with `BrotliCompress`.
     * @since v11.7.0, v10.16.0
     */
    function brotliCompressSync(buf: InputType, options?: BrotliOptions): NonSharedBuffer;
    /**
     * @since v11.7.0, v10.16.0
     */
    function brotliDecompress(buf: InputType, options: BrotliOptions, callback: CompressCallback): void;
    function brotliDecompress(buf: InputType, callback: CompressCallback): void;
    namespace brotliDecompress {
        function __promisify__(buffer: InputType, options?: BrotliOptions): Promise<NonSharedBuffer>;
    }
    /**
     * Decompress a chunk of data with `BrotliDecompress`.
     * @since v11.7.0, v10.16.0
     */
    function brotliDecompressSync(buf: InputType, options?: BrotliOptions): NonSharedBuffer;
    /**
     * @since v0.6.0
     */
    function deflate(buf: InputType, callback: CompressCallback): void;
    function deflate(buf: InputType, options: ZlibOptions, callback: CompressCallback): void;
    namespace deflate {
        function __promisify__(buffer: InputType, options?: ZlibOptions): Promise<NonSharedBuffer>;
    }
    /**
     * Compress a chunk of data with `Deflate`.
     * @since v0.11.12
     */
    function deflateSync(buf: InputType, options?: ZlibOptions): NonSharedBuffer;
    /**
     * @since v0.6.0
     */
    function deflateRaw(buf: InputType, callback: CompressCallback): void;
    function deflateRaw(buf: InputType, options: ZlibOptions, callback: CompressCallback): void;
    namespace deflateRaw {
        function __promisify__(buffer: InputType, options?: ZlibOptions): Promise<NonSharedBuffer>;
    }
    /**
     * Compress a chunk of data with `DeflateRaw`.
     * @since v0.11.12
     */
    function deflateRawSync(buf: InputType, options?: ZlibOptions): NonSharedBuffer;
    /**
     * @since v0.6.0
     */
    function gzip(buf: InputType, callback: CompressCallback): void;
    function gzip(buf: InputType, options: ZlibOptions, callback: CompressCallback): void;
    namespace gzip {
        function __promisify__(buffer: InputType, options?: ZlibOptions): Promise<NonSharedBuffer>;
    }
    /**
     * Compress a chunk of data with `Gzip`.
     * @since v0.11.12
     */
    function gzipSync(buf: InputType, options?: ZlibOptions): NonSharedBuffer;
    /**
     * @since v0.6.0
     */
    function gunzip(buf: InputType, callback: CompressCallback): void;
    function gunzip(buf: InputType, options: ZlibOptions, callback: CompressCallback): void;
    namespace gunzip {
        function __promisify__(buffer: InputType, options?: ZlibOptions): Promise<NonSharedBuffer>;
    }
    /**
     * Decompress a chunk of data with `Gunzip`.
     * @since v0.11.12
     */
    function gunzipSync(buf: InputType, options?: ZlibOptions): NonSharedBuffer;
    /**
     * @since v0.6.0
     */
    function inflate(buf: InputType, callback: CompressCallback): void;
    function inflate(buf: InputType, options: ZlibOptions, callback: CompressCallback): void;
    namespace inflate {
        function __promisify__(buffer: InputType, options?: ZlibOptions): Promise<NonSharedBuffer>;
    }
    /**
     * Decompress a chunk of data with `Inflate`.
     * @since v0.11.12
     */
    function inflateSync(buf: InputType, options?: ZlibOptions): NonSharedBuffer;
    /**
     * @since v0.6.0
     */
    function inflateRaw(buf: InputType, callback: CompressCallback): void;
    function inflateRaw(buf: InputType, options: ZlibOptions, callback: CompressCallback): void;
    namespace inflateRaw {
        function __promisify__(buffer: InputType, options?: ZlibOptions): Promise<NonSharedBuffer>;
    }
    /**
     * Decompress a chunk of data with `InflateRaw`.
     * @since v0.11.12
     */
    function inflateRawSync(buf: InputType, options?: ZlibOptions): NonSharedBuffer;
    /**
     * @since v0.6.0
     */
    function unzip(buf: InputType, callback: CompressCallback): void;
    function unzip(buf: InputType, options: ZlibOptions, callback: CompressCallback): void;
    namespace unzip {
        function __promisify__(buffer: InputType, options?: ZlibOptions): Promise<NonSharedBuffer>;
    }
    /**
     * Decompress a chunk of data with `Unzip`.
     * @since v0.11.12
     */
    function unzipSync(buf: InputType, options?: ZlibOptions): NonSharedBuffer;
    /**
     * @since v22.15.0
     * @experimental
     */
    function zstdCompress(buf: InputType, callback: CompressCallback): void;
    function zstdCompress(buf: InputType, options: ZstdOptions, callback: CompressCallback): void;
    namespace zstdCompress {
        function __promisify__(buffer: InputType, options?: ZstdOptions): Promise<NonSharedBuffer>;
    }
    /**
     * Compress a chunk of data with `ZstdCompress`.
     * @since v22.15.0
     * @experimental
     */
    function zstdCompressSync(buf: InputType, options?: ZstdOptions): NonSharedBuffer;
    /**
     * @since v22.15.0
     * @experimental
     */
    function zstdDecompress(buf: InputType, callback: CompressCallback): void;
    function zstdDecompress(buf: InputType, options: ZstdOptions, callback: CompressCallback): void;
    namespace zstdDecompress {
        function __promisify__(buffer: InputType, options?: ZstdOptions): Promise<NonSharedBuffer>;
    }
    /**
     * Decompress a chunk of data with `ZstdDecompress`.
     * @since v22.15.0
     * @experimental
     */
    function zstdDecompressSync(buf: InputType, options?: ZstdOptions): NonSharedBuffer;
    namespace constants {
        const BROTLI_DECODE: number;
        const BROTLI_DECODER_ERROR_ALLOC_BLOCK_TYPE_TREES: number;
        const BROTLI_DECODER_ERROR_ALLOC_CONTEXT_MAP: number;
        const BROTLI_DECODER_ERROR_ALLOC_CONTEXT_MODES: number;
        const BROTLI_DECODER_ERROR_ALLOC_RING_BUFFER_1: number;
        const BROTLI_DECODER_ERROR_ALLOC_RING_BUFFER_2: number;
        const BROTLI_DECODER_ERROR_ALLOC_TREE_GROUPS: number;
        const BROTLI_DECODER_ERROR_DICTIONARY_NOT_SET: number;
        const BROTLI_DECODER_ERROR_FORMAT_BLOCK_LENGTH_1: number;
        const BROTLI_DECODER_ERROR_FORMAT_BLOCK_LENGTH_2: number;
        const BROTLI_DECODER_ERROR_FORMAT_CL_SPACE: number;
        const BROTLI_DECODER_ERROR_FORMAT_CONTEXT_MAP_REPEAT: number;
        const BROTLI_DECODER_ERROR_FORMAT_DICTIONARY: number;
        const BROTLI_DECODER_ERROR_FORMAT_DISTANCE: number;
        const BROTLI_DECODER_ERROR_FORMAT_EXUBERANT_META_NIBBLE: number;
        const BROTLI_DECODER_ERROR_FORMAT_EXUBERANT_NIBBLE: number;
        const BROTLI_DECODER_ERROR_FORMAT_HUFFMAN_SPACE: number;
        const BROTLI_DECODER_ERROR_FORMAT_PADDING_1: number;
        const BROTLI_DECODER_ERROR_FORMAT_PADDING_2: number;
        const BROTLI_DECODER_ERROR_FORMAT_RESERVED: number;
        const BROTLI_DECODER_ERROR_FORMAT_SIMPLE_HUFFMAN_ALPHABET: number;
        const BROTLI_DECODER_ERROR_FORMAT_SIMPLE_HUFFMAN_SAME: number;
        const BROTLI_DECODER_ERROR_FORMAT_TRANSFORM: number;
        const BROTLI_DECODER_ERROR_FORMAT_WINDOW_BITS: number;
        const BROTLI_DECODER_ERROR_INVALID_ARGUMENTS: number;
        const BROTLI_DECODER_ERROR_UNREACHABLE: number;
        const BROTLI_DECODER_NEEDS_MORE_INPUT: number;
        const BROTLI_DECODER_NEEDS_MORE_OUTPUT: number;
        const BROTLI_DECODER_NO_ERROR: number;
        const BROTLI_DECODER_PARAM_DISABLE_RING_BUFFER_REALLOCATION: number;
        const BROTLI_DECODER_PARAM_LARGE_WINDOW: number;
        const BROTLI_DECODER_RESULT_ERROR: number;
        const BROTLI_DECODER_RESULT_NEEDS_MORE_INPUT: number;
        const BROTLI_DECODER_RESULT_NEEDS_MORE_OUTPUT: number;
        const BROTLI_DECODER_RESULT_SUCCESS: number;
        const BROTLI_DECODER_SUCCESS: number;
        const BROTLI_DEFAULT_MODE: number;
        const BROTLI_DEFAULT_QUALITY: number;
        const BROTLI_DEFAULT_WINDOW: number;
        const BROTLI_ENCODE: number;
        const BROTLI_LARGE_MAX_WINDOW_BITS: number;
        const BROTLI_MAX_INPUT_BLOCK_BITS: number;
        const BROTLI_MAX_QUALITY: number;
        const BROTLI_MAX_WINDOW_BITS: number;
        const BROTLI_MIN_INPUT_BLOCK_BITS: number;
        const BROTLI_MIN_QUALITY: number;
        const BROTLI_MIN_WINDOW_BITS: number;
        const BROTLI_MODE_FONT: number;
        const BROTLI_MODE_GENERIC: number;
        const BROTLI_MODE_TEXT: number;
        const BROTLI_OPERATION_EMIT_METADATA: number;
        const BROTLI_OPERATION_FINISH: number;
        const BROTLI_OPERATION_FLUSH: number;
        const BROTLI_OPERATION_PROCESS: number;
        const BROTLI_PARAM_DISABLE_LITERAL_CONTEXT_MODELING: number;
        const BROTLI_PARAM_LARGE_WINDOW: number;
        const BROTLI_PARAM_LGBLOCK: number;
        const BROTLI_PARAM_LGWIN: number;
        const BROTLI_PARAM_MODE: number;
        const BROTLI_PARAM_NDIRECT: number;
        const BROTLI_PARAM_NPOSTFIX: number;
        const BROTLI_PARAM_QUALITY: number;
        const BROTLI_PARAM_SIZE_HINT: number;
        const DEFLATE: number;
        const DEFLATERAW: number;
        const GUNZIP: number;
        const GZIP: number;
        const INFLATE: number;
        const INFLATERAW: number;
        const UNZIP: number;
        const ZLIB_VERNUM: number;
        const ZSTD_CLEVEL_DEFAULT: number;
        const ZSTD_COMPRESS: number;
        const ZSTD_DECOMPRESS: number;
        const ZSTD_btlazy2: number;
        const ZSTD_btopt: number;
        const ZSTD_btultra: number;
        const ZSTD_btultra2: number;
        const ZSTD_c_chainLog: number;
        const ZSTD_c_checksumFlag: number;
        const ZSTD_c_compressionLevel: number;
        const ZSTD_c_contentSizeFlag: number;
        const ZSTD_c_dictIDFlag: number;
        const ZSTD_c_enableLongDistanceMatching: number;
        const ZSTD_c_hashLog: number;
        const ZSTD_c_jobSize: number;
        const ZSTD_c_ldmBucketSizeLog: number;
        const ZSTD_c_ldmHashLog: number;
        const ZSTD_c_ldmHashRateLog: number;
        const ZSTD_c_ldmMinMatch: number;
        const ZSTD_c_minMatch: number;
        const ZSTD_c_nbWorkers: number;
        const ZSTD_c_overlapLog: number;
        const ZSTD_c_searchLog: number;
        const ZSTD_c_strategy: number;
        const ZSTD_c_targetLength: number;
        const ZSTD_c_windowLog: number;
        const ZSTD_d_windowLogMax: number;
        const ZSTD_dfast: number;
        const ZSTD_e_continue: number;
        const ZSTD_e_end: number;
        const ZSTD_e_flush: number;
        const ZSTD_error_GENERIC: number;
        const ZSTD_error_checksum_wrong: number;
        const ZSTD_error_corruption_detected: number;
        const ZSTD_error_dictionaryCreation_failed: number;
        const ZSTD_error_dictionary_corrupted: number;
        const ZSTD_error_dictionary_wrong: number;
        const ZSTD_error_dstBuffer_null: number;
        const ZSTD_error_dstSize_tooSmall: number;
        const ZSTD_error_frameParameter_unsupported: number;
        const ZSTD_error_frameParameter_windowTooLarge: number;
        const ZSTD_error_init_missing: number;
        const ZSTD_error_literals_headerWrong: number;
        const ZSTD_error_maxSymbolValue_tooLarge: number;
        const ZSTD_error_maxSymbolValue_tooSmall: number;
        const ZSTD_error_memory_allocation: number;
        const ZSTD_error_noForwardProgress_destFull: number;
        const ZSTD_error_noForwardProgress_inputEmpty: number;
        const ZSTD_error_no_error: number;
        const ZSTD_error_parameter_combination_unsupported: number;
        const ZSTD_error_parameter_outOfBound: number;
        const ZSTD_error_parameter_unsupported: number;
        const ZSTD_error_prefix_unknown: number;
        const ZSTD_error_srcSize_wrong: number;
        const ZSTD_error_stabilityCondition_notRespected: number;
        const ZSTD_error_stage_wrong: number;
        const ZSTD_error_tableLog_tooLarge: number;
        const ZSTD_error_version_unsupported: number;
        const ZSTD_error_workSpace_tooSmall: number;
        const ZSTD_fast: number;
        const ZSTD_greedy: number;
        const ZSTD_lazy: number;
        const ZSTD_lazy2: number;
        const Z_BEST_COMPRESSION: number;
        const Z_BEST_SPEED: number;
        const Z_BLOCK: number;
        const Z_BUF_ERROR: number;
        const Z_DATA_ERROR: number;
        const Z_DEFAULT_CHUNK: number;
        const Z_DEFAULT_COMPRESSION: number;
        const Z_DEFAULT_LEVEL: number;
        const Z_DEFAULT_MEMLEVEL: number;
        const Z_DEFAULT_STRATEGY: number;
        const Z_DEFAULT_WINDOWBITS: number;
        const Z_ERRNO: number;
        const Z_FILTERED: number;
        const Z_FINISH: number;
        const Z_FIXED: number;
        const Z_FULL_FLUSH: number;
        const Z_HUFFMAN_ONLY: number;
        const Z_MAX_CHUNK: number;
        const Z_MAX_LEVEL: number;
        const Z_MAX_MEMLEVEL: number;
        const Z_MAX_WINDOWBITS: number;
        const Z_MEM_ERROR: number;
        const Z_MIN_CHUNK: number;
        const Z_MIN_LEVEL: number;
        const Z_MIN_MEMLEVEL: number;
        const Z_MIN_WINDOWBITS: number;
        const Z_NEED_DICT: number;
        const Z_NO_COMPRESSION: number;
        const Z_NO_FLUSH: number;
        const Z_OK: number;
        const Z_PARTIAL_FLUSH: number;
        const Z_RLE: number;
        const Z_STREAM_END: number;
        const Z_STREAM_ERROR: number;
        const Z_SYNC_FLUSH: number;
        const Z_VERSION_ERROR: number;
    }
}
declare module "zlib" {
    export * from "node:zlib";
}
