import { BorrowedHeapCharPointer, JSContextPointer, JSRuntimePointer, JSValueConstPointer, JSValuePointer, OwnedHeapCharPointer } from "./types-ffi";
declare namespace Emscripten {
    interface FileSystemType {
    }
    type EnvironmentType = "WEB" | "NODE" | "SHELL" | "WORKER";
    type ValueType = "number" | "string" | "array" | "boolean";
    type TypeCompatibleWithC = number | string | any[] | boolean;
    type WebAssemblyImports = Array<{
        name: string;
        kind: string;
    }>;
    type WebAssemblyExports = Array<{
        module: string;
        name: string;
        kind: string;
    }>;
    interface CCallOpts {
        async?: boolean;
    }
}
/**
 * Typings for the features we use to interface with our Emscripten build of
 * QuickJS.
 */
interface EmscriptenModule {
    /**
     * Write JS `str` to HeapChar pointer.
     * https://emscripten.org/docs/api_reference/preamble.js.html#stringToUTF8
     */
    stringToUTF8(str: string, outPtr: OwnedHeapCharPointer, maxBytesToRead?: number): void;
    /**
     * HeapChar to JS string.
     * https://emscripten.org/docs/api_reference/preamble.js.html#UTF8ToString
     */
    UTF8ToString(ptr: BorrowedHeapCharPointer, maxBytesToRead?: number): string;
    lengthBytesUTF8(str: string): number;
    _malloc(size: number): number;
    _free(ptr: number): void;
    cwrap(ident: string, returnType: Emscripten.ValueType | null, argTypes: Emscripten.ValueType[], opts?: Emscripten.CCallOpts): (...args: any[]) => any;
    HEAP8: Int8Array;
    HEAP16: Int16Array;
    HEAP32: Int32Array;
    HEAPU8: Uint8Array;
    HEAPU16: Uint16Array;
    HEAPU32: Uint32Array;
    HEAPF32: Float32Array;
    HEAPF64: Float64Array;
    TOTAL_STACK: number;
    TOTAL_MEMORY: number;
    FAST_MEMORY: number;
}
declare const AsyncifySleepReturnValue: unique symbol;
/** @private */
export type AsyncifySleepResult<T> = T & typeof AsyncifySleepReturnValue;
/**
 * Allows us to optionally suspend the Emscripten runtime to wait for a promise.
 * https://emscripten.org/docs/porting/asyncify.html#ways-to-use-async-apis-in-older-engines
 * ```
 * EM_JS(int, do_fetch, (), {
 *   return Asyncify.handleSleep(function (wakeUp) {
 *     out("waiting for a fetch");
 *     fetch("a.html").then(function (response) {
 *       out("got the fetch response");
 *       // (normally you would do something with the fetch here)
 *       wakeUp(42);
 *     });
 *   });
 * });
 * ```
 * @private
 */
export interface Asyncify {
    handleSleep<T>(maybeAsyncFn: (wakeUp: (result: T) => void) => void): AsyncifySleepResult<T>;
}
/**
 * @private
 */
export interface EmscriptenModuleCallbacks {
    callFunction: (asyncify: Asyncify | undefined, ctx: JSContextPointer, this_ptr: JSValueConstPointer, argc: number, argv: JSValueConstPointer, fn_id: number) => JSValuePointer | AsyncifySleepResult<JSValuePointer>;
    loadModuleSource: (asyncify: Asyncify | undefined, rt: JSRuntimePointer, ctx: JSContextPointer, module_name: string) => BorrowedHeapCharPointer | AsyncifySleepResult<BorrowedHeapCharPointer>;
    normalizeModule: (asyncify: Asyncify | undefined, rt: JSRuntimePointer, ctx: JSContextPointer, module_base_name: string, module_name: string) => BorrowedHeapCharPointer | AsyncifySleepResult<BorrowedHeapCharPointer>;
    shouldInterrupt: (asyncify: Asyncify | undefined, rt: JSRuntimePointer) => 0 | 1 | AsyncifySleepResult<0 | 1>;
}
export interface QuickJSEmscriptenModule extends EmscriptenModule {
    type: "sync";
    callbacks: EmscriptenModuleCallbacks;
}
export interface QuickJSAsyncEmscriptenModule extends EmscriptenModule {
    /** @todo Implement this field */
    type: "async";
    callbacks: EmscriptenModuleCallbacks;
}
export type EitherModule = QuickJSEmscriptenModule | QuickJSAsyncEmscriptenModule;
export interface EmscriptenModuleLoader<T extends EmscriptenModule> {
    (): Promise<T>;
}
export {};
