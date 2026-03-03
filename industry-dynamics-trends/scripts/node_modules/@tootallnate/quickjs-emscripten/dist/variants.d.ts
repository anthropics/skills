import type { QuickJSFFI as ReleaseSyncFFI } from "./generated/ffi.WASM_RELEASE_SYNC";
import type { EmscriptenModuleLoader, QuickJSEmscriptenModule, QuickJSAsyncEmscriptenModule } from "./emscripten-types";
import type { QuickJSWASMModule } from "./module";
import type { QuickJSAsyncWASMModule } from "./module-asyncify";
/** @private */
export type QuickJSFFI = ReleaseSyncFFI;
/** @private */
export type QuickJSFFIConstructor = typeof ReleaseSyncFFI;
/** @private */
export type QuickJSAsyncFFI = any;
/** @private */
export type QuickJSAsyncFFIConstructor = any;
/**
 * quickjs-emscripten provides multiple build variants of the core WebAssembly
 * module. These variants are each intended for a different use case.
 *
 * To create an instance of the library using a specific build variant, pass the
 * build variant to {@link newQuickJSWASMModule} or {@link newQuickJSAsyncWASMModule}.
 *
 * Synchronous build variants:
 *
 * - {@link RELEASE_SYNC} - This is the default synchronous variant, for general purpose use.
 * - {@link DEBUG_SYNC} - Synchronous build variant for debugging memory leaks.
 */
export interface SyncBuildVariant {
    type: "sync";
    importFFI: () => Promise<QuickJSFFIConstructor>;
    importModuleLoader: () => Promise<EmscriptenModuleLoader<QuickJSEmscriptenModule>>;
}
/**
 * quickjs-emscripten provides multiple build variants of the core WebAssembly
 * module. These variants are each intended for a different use case.
 *
 * To create an instance of the library using a specific build variant, pass the
 * build variant to {@link newQuickJSWASMModule} or {@link newQuickJSAsyncWASMModule}.
 *
 * Asyncified build variants:
 *
 * - {@link RELEASE_ASYNC} - This is the default asyncified build variant, for general purpose use.
 * - {@link DEBUG_ASYNC} - Asyncified build variant with debug logging.
 */
export interface AsyncBuildVariant {
    type: "async";
    importFFI: () => Promise<QuickJSAsyncFFIConstructor>;
    importModuleLoader: () => Promise<EmscriptenModuleLoader<QuickJSAsyncEmscriptenModule>>;
}
/**
 * Create a new, completely isolated WebAssembly module containing the QuickJS library.
 * See the documentation on [[QuickJSWASMModule]].
 *
 * Note that there is a hard limit on the number of WebAssembly modules in older
 * versions of v8:
 * https://bugs.chromium.org/p/v8/issues/detail?id=12076
 */
export declare function newQuickJSWASMModule(
/**
 * Optionally, pass a {@link SyncBuildVariant} to construct a different WebAssembly module.
 */
variant?: SyncBuildVariant): Promise<QuickJSWASMModule>;
/**
 * Create a new, completely isolated WebAssembly module containing a version of the QuickJS library
 * compiled with Emscripten's [ASYNCIFY](https://emscripten.org/docs/porting/asyncify.html) transform.
 *
 * This version of the library offers features that enable synchronous code
 * inside the VM to interact with asynchronous code in the host environment.
 * See the documentation on [[QuickJSAsyncWASMModule]], [[QuickJSAsyncRuntime]],
 * and [[QuickJSAsyncContext]].
 *
 * Note that there is a hard limit on the number of WebAssembly modules in older
 * versions of v8:
 * https://bugs.chromium.org/p/v8/issues/detail?id=12076
 */
export declare function newQuickJSAsyncWASMModule(
/**
 * Optionally, pass a {@link AsyncBuildVariant} to construct a different WebAssembly module.
 */
variant?: AsyncBuildVariant): Promise<QuickJSAsyncWASMModule>;
/**
 * Helper intended to memoize the creation of a WebAssembly module.
 * ```typescript
 * const getDebugModule = memoizePromiseFactory(() => newQuickJSWASMModule(DEBUG_SYNC))
 * ```
 */
export declare function memoizePromiseFactory<T>(fn: () => Promise<T>): () => Promise<T>;
/**
 * This build variant is compiled with `-fsanitize=leak`. It instruments all
 * memory allocations and when combined with sourcemaps, can present stack trace
 * locations where memory leaks occur.
 *
 * See [[TestQuickJSWASMModule]] which provides access to the leak sanitizer via
 * {@link TestQuickJSWASMModule.assertNoMemoryAllocated}.
 *
 * The downside is that it's 100-1000x slower than the other variants.
 * Suggested use case: automated testing, regression testing, and interactive
 * debugging.
 */
export declare const DEBUG_SYNC: SyncBuildVariant;
/**
 * This is the default (synchronous) build variant.
 * {@link getQuickJS} returns a memoized instance of this build variant.
 */
export declare const RELEASE_SYNC: SyncBuildVariant;
/**
 * The async debug build variant may or may not have the sanitizer enabled.
 * It does print a lot of debug logs.
 *
 * Suggested use case: interactive debugging only.
 */
export declare const DEBUG_ASYNC: AsyncBuildVariant;
/**
 * This is the default asyncified build variant.
 */
export declare const RELEASE_ASYNC: AsyncBuildVariant;
