import type { QuickJSWASMModule } from "./module";
import type { QuickJSRuntime, InterruptHandler } from "./runtime";
import type { QuickJSContext } from "./context";
export type { QuickJSWASMModule, QuickJSContext, QuickJSRuntime };
import type { QuickJSAsyncWASMModule } from "./module-asyncify";
import type { QuickJSAsyncRuntime } from "./runtime-asyncify";
import type { QuickJSAsyncContext, AsyncFunctionImplementation } from "./context-asyncify";
import { AsyncRuntimeOptions, ContextOptions } from "./types";
export type { QuickJSAsyncContext, QuickJSAsyncRuntime, QuickJSAsyncWASMModule, AsyncFunctionImplementation, };
import { newQuickJSWASMModule, newQuickJSAsyncWASMModule, DEBUG_ASYNC, DEBUG_SYNC, RELEASE_ASYNC, RELEASE_SYNC, SyncBuildVariant, AsyncBuildVariant } from "./variants";
export { newQuickJSWASMModule, newQuickJSAsyncWASMModule, DEBUG_ASYNC, DEBUG_SYNC, RELEASE_ASYNC, RELEASE_SYNC, SyncBuildVariant, AsyncBuildVariant, };
export * from "./vm-interface";
export * from "./lifetime";
/** Collects the informative errors this library may throw. */
export * as errors from "./errors";
export * from "./deferred-promise";
export * from "./module-test";
export type { StaticJSValue, JSValueConst, JSValue, QuickJSHandle, ContextOptions, ContextEvalOptions, RuntimeOptions, AsyncRuntimeOptions, RuntimeOptionsBase, JSModuleLoader, JSModuleLoadResult, JSModuleLoaderAsync, JSModuleLoadSuccess, JSModuleLoadFailure, JSModuleNormalizer, JSModuleNormalizerAsync, JSModuleNormalizeResult, JSModuleNormalizeFailure, JSModuleNormalizeSuccess, } from "./types";
export type { ModuleEvalOptions } from "./module";
export type { InterruptHandler, ExecutePendingJobsResult } from "./runtime";
export type { QuickJSPropertyKey } from "./context";
/**
 * Get a shared singleton {@link QuickJSWASMModule}. Use this to evaluate code
 * or create Javascript environments.
 *
 * This is the top-level entrypoint for the quickjs-emscripten library.
 *
 * If you need strictest possible isolation guarantees, you may create a
 * separate {@link QuickJSWASMModule} via {@link newQuickJSWASMModule}.
 *
 * To work with the asyncified version of this library, see these functions:
 *
 * - {@link newAsyncRuntime}.
 * - {@link newAsyncContext}.
 * - {@link newQuickJSAsyncWASMModule}.
 */
export declare function getQuickJS(): Promise<QuickJSWASMModule>;
/**
 * Provides synchronous access to the shared {@link QuickJSWASMModule} instance returned by {@link getQuickJS}, as long as
 * least once.
 * @throws If called before `getQuickJS` resolves.
 */
export declare function getQuickJSSync(): QuickJSWASMModule;
/**
 * Create a new [[QuickJSAsyncRuntime]] in a separate WebAssembly module.
 *
 * Each runtime is isolated in a separate WebAssembly module, so that errors in
 * one runtime cannot contaminate another runtime, and each runtime can execute
 * an asynchronous action without conflicts.
 *
 * Note that there is a hard limit on the number of WebAssembly modules in older
 * versions of v8:
 * https://bugs.chromium.org/p/v8/issues/detail?id=12076
 */
export declare function newAsyncRuntime(options?: AsyncRuntimeOptions): Promise<QuickJSAsyncRuntime>;
/**
 * Create a new [[QuickJSAsyncContext]] (with an associated runtime) in an
 * separate WebAssembly module.
 *
 * Each context is isolated in a separate WebAssembly module, so that errors in
 * one runtime cannot contaminate another runtime, and each runtime can execute
 * an asynchronous action without conflicts.
 *
 * Note that there is a hard limit on the number of WebAssembly modules in older
 * versions of v8:
 * https://bugs.chromium.org/p/v8/issues/detail?id=12076
 */
export declare function newAsyncContext(options?: ContextOptions): Promise<QuickJSAsyncContext>;
/**
 * Returns an interrupt handler that interrupts Javascript execution after a deadline time.
 *
 * @param deadline - Interrupt execution if it's still running after this time.
 *   Number values are compared against `Date.now()`
 */
export declare function shouldInterruptAfterDeadline(deadline: Date | number): InterruptHandler;
