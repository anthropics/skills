import { QuickJSContext } from "./context";
import { Asyncify, AsyncifySleepResult, EitherModule, EmscriptenModuleCallbacks } from "./emscripten-types";
import { JSContextPointer, JSRuntimePointer } from "./types-ffi";
import { InterruptHandler, QuickJSRuntime } from "./runtime";
import { ContextOptions, EitherFFI, JSModuleLoader, RuntimeOptions, RuntimeOptionsBase } from "./types";
type EmscriptenCallback<BaseArgs extends any[], Result> = (...args: [Asyncify | undefined, ...BaseArgs]) => Result | AsyncifySleepResult<Result>;
type MaybeAsyncEmscriptenCallback<T extends EmscriptenCallback<any, any>> = T extends EmscriptenCallback<infer Args, infer Result> ? (...args: Args) => Result | Promise<Result> : never;
type MaybeAsyncEmscriptenCallbacks = {
    [K in keyof EmscriptenModuleCallbacks]: MaybeAsyncEmscriptenCallback<EmscriptenModuleCallbacks[K]>;
};
/**
 * @private
 */
export interface ContextCallbacks {
    callFunction: MaybeAsyncEmscriptenCallbacks["callFunction"];
}
/**
 * @private
 */
export interface RuntimeCallbacks {
    shouldInterrupt: MaybeAsyncEmscriptenCallbacks["shouldInterrupt"];
    loadModuleSource: MaybeAsyncEmscriptenCallbacks["loadModuleSource"];
    normalizeModule: MaybeAsyncEmscriptenCallbacks["normalizeModule"];
}
/**
 * Options for [[QuickJSWASMModule.evalCode]].
 */
export interface ModuleEvalOptions {
    /**
     * Interrupt evaluation if `shouldInterrupt` returns `true`.
     * See [[shouldInterruptAfterDeadline]].
     */
    shouldInterrupt?: InterruptHandler;
    /**
     * Memory limit, in bytes, of WebAssembly heap memory used by the QuickJS VM.
     */
    memoryLimitBytes?: number;
    /**
     * Stack size limit for this vm, in bytes
     * To remove the limit, set to `0`.
     */
    maxStackSizeBytes?: number;
    /**
     * Module loader for any `import` statements or expressions.
     */
    moduleLoader?: JSModuleLoader;
}
/**
 * We use static functions per module to dispatch runtime or context calls from
 * C to the host.  This class manages the indirection from a specific runtime or
 * context pointer to the appropriate callback handler.
 *
 * @private
 */
export declare class QuickJSModuleCallbacks {
    private module;
    private contextCallbacks;
    private runtimeCallbacks;
    constructor(module: EitherModule);
    setRuntimeCallbacks(rt: JSRuntimePointer, callbacks: RuntimeCallbacks): void;
    deleteRuntime(rt: JSRuntimePointer): void;
    setContextCallbacks(ctx: JSContextPointer, callbacks: ContextCallbacks): void;
    deleteContext(ctx: JSContextPointer): void;
    private suspendedCount;
    private suspended;
    private handleAsyncify;
    private cToHostCallbacks;
}
/**
 * Process RuntimeOptions and apply them to a QuickJSRuntime.
 * @private
 */
export declare function applyBaseRuntimeOptions(runtime: QuickJSRuntime, options: RuntimeOptionsBase): void;
/**
 * Process ModuleEvalOptions and apply them to a QuickJSRuntime.
 * @private
 */
export declare function applyModuleEvalRuntimeOptions<T extends QuickJSRuntime>(runtime: T, options: ModuleEvalOptions): void;
/**
 * This class presents a Javascript interface to QuickJS, a Javascript interpreter
 * that supports EcmaScript 2020 (ES2020).
 *
 * It wraps a single WebAssembly module containing the QuickJS library and
 * associated helper C code. WebAssembly modules are completely isolated from
 * each other by the host's WebAssembly runtime. Separate WebAssembly modules
 * have the most isolation guarantees possible with this library.
 *
 * The simplest way to start running code is {@link evalCode}. This shortcut
 * method will evaluate Javascript safely and return the result as a native
 * Javascript value.
 *
 * For more control over the execution environment, or to interact with values
 * inside QuickJS, create a context with {@link newContext} or a runtime with
 * {@link newRuntime}.
 */
export declare class QuickJSWASMModule {
    /** @private */
    protected ffi: EitherFFI;
    /** @private */
    protected callbacks: QuickJSModuleCallbacks;
    /** @private */
    protected module: EitherModule;
    /** @private */
    constructor(module: EitherModule, ffi: EitherFFI);
    /**
     * Create a runtime.
     * Use the runtime to set limits on CPU and memory usage and configure module
     * loading for one or more [[QuickJSContext]]s inside the runtime.
     */
    newRuntime(options?: RuntimeOptions): QuickJSRuntime;
    /**
     * A simplified API to create a new [[QuickJSRuntime]] and a
     * [[QuickJSContext]] inside that runtime at the same time. The runtime will
     * be disposed when the context is disposed.
     */
    newContext(options?: ContextOptions): QuickJSContext;
    /**
     * One-off evaluate code without needing to create a [[QuickJSRuntime]] or
     * [[QuickJSContext]] explicitly.
     *
     * To protect against infinite loops, use the `shouldInterrupt` option. The
     * [[shouldInterruptAfterDeadline]] function will create a time-based deadline.
     *
     * If you need more control over how the code executes, create a
     * [[QuickJSRuntime]] (with [[newRuntime]]) or a [[QuickJSContext]] (with
     * [[newContext]] or [[QuickJSRuntime.newContext]]), and use its
     * [[QuickJSContext.evalCode]] method.
     *
     * Asynchronous callbacks may not run during the first call to `evalCode`. If
     * you need to work with async code inside QuickJS, create a runtime and use
     * [[QuickJSRuntime.executePendingJobs]].
     *
     * @returns The result is coerced to a native Javascript value using JSON
     * serialization, so properties and values unsupported by JSON will be dropped.
     *
     * @throws If `code` throws during evaluation, the exception will be
     * converted into a native Javascript value and thrown.
     *
     * @throws if `options.shouldInterrupt` interrupted execution, will throw a Error
     * with name `"InternalError"` and  message `"interrupted"`.
     */
    evalCode(code: string, options?: ModuleEvalOptions): unknown;
    /**
     * Get a low-level interface to the QuickJS functions in this WebAssembly
     * module.
     * @experimental
     * @unstable No warranty is provided with this API. It could change at any time.
     * @private
     */
    getFFI(): EitherFFI;
}
export {};
