import { QuickJSAsyncContext } from "./context-asyncify";
import { QuickJSAsyncEmscriptenModule } from "./emscripten-types";
import { QuickJSAsyncFFI } from "./variants";
import { ModuleEvalOptions, QuickJSWASMModule } from "./module";
import { QuickJSAsyncRuntime } from "./runtime-asyncify";
import { AsyncRuntimeOptions, ContextOptions } from "./types";
/**
 * Asyncified version of [[QuickJSWASMModule]].
 *
 * Due to limitations of Emscripten's ASYNCIFY process, only a single async
 * function call can happen at a time across the entire WebAssembly module.
 *
 * That means that all runtimes, contexts, functions, etc created inside this
 * WebAssembly are limited to a single concurrent async action.
 * **Multiple concurrent async actions is an error.**
 *
 * To allow for multiple concurrent async actions, you must create multiple WebAssembly
 * modules.
 */
export declare class QuickJSAsyncWASMModule extends QuickJSWASMModule {
    /** @private */
    protected ffi: QuickJSAsyncFFI;
    /** @private */
    protected module: QuickJSAsyncEmscriptenModule;
    /** @private */
    constructor(module: QuickJSAsyncEmscriptenModule, ffi: QuickJSAsyncFFI);
    /**
     * Create a new async runtime inside this WebAssembly module. All runtimes inside a
     * module are limited to a single async call at a time. For multiple
     * concurrent async actions, create multiple WebAssembly modules.
     */
    newRuntime(options?: AsyncRuntimeOptions): QuickJSAsyncRuntime;
    /**
     * A simplified API to create a new [[QuickJSRuntime]] and a
     * [[QuickJSContext]] inside that runtime at the same time. The runtime will
     * be disposed when the context is disposed.
     */
    newContext(options?: ContextOptions): QuickJSAsyncContext;
    /** Synchronous evalCode is not supported. */
    evalCode(): never;
    /**
     * One-off evaluate code without needing to create a [[QuickJSRuntimeAsync]] or
     * [[QuickJSContextSync]] explicitly.
     *
     * This version allows for asynchronous Ecmascript module loading.
     *
     * Note that only a single async action can occur at a time inside the entire WebAssembly module.
     * **Multiple concurrent async actions is an error.**
     *
     * See the documentation for [[QuickJSWASMModule.evalCode]] for more details.
     */
    evalCodeAsync(code: string, options: ModuleEvalOptions): Promise<unknown>;
}
