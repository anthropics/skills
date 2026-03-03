import { QuickJSContext } from "./context";
import { QuickJSAsyncEmscriptenModule } from "./emscripten-types";
import { QuickJSAsyncFFI } from "./variants";
import { JSRuntimePointer } from "./types-ffi";
import { Lifetime } from "./lifetime";
import { QuickJSModuleCallbacks } from "./module";
import { QuickJSAsyncRuntime } from "./runtime-asyncify";
import { ContextEvalOptions, QuickJSHandle } from "./types";
import { VmCallResult } from "./vm-interface";
export type AsyncFunctionImplementation = (this: QuickJSHandle, ...args: QuickJSHandle[]) => Promise<QuickJSHandle | VmCallResult<QuickJSHandle> | void>;
/**
 * Asyncified version of [[QuickJSContext]].
 *
 * *Asyncify* allows normally synchronous code to wait for asynchronous Promises
 * or callbacks. The asyncified version of QuickJSContext can wait for async
 * host functions as though they were synchronous.
 */
export declare class QuickJSAsyncContext extends QuickJSContext {
    runtime: QuickJSAsyncRuntime;
    /** @private */
    protected module: QuickJSAsyncEmscriptenModule;
    /** @private */
    protected ffi: QuickJSAsyncFFI;
    /** @private */
    protected rt: Lifetime<JSRuntimePointer>;
    /** @private */
    protected callbacks: QuickJSModuleCallbacks;
    /**
     * Asyncified version of [[evalCode]].
     */
    evalCodeAsync(code: string, filename?: string, 
    /** See [[EvalFlags]] for number semantics */
    options?: number | ContextEvalOptions): Promise<VmCallResult<QuickJSHandle>>;
    /**
     * Similar to [[newFunction]].
     * Convert an async host Javascript function into a synchronous QuickJS function value.
     *
     * Whenever QuickJS calls this function, the VM's stack will be unwound while
     * waiting the async function to complete, and then restored when the returned
     * promise resolves.
     *
     * Asyncified functions must never call other asyncified functions or
     * `import`, even indirectly, because the stack cannot be unwound twice.
     *
     * See [Emscripten's docs on Asyncify](https://emscripten.org/docs/porting/asyncify.html).
     */
    newAsyncifiedFunction(name: string, fn: AsyncFunctionImplementation): QuickJSHandle;
}
