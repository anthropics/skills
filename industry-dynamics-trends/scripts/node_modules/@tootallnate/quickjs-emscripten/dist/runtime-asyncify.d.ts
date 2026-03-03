import { Lifetime } from ".";
import { QuickJSAsyncContext } from "./context-asyncify";
import { QuickJSAsyncEmscriptenModule } from "./emscripten-types";
import { QuickJSAsyncFFI } from "./variants";
import { JSContextPointer, JSRuntimePointer } from "./types-ffi";
import { QuickJSModuleCallbacks } from "./module";
import { QuickJSRuntime } from "./runtime";
import { ContextOptions, JSModuleLoaderAsync, JSModuleNormalizerAsync } from "./types";
export declare class QuickJSAsyncRuntime extends QuickJSRuntime {
    context: QuickJSAsyncContext | undefined;
    /** @private */
    protected module: QuickJSAsyncEmscriptenModule;
    /** @private */
    protected ffi: QuickJSAsyncFFI;
    /** @private */
    protected rt: Lifetime<JSRuntimePointer>;
    /** @private */
    protected callbacks: QuickJSModuleCallbacks;
    /** @private */
    protected contextMap: Map<JSContextPointer, QuickJSAsyncContext>;
    /** @private */
    constructor(args: {
        module: QuickJSAsyncEmscriptenModule;
        ffi: QuickJSAsyncFFI;
        rt: Lifetime<JSRuntimePointer>;
        callbacks: QuickJSModuleCallbacks;
    });
    newContext(options?: ContextOptions): QuickJSAsyncContext;
    setModuleLoader(moduleLoader: JSModuleLoaderAsync, moduleNormalizer?: JSModuleNormalizerAsync): void;
    /**
     * Set the max stack size for this runtime in bytes.
     * To remove the limit, set to `0`.
     *
     * Setting this limit also adjusts the global `ASYNCIFY_STACK_SIZE` for the entire {@link QuickJSAsyncWASMModule}.
     * See the [pull request](https://github.com/justjake/quickjs-emscripten/pull/114) for more details.
     */
    setMaxStackSize(stackSize: number): void;
}
