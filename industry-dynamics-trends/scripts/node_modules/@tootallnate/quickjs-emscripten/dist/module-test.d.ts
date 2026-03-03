import type { QuickJSContext } from "./context";
import type { ModuleEvalOptions, QuickJSWASMModule } from "./module";
import type { QuickJSRuntime } from "./runtime";
import type { ContextOptions, RuntimeOptions } from "./types";
/**
 * A test wrapper of [[QuickJSWASMModule]] that keeps a reference to each
 * context or runtime created.
 *
 * Call [[disposeAll]] to reset these sets and calls `dispose` on any left alive
 * (which may throw an error).
 *
 * Call [[assertNoMemoryAllocated]] at the end of a test, when you expect that you've
 * freed all the memory you've ever allocated.
 */
export declare class TestQuickJSWASMModule implements Pick<QuickJSWASMModule, keyof QuickJSWASMModule> {
    private parent;
    contexts: Set<QuickJSContext>;
    runtimes: Set<QuickJSRuntime>;
    constructor(parent: QuickJSWASMModule);
    newRuntime(options?: RuntimeOptions): QuickJSRuntime;
    newContext(options?: ContextOptions): QuickJSContext;
    evalCode(code: string, options?: ModuleEvalOptions): unknown;
    disposeAll(): void;
    assertNoMemoryAllocated(): void;
    /** @private */
    getFFI(): any;
}
