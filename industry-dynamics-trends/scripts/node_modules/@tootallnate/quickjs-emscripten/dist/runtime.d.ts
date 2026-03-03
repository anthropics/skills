import { QuickJSContext } from "./context";
import { EitherModule } from "./emscripten-types";
import { JSContextPointer, JSRuntimePointer } from "./types-ffi";
import { Disposable, Lifetime, Scope } from "./lifetime";
import { ModuleMemory } from "./memory";
import { QuickJSModuleCallbacks } from "./module";
import { ContextOptions, EitherFFI, JSModuleLoader, JSModuleNormalizer, QuickJSHandle } from "./types";
import { SuccessOrFail } from "./vm-interface";
/**
 * Callback called regularly while the VM executes code.
 * Determines if a VM's execution should be interrupted.
 *
 * @returns `true` to interrupt JS execution inside the VM.
 * @returns `false` or `undefined` to continue JS execution inside the VM.
 */
export type InterruptHandler = (runtime: QuickJSRuntime) => boolean | undefined;
/**
 * Used as an optional for the results of executing pendingJobs.
 * On success, `value` contains the number of async jobs executed
 * by the runtime.
 * @source
 */
export type ExecutePendingJobsResult = SuccessOrFail<
/** Number of jobs successfully executed. */
number, 
/** The error that occurred. */
QuickJSHandle & {
    /** The context where the error occurred. */
    context: QuickJSContext;
}>;
/**
 * A runtime represents a Javascript runtime corresponding to an object heap.
 * Several runtimes can exist at the same time but they cannot exchange objects.
 * Inside a given runtime, no multi-threading is supported.
 *
 * You can think of separate runtimes like different domains in a browser, and
 * the contexts within a runtime like the different windows open to the same
 * domain.
 *
 * Create a runtime via {@link QuickJSWASMModule.newRuntime}.
 *
 * You should create separate runtime instances for untrusted code from
 * different sources for isolation. However, stronger isolation is also
 * available (at the cost of memory usage), by creating separate WebAssembly
 * modules to further isolate untrusted code.
 * See {@link newQuickJSWASMModule}.
 *
 * Implement memory and CPU constraints with [[setInterruptHandler]]
 * (called regularly while the interpreter runs), [[setMemoryLimit]], and
 * [[setMaxStackSize]].
 * Use [[computeMemoryUsage]] or [[dumpMemoryUsage]] to guide memory limit
 * tuning.
 *
 * Configure ES module loading with [[setModuleLoader]].
 */
export declare class QuickJSRuntime implements Disposable {
    /**
     * If this runtime was created as as part of a context, points to the context
     * associated with the runtime.
     *
     * If this runtime was created stand-alone, this may or may not contain a context.
     * A context here may be allocated if one is needed by the runtime, eg for [[computeMemoryUsage]].
     */
    context: QuickJSContext | undefined;
    /** @private */
    protected module: EitherModule;
    /** @private */
    protected memory: ModuleMemory;
    /** @private */
    protected ffi: EitherFFI;
    /** @private */
    protected rt: Lifetime<JSRuntimePointer>;
    /** @private */
    protected callbacks: QuickJSModuleCallbacks;
    /** @private */
    protected scope: Scope;
    /** @private */
    protected contextMap: Map<JSContextPointer, QuickJSContext>;
    /** @private */
    protected moduleLoader: JSModuleLoader | undefined;
    /** @private */
    protected moduleNormalizer: JSModuleNormalizer | undefined;
    /** @private */
    constructor(args: {
        module: EitherModule;
        ffi: EitherFFI;
        rt: Lifetime<JSRuntimePointer>;
        callbacks: QuickJSModuleCallbacks;
        ownedLifetimes?: Disposable[];
    });
    get alive(): boolean;
    dispose(): void;
    newContext(options?: ContextOptions): QuickJSContext;
    /**
     * Set the loader for EcmaScript modules requested by any context in this
     * runtime.
     *
     * The loader can be removed with [[removeModuleLoader]].
     */
    setModuleLoader(moduleLoader: JSModuleLoader, moduleNormalizer?: JSModuleNormalizer): void;
    /**
     * Remove the the loader set by [[setModuleLoader]]. This disables module loading.
     */
    removeModuleLoader(): void;
    /**
     * In QuickJS, promises and async functions create pendingJobs. These do not execute
     * immediately and need to be run by calling [[executePendingJobs]].
     *
     * @return true if there is at least one pendingJob queued up.
     */
    hasPendingJob(): boolean;
    private interruptHandler;
    /**
     * Set a callback which is regularly called by the QuickJS engine when it is
     * executing code. This callback can be used to implement an execution
     * timeout.
     *
     * The interrupt handler can be removed with [[removeInterruptHandler]].
     */
    setInterruptHandler(cb: InterruptHandler): void;
    /**
     * Remove the interrupt handler, if any.
     * See [[setInterruptHandler]].
     */
    removeInterruptHandler(): void;
    /**
     * Execute pendingJobs on the runtime until `maxJobsToExecute` jobs are
     * executed (default all pendingJobs), the queue is exhausted, or the runtime
     * encounters an exception.
     *
     * In QuickJS, promises and async functions *inside the runtime* create
     * pendingJobs. These do not execute immediately and need to triggered to run.
     *
     * @param maxJobsToExecute - When negative, run all pending jobs. Otherwise execute
     * at most `maxJobsToExecute` before returning.
     *
     * @return On success, the number of executed jobs. On error, the exception
     * that stopped execution, and the context it occurred in. Note that
     * executePendingJobs will not normally return errors thrown inside async
     * functions or rejected promises. Those errors are available by calling
     * [[resolvePromise]] on the promise handle returned by the async function.
     */
    executePendingJobs(maxJobsToExecute?: number | void): ExecutePendingJobsResult;
    /**
     * Set the max memory this runtime can allocate.
     * To remove the limit, set to `-1`.
     */
    setMemoryLimit(limitBytes: number): void;
    /**
     * Compute memory usage for this runtime. Returns the result as a handle to a
     * JSValue object. Use [[QuickJSContext.dump]] to convert to a native object.
     * Calling this method will allocate more memory inside the runtime. The information
     * is accurate as of just before the call to `computeMemoryUsage`.
     * For a human-digestible representation, see [[dumpMemoryUsage]].
     */
    computeMemoryUsage(): QuickJSHandle;
    /**
     * @returns a human-readable description of memory usage in this runtime.
     * For programmatic access to this information, see [[computeMemoryUsage]].
     */
    dumpMemoryUsage(): string;
    /**
     * Set the max stack size for this runtime, in bytes.
     * To remove the limit, set to `0`.
     */
    setMaxStackSize(stackSize: number): void;
    /**
     * Assert that `handle` is owned by this runtime.
     * @throws QuickJSWrongOwner if owned by a different runtime.
     */
    assertOwned(handle: QuickJSHandle): void;
    private getSystemContext;
    private cToHostCallbacks;
}
