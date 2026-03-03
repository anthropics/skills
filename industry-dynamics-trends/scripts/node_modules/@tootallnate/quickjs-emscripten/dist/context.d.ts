import { QuickJSDeferredPromise } from "./deferred-promise";
import type { EitherModule } from "./emscripten-types";
import { JSBorrowedCharPointer, JSContextPointer, JSRuntimePointer, JSValueConstPointer, JSValuePointer } from "./types-ffi";
import { Disposable, Lifetime, Scope } from "./lifetime";
import { ModuleMemory } from "./memory";
import { QuickJSModuleCallbacks } from "./module";
import { QuickJSRuntime } from "./runtime";
import { ContextEvalOptions, EitherFFI, JSValue, PromiseExecutor, QuickJSHandle } from "./types";
import { LowLevelJavascriptVm, SuccessOrFail, VmCallResult, VmFunctionImplementation, VmPropertyDescriptor } from "./vm-interface";
/**
 * Property key for getting or setting a property on a handle with
 * [[QuickJSContext.getProp]], [[QuickJSContext.setProp]], or [[QuickJSContext.defineProp]].
 */
export type QuickJSPropertyKey = number | string | QuickJSHandle;
/**
 * @private
 */
declare class ContextMemory extends ModuleMemory implements Disposable {
    readonly owner: QuickJSRuntime;
    readonly ctx: Lifetime<JSContextPointer>;
    readonly rt: Lifetime<JSRuntimePointer>;
    readonly module: EitherModule;
    readonly ffi: EitherFFI;
    readonly scope: Scope;
    /** @private */
    constructor(args: {
        owner: QuickJSRuntime;
        module: EitherModule;
        ffi: EitherFFI;
        ctx: Lifetime<JSContextPointer>;
        rt: Lifetime<JSRuntimePointer>;
        ownedLifetimes?: Disposable[];
    });
    get alive(): boolean;
    dispose(): void;
    /**
     * Track `lifetime` so that it is disposed when this scope is disposed.
     */
    manage<T extends Disposable>(lifetime: T): T;
    copyJSValue: (ptr: JSValuePointer | JSValueConstPointer) => any;
    freeJSValue: (ptr: JSValuePointer) => void;
    consumeJSCharPointer(ptr: JSBorrowedCharPointer): string;
    heapValueHandle(ptr: JSValuePointer): JSValue;
}
/**
 * QuickJSContext wraps a QuickJS Javascript context (JSContext*) within a
 * runtime. The contexts within the same runtime may exchange objects freely.
 * You can think of separate runtimes like different domains in a browser, and
 * the contexts within a runtime like the different windows open to the same
 * domain. The {@link runtime} references the context's runtime.
 *
 * This class's methods return {@link QuickJSHandle}, which wrap C pointers (JSValue*).
 * It's the caller's responsibility to call `.dispose()` on any
 * handles you create to free memory once you're done with the handle.
 *
 * Use {@link QuickJSRuntime.newContext} or {@link QuickJSWASMModule.newContext}
 * to create a new QuickJSContext.
 *
 * Create QuickJS values inside the interpreter with methods like
 * [[newNumber]], [[newString]], [[newArray]], [[newObject]],
 * [[newFunction]], and [[newPromise]].
 *
 * Call [[setProp]] or [[defineProp]] to customize objects. Use those methods
 * with [[global]] to expose the values you create to the interior of the
 * interpreter, so they can be used in [[evalCode]].
 *
 * Use [[evalCode]] or [[callFunction]] to execute Javascript inside the VM. If
 * you're using asynchronous code inside the QuickJSContext, you may need to also
 * call [[executePendingJobs]]. Executing code inside the runtime returns a
 * result object representing successful execution or an error. You must dispose
 * of any such results to avoid leaking memory inside the VM.
 *
 * Implement memory and CPU constraints at the runtime level, using [[runtime]].
 * See {@link QuickJSRuntime} for more information.
 *
 */
export declare class QuickJSContext implements LowLevelJavascriptVm<QuickJSHandle>, Disposable {
    /**
     * The runtime that created this context.
     */
    readonly runtime: QuickJSRuntime;
    /** @private */
    protected readonly ctx: Lifetime<JSContextPointer>;
    /** @private */
    protected readonly rt: Lifetime<JSRuntimePointer>;
    /** @private */
    protected readonly module: EitherModule;
    /** @private */
    protected readonly ffi: EitherFFI;
    /** @private */
    protected memory: ContextMemory;
    /** @private */
    protected _undefined: QuickJSHandle | undefined;
    /** @private */
    protected _null: QuickJSHandle | undefined;
    /** @private */
    protected _false: QuickJSHandle | undefined;
    /** @private */
    protected _true: QuickJSHandle | undefined;
    /** @private */
    protected _global: QuickJSHandle | undefined;
    /** @private */
    protected _BigInt: QuickJSHandle | undefined;
    /**
     * Use {@link QuickJS.createVm} to create a QuickJSContext instance.
     */
    constructor(args: {
        module: EitherModule;
        ffi: EitherFFI;
        ctx: Lifetime<JSContextPointer>;
        rt: Lifetime<JSRuntimePointer>;
        runtime: QuickJSRuntime;
        ownedLifetimes?: Disposable[];
        callbacks: QuickJSModuleCallbacks;
    });
    get alive(): boolean;
    /**
     * Dispose of this VM's underlying resources.
     *
     * @throws Calling this method without disposing of all created handles
     * will result in an error.
     */
    dispose(): void;
    /**
     * [`undefined`](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/undefined).
     */
    get undefined(): QuickJSHandle;
    /**
     * [`null`](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/null).
     */
    get null(): QuickJSHandle;
    /**
     * [`true`](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/true).
     */
    get true(): QuickJSHandle;
    /**
     * [`false`](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/false).
     */
    get false(): QuickJSHandle;
    /**
     * [`global`](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects).
     * A handle to the global object inside the interpreter.
     * You can set properties to create global variables.
     */
    get global(): QuickJSHandle;
    /**
     * Converts a Javascript number into a QuickJS value.
     */
    newNumber(num: number): QuickJSHandle;
    /**
     * Create a QuickJS [string](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/String) value.
     */
    newString(str: string): QuickJSHandle;
    /**
     * Create a QuickJS [symbol](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Symbol) value.
     * No two symbols created with this function will be the same value.
     */
    newUniqueSymbol(description: string | symbol): QuickJSHandle;
    /**
     * Get a symbol from the [global registry](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Symbol#shared_symbols_in_the_global_symbol_registry) for the given key.
     * All symbols created with the same key will be the same value.
     */
    newSymbolFor(key: string | symbol): QuickJSHandle;
    /**
     * Create a QuickJS [bigint](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/BigInt) value.
     */
    newBigInt(num: bigint): QuickJSHandle;
    /**
     * `{}`.
     * Create a new QuickJS [object](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Operators/Object_initializer).
     *
     * @param prototype - Like [`Object.create`](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Object/create).
     */
    newObject(prototype?: QuickJSHandle): QuickJSHandle;
    /**
     * `[]`.
     * Create a new QuickJS [array](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Array).
     */
    newArray(): QuickJSHandle;
    /**
     * Create a new [[QuickJSDeferredPromise]]. Use `deferred.resolve(handle)` and
     * `deferred.reject(handle)` to fulfill the promise handle available at `deferred.handle`.
     * Note that you are responsible for calling `deferred.dispose()` to free the underlying
     * resources; see the documentation on [[QuickJSDeferredPromise]] for details.
     */
    newPromise(): QuickJSDeferredPromise;
    /**
     * Create a new [[QuickJSDeferredPromise]] that resolves when the
     * given native Promise<QuickJSHandle> resolves. Rejections will be coerced
     * to a QuickJS error.
     *
     * You can still resolve/reject the created promise "early" using its methods.
     */
    newPromise(promise: Promise<QuickJSHandle>): QuickJSDeferredPromise;
    /**
     * Construct a new native Promise<QuickJSHandle>, and then convert it into a
     * [[QuickJSDeferredPromise]].
     *
     * You can still resolve/reject the created promise "early" using its methods.
     */
    newPromise(newPromiseFn: PromiseExecutor<QuickJSHandle, Error | QuickJSHandle>): QuickJSDeferredPromise;
    /**
     * Convert a Javascript function into a QuickJS function value.
     * See [[VmFunctionImplementation]] for more details.
     *
     * A [[VmFunctionImplementation]] should not free its arguments or its return
     * value. A VmFunctionImplementation should also not retain any references to
     * its return value.
     *
     * To implement an async function, create a promise with [[newPromise]], then
     * return the deferred promise handle from `deferred.handle` from your
     * function implementation:
     *
     * ```
     * const deferred = vm.newPromise()
     * someNativeAsyncFunction().then(deferred.resolve)
     * return deferred.handle
     * ```
     */
    newFunction(name: string, fn: VmFunctionImplementation<QuickJSHandle>): QuickJSHandle;
    newError(error: {
        name: string;
        message: string;
    }): QuickJSHandle;
    newError(message: string): QuickJSHandle;
    newError(): QuickJSHandle;
    /**
     * `typeof` operator. **Not** [standards compliant](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Operators/typeof).
     *
     * @remarks
     * Does not support BigInt values correctly.
     */
    typeof(handle: QuickJSHandle): string;
    /**
     * Converts `handle` into a Javascript number.
     * @returns `NaN` on error, otherwise a `number`.
     */
    getNumber(handle: QuickJSHandle): number;
    /**
     * Converts `handle` to a Javascript string.
     */
    getString(handle: QuickJSHandle): string;
    /**
     * Converts `handle` into a Javascript symbol. If the symbol is in the global
     * registry in the guest, it will be created with Symbol.for on the host.
     */
    getSymbol(handle: QuickJSHandle): symbol;
    /**
     * Converts `handle` to a Javascript bigint.
     */
    getBigInt(handle: QuickJSHandle): bigint;
    /**
     * `Promise.resolve(value)`.
     * Convert a handle containing a Promise-like value inside the VM into an
     * actual promise on the host.
     *
     * @remarks
     * You may need to call [[executePendingJobs]] to ensure that the promise is resolved.
     *
     * @param promiseLikeHandle - A handle to a Promise-like value with a `.then(onSuccess, onError)` method.
     */
    resolvePromise(promiseLikeHandle: QuickJSHandle): Promise<VmCallResult<QuickJSHandle>>;
    /**
     * `handle[key]`.
     * Get a property from a JSValue.
     *
     * @param key - The property may be specified as a JSValue handle, or as a
     * Javascript string (which will be converted automatically).
     */
    getProp(handle: QuickJSHandle, key: QuickJSPropertyKey): QuickJSHandle;
    /**
     * `handle[key] = value`.
     * Set a property on a JSValue.
     *
     * @remarks
     * Note that the QuickJS authors recommend using [[defineProp]] to define new
     * properties.
     *
     * @param key - The property may be specified as a JSValue handle, or as a
     * Javascript string or number (which will be converted automatically to a JSValue).
     */
    setProp(handle: QuickJSHandle, key: QuickJSPropertyKey, value: QuickJSHandle): void;
    /**
     * [`Object.defineProperty(handle, key, descriptor)`](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Object/defineProperty).
     *
     * @param key - The property may be specified as a JSValue handle, or as a
     * Javascript string or number (which will be converted automatically to a JSValue).
     */
    defineProp(handle: QuickJSHandle, key: QuickJSPropertyKey, descriptor: VmPropertyDescriptor<QuickJSHandle>): void;
    /**
     * [`func.call(thisVal, ...args)`](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Function/call).
     * Call a JSValue as a function.
     *
     * See [[unwrapResult]], which will throw if the function returned an error, or
     * return the result handle directly. If evaluation returned a handle containing
     * a promise, use [[resolvePromise]] to convert it to a native promise and
     * [[executePendingJobs]] to finish evaluating the promise.
     *
     * @returns A result. If the function threw synchronously, `result.error` be a
     * handle to the exception. Otherwise `result.value` will be a handle to the
     * value.
     */
    callFunction(func: QuickJSHandle, thisVal: QuickJSHandle, ...args: QuickJSHandle[]): VmCallResult<QuickJSHandle>;
    /**
     * Like [`eval(code)`](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/eval#Description).
     * Evaluates the Javascript source `code` in the global scope of this VM.
     * When working with async code, you many need to call [[executePendingJobs]]
     * to execute callbacks pending after synchronous evaluation returns.
     *
     * See [[unwrapResult]], which will throw if the function returned an error, or
     * return the result handle directly. If evaluation returned a handle containing
     * a promise, use [[resolvePromise]] to convert it to a native promise and
     * [[executePendingJobs]] to finish evaluating the promise.
     *
     * *Note*: to protect against infinite loops, provide an interrupt handler to
     * [[setInterruptHandler]]. You can use [[shouldInterruptAfterDeadline]] to
     * create a time-based deadline.
     *
     * @returns The last statement's value. If the code threw synchronously,
     * `result.error` will be a handle to the exception. If execution was
     * interrupted, the error will have name `InternalError` and message
     * `interrupted`.
     */
    evalCode(code: string, filename?: string, 
    /**
     * If no options are passed, a heuristic will be used to detect if `code` is
     * an ES module.
     *
     * See [[EvalFlags]] for number semantics.
     */
    options?: number | ContextEvalOptions): VmCallResult<QuickJSHandle>;
    /**
     * Throw an error in the VM, interrupted whatever current execution is in progress when execution resumes.
     * @experimental
     */
    throw(error: Error | QuickJSHandle): any;
    /**
     * @private
     */
    protected borrowPropertyKey(key: QuickJSPropertyKey): QuickJSHandle;
    /**
     * @private
     */
    getMemory(rt: JSRuntimePointer): ContextMemory;
    /**
     * Dump a JSValue to Javascript in a best-effort fashion.
     * Returns `handle.toString()` if it cannot be serialized to JSON.
     */
    dump(handle: QuickJSHandle): any;
    /**
     * Unwrap a SuccessOrFail result such as a [[VmCallResult]] or a
     * [[ExecutePendingJobsResult]], where the fail branch contains a handle to a QuickJS error value.
     * If the result is a success, returns the value.
     * If the result is an error, converts the error to a native object and throws the error.
     */
    unwrapResult<T>(result: SuccessOrFail<T, QuickJSHandle>): T;
    /** @private */
    protected fnNextId: number;
    /** @private */
    protected fnMaps: Map<number, Map<number, VmFunctionImplementation<QuickJSHandle>>>;
    /** @private */
    protected getFunction(fn_id: number): VmFunctionImplementation<QuickJSHandle> | undefined;
    /** @private */
    protected setFunction(fn_id: number, handle: VmFunctionImplementation<QuickJSHandle>): Map<number, VmFunctionImplementation<QuickJSHandle>>;
    /**
     * @hidden
     */
    private cToHostCallbacks;
    private errorToHandle;
}
export {};
