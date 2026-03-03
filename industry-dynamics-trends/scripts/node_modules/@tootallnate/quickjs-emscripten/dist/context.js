"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.QuickJSContext = void 0;
const debug_1 = require("./debug");
const deferred_promise_1 = require("./deferred-promise");
const errors_1 = require("./errors");
const lifetime_1 = require("./lifetime");
const memory_1 = require("./memory");
const types_1 = require("./types");
/**
 * @private
 */
class ContextMemory extends memory_1.ModuleMemory {
    /** @private */
    constructor(args) {
        super(args.module);
        this.scope = new lifetime_1.Scope();
        this.copyJSValue = (ptr) => {
            return this.ffi.QTS_DupValuePointer(this.ctx.value, ptr);
        };
        this.freeJSValue = (ptr) => {
            this.ffi.QTS_FreeValuePointer(this.ctx.value, ptr);
        };
        args.ownedLifetimes?.forEach((lifetime) => this.scope.manage(lifetime));
        this.owner = args.owner;
        this.module = args.module;
        this.ffi = args.ffi;
        this.rt = args.rt;
        this.ctx = this.scope.manage(args.ctx);
    }
    get alive() {
        return this.scope.alive;
    }
    dispose() {
        return this.scope.dispose();
    }
    /**
     * Track `lifetime` so that it is disposed when this scope is disposed.
     */
    manage(lifetime) {
        return this.scope.manage(lifetime);
    }
    consumeJSCharPointer(ptr) {
        const str = this.module.UTF8ToString(ptr);
        this.ffi.QTS_FreeCString(this.ctx.value, ptr);
        return str;
    }
    heapValueHandle(ptr) {
        return new lifetime_1.Lifetime(ptr, this.copyJSValue, this.freeJSValue, this.owner);
    }
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
// TODO: Manage own callback registration
class QuickJSContext {
    /**
     * Use {@link QuickJS.createVm} to create a QuickJSContext instance.
     */
    constructor(args) {
        /** @private */
        this._undefined = undefined;
        /** @private */
        this._null = undefined;
        /** @private */
        this._false = undefined;
        /** @private */
        this._true = undefined;
        /** @private */
        this._global = undefined;
        /** @private */
        this._BigInt = undefined;
        /** @private */
        this.fnNextId = -32768; // min value of signed 16bit int used by Quickjs
        /** @private */
        this.fnMaps = new Map();
        /**
         * @hidden
         */
        this.cToHostCallbacks = {
            callFunction: (ctx, this_ptr, argc, argv, fn_id) => {
                if (ctx !== this.ctx.value) {
                    throw new Error("QuickJSContext instance received C -> JS call with mismatched ctx");
                }
                const fn = this.getFunction(fn_id);
                if (!fn) {
                    // this "throw" is not catch-able from the TS side. could we somehow handle this higher up?
                    throw new Error(`QuickJSContext had no callback with id ${fn_id}`);
                }
                return lifetime_1.Scope.withScopeMaybeAsync(this, function* (awaited, scope) {
                    const thisHandle = scope.manage(new lifetime_1.WeakLifetime(this_ptr, this.memory.copyJSValue, this.memory.freeJSValue, this.runtime));
                    const argHandles = new Array(argc);
                    for (let i = 0; i < argc; i++) {
                        const ptr = this.ffi.QTS_ArgvGetJSValueConstPointer(argv, i);
                        argHandles[i] = scope.manage(new lifetime_1.WeakLifetime(ptr, this.memory.copyJSValue, this.memory.freeJSValue, this.runtime));
                    }
                    try {
                        const result = yield* awaited(fn.apply(thisHandle, argHandles));
                        if (result) {
                            if ("error" in result && result.error) {
                                (0, debug_1.debugLog)("throw error", result.error);
                                throw result.error;
                            }
                            const handle = scope.manage(result instanceof lifetime_1.Lifetime ? result : result.value);
                            return this.ffi.QTS_DupValuePointer(this.ctx.value, handle.value);
                        }
                        return 0;
                    }
                    catch (error) {
                        return this.errorToHandle(error).consume((errorHandle) => this.ffi.QTS_Throw(this.ctx.value, errorHandle.value));
                    }
                });
            },
        };
        this.runtime = args.runtime;
        this.module = args.module;
        this.ffi = args.ffi;
        this.rt = args.rt;
        this.ctx = args.ctx;
        this.memory = new ContextMemory({
            ...args,
            owner: this.runtime,
        });
        args.callbacks.setContextCallbacks(this.ctx.value, this.cToHostCallbacks);
        this.dump = this.dump.bind(this);
        this.getString = this.getString.bind(this);
        this.getNumber = this.getNumber.bind(this);
        this.resolvePromise = this.resolvePromise.bind(this);
    }
    // @implement Disposable ----------------------------------------------------
    get alive() {
        return this.memory.alive;
    }
    /**
     * Dispose of this VM's underlying resources.
     *
     * @throws Calling this method without disposing of all created handles
     * will result in an error.
     */
    dispose() {
        this.memory.dispose();
    }
    // Globals ------------------------------------------------------------------
    /**
     * [`undefined`](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/undefined).
     */
    get undefined() {
        if (this._undefined) {
            return this._undefined;
        }
        // Undefined is a constant, immutable value in QuickJS.
        const ptr = this.ffi.QTS_GetUndefined();
        return (this._undefined = new lifetime_1.StaticLifetime(ptr));
    }
    /**
     * [`null`](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/null).
     */
    get null() {
        if (this._null) {
            return this._null;
        }
        // Null is a constant, immutable value in QuickJS.
        const ptr = this.ffi.QTS_GetNull();
        return (this._null = new lifetime_1.StaticLifetime(ptr));
    }
    /**
     * [`true`](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/true).
     */
    get true() {
        if (this._true) {
            return this._true;
        }
        // True is a constant, immutable value in QuickJS.
        const ptr = this.ffi.QTS_GetTrue();
        return (this._true = new lifetime_1.StaticLifetime(ptr));
    }
    /**
     * [`false`](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/false).
     */
    get false() {
        if (this._false) {
            return this._false;
        }
        // False is a constant, immutable value in QuickJS.
        const ptr = this.ffi.QTS_GetFalse();
        return (this._false = new lifetime_1.StaticLifetime(ptr));
    }
    /**
     * [`global`](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects).
     * A handle to the global object inside the interpreter.
     * You can set properties to create global variables.
     */
    get global() {
        if (this._global) {
            return this._global;
        }
        // The global is a JSValue, but since it's lifetime is as long as the VM's,
        // we should manage it.
        const ptr = this.ffi.QTS_GetGlobalObject(this.ctx.value);
        // Automatically clean up this reference when we dispose
        this.memory.manage(this.memory.heapValueHandle(ptr));
        // This isn't technically a static lifetime, but since it has the same
        // lifetime as the VM, it's okay to fake one since when the VM is
        // disposed, no other functions will accept the value.
        this._global = new lifetime_1.StaticLifetime(ptr, this.runtime);
        return this._global;
    }
    // New values ---------------------------------------------------------------
    /**
     * Converts a Javascript number into a QuickJS value.
     */
    newNumber(num) {
        return this.memory.heapValueHandle(this.ffi.QTS_NewFloat64(this.ctx.value, num));
    }
    /**
     * Create a QuickJS [string](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/String) value.
     */
    newString(str) {
        const ptr = this.memory
            .newHeapCharPointer(str)
            .consume((charHandle) => this.ffi.QTS_NewString(this.ctx.value, charHandle.value));
        return this.memory.heapValueHandle(ptr);
    }
    /**
     * Create a QuickJS [symbol](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Symbol) value.
     * No two symbols created with this function will be the same value.
     */
    newUniqueSymbol(description) {
        const key = (typeof description === "symbol" ? description.description : description) ?? "";
        const ptr = this.memory
            .newHeapCharPointer(key)
            .consume((charHandle) => this.ffi.QTS_NewSymbol(this.ctx.value, charHandle.value, 0));
        return this.memory.heapValueHandle(ptr);
    }
    /**
     * Get a symbol from the [global registry](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Symbol#shared_symbols_in_the_global_symbol_registry) for the given key.
     * All symbols created with the same key will be the same value.
     */
    newSymbolFor(key) {
        const description = (typeof key === "symbol" ? key.description : key) ?? "";
        const ptr = this.memory
            .newHeapCharPointer(description)
            .consume((charHandle) => this.ffi.QTS_NewSymbol(this.ctx.value, charHandle.value, 1));
        return this.memory.heapValueHandle(ptr);
    }
    /**
     * Create a QuickJS [bigint](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/BigInt) value.
     */
    newBigInt(num) {
        if (!this._BigInt) {
            const bigIntHandle = this.getProp(this.global, "BigInt");
            this.memory.manage(bigIntHandle);
            this._BigInt = new lifetime_1.StaticLifetime(bigIntHandle.value, this.runtime);
        }
        const bigIntHandle = this._BigInt;
        const asString = String(num);
        return this.newString(asString).consume((handle) => this.unwrapResult(this.callFunction(bigIntHandle, this.undefined, handle)));
    }
    /**
     * `{}`.
     * Create a new QuickJS [object](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Operators/Object_initializer).
     *
     * @param prototype - Like [`Object.create`](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Object/create).
     */
    newObject(prototype) {
        if (prototype) {
            this.runtime.assertOwned(prototype);
        }
        const ptr = prototype
            ? this.ffi.QTS_NewObjectProto(this.ctx.value, prototype.value)
            : this.ffi.QTS_NewObject(this.ctx.value);
        return this.memory.heapValueHandle(ptr);
    }
    /**
     * `[]`.
     * Create a new QuickJS [array](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Array).
     */
    newArray() {
        const ptr = this.ffi.QTS_NewArray(this.ctx.value);
        return this.memory.heapValueHandle(ptr);
    }
    newPromise(value) {
        const deferredPromise = lifetime_1.Scope.withScope((scope) => {
            const mutablePointerArray = scope.manage(this.memory.newMutablePointerArray(2));
            const promisePtr = this.ffi.QTS_NewPromiseCapability(this.ctx.value, mutablePointerArray.value.ptr);
            const promiseHandle = this.memory.heapValueHandle(promisePtr);
            const [resolveHandle, rejectHandle] = Array.from(mutablePointerArray.value.typedArray).map((jsvaluePtr) => this.memory.heapValueHandle(jsvaluePtr));
            return new deferred_promise_1.QuickJSDeferredPromise({
                context: this,
                promiseHandle,
                resolveHandle,
                rejectHandle,
            });
        });
        if (value && typeof value === "function") {
            value = new Promise(value);
        }
        if (value) {
            Promise.resolve(value).then(deferredPromise.resolve, (error) => error instanceof lifetime_1.Lifetime
                ? deferredPromise.reject(error)
                : this.newError(error).consume(deferredPromise.reject));
        }
        return deferredPromise;
    }
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
    newFunction(name, fn) {
        const fnId = ++this.fnNextId;
        this.setFunction(fnId, fn);
        return this.memory.heapValueHandle(this.ffi.QTS_NewFunction(this.ctx.value, fnId, name));
    }
    newError(error) {
        const errorHandle = this.memory.heapValueHandle(this.ffi.QTS_NewError(this.ctx.value));
        if (error && typeof error === "object") {
            if (error.name !== undefined) {
                this.newString(error.name).consume((handle) => this.setProp(errorHandle, "name", handle));
            }
            if (error.message !== undefined) {
                this.newString(error.message).consume((handle) => this.setProp(errorHandle, "message", handle));
            }
        }
        else if (typeof error === "string") {
            this.newString(error).consume((handle) => this.setProp(errorHandle, "message", handle));
        }
        else if (error !== undefined) {
            // This isn't supported in the type signature but maybe it will make life easier.
            this.newString(String(error)).consume((handle) => this.setProp(errorHandle, "message", handle));
        }
        return errorHandle;
    }
    // Read values --------------------------------------------------------------
    /**
     * `typeof` operator. **Not** [standards compliant](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Operators/typeof).
     *
     * @remarks
     * Does not support BigInt values correctly.
     */
    typeof(handle) {
        this.runtime.assertOwned(handle);
        return this.memory.consumeHeapCharPointer(this.ffi.QTS_Typeof(this.ctx.value, handle.value));
    }
    /**
     * Converts `handle` into a Javascript number.
     * @returns `NaN` on error, otherwise a `number`.
     */
    getNumber(handle) {
        this.runtime.assertOwned(handle);
        return this.ffi.QTS_GetFloat64(this.ctx.value, handle.value);
    }
    /**
     * Converts `handle` to a Javascript string.
     */
    getString(handle) {
        this.runtime.assertOwned(handle);
        return this.memory.consumeJSCharPointer(this.ffi.QTS_GetString(this.ctx.value, handle.value));
    }
    /**
     * Converts `handle` into a Javascript symbol. If the symbol is in the global
     * registry in the guest, it will be created with Symbol.for on the host.
     */
    getSymbol(handle) {
        this.runtime.assertOwned(handle);
        const key = this.memory.consumeJSCharPointer(this.ffi.QTS_GetSymbolDescriptionOrKey(this.ctx.value, handle.value));
        const isGlobal = this.ffi.QTS_IsGlobalSymbol(this.ctx.value, handle.value);
        return isGlobal ? Symbol.for(key) : Symbol(key);
    }
    /**
     * Converts `handle` to a Javascript bigint.
     */
    getBigInt(handle) {
        this.runtime.assertOwned(handle);
        const asString = this.getString(handle);
        return BigInt(asString);
    }
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
    resolvePromise(promiseLikeHandle) {
        this.runtime.assertOwned(promiseLikeHandle);
        const vmResolveResult = lifetime_1.Scope.withScope((scope) => {
            const vmPromise = scope.manage(this.getProp(this.global, "Promise"));
            const vmPromiseResolve = scope.manage(this.getProp(vmPromise, "resolve"));
            return this.callFunction(vmPromiseResolve, vmPromise, promiseLikeHandle);
        });
        if (vmResolveResult.error) {
            return Promise.resolve(vmResolveResult);
        }
        return new Promise((resolve) => {
            lifetime_1.Scope.withScope((scope) => {
                const resolveHandle = scope.manage(this.newFunction("resolve", (value) => {
                    resolve({ value: value && value.dup() });
                }));
                const rejectHandle = scope.manage(this.newFunction("reject", (error) => {
                    resolve({ error: error && error.dup() });
                }));
                const promiseHandle = scope.manage(vmResolveResult.value);
                const promiseThenHandle = scope.manage(this.getProp(promiseHandle, "then"));
                this.unwrapResult(this.callFunction(promiseThenHandle, promiseHandle, resolveHandle, rejectHandle)).dispose();
            });
        });
    }
    // Properties ---------------------------------------------------------------
    /**
     * `handle[key]`.
     * Get a property from a JSValue.
     *
     * @param key - The property may be specified as a JSValue handle, or as a
     * Javascript string (which will be converted automatically).
     */
    getProp(handle, key) {
        this.runtime.assertOwned(handle);
        const ptr = this.borrowPropertyKey(key).consume((quickJSKey) => this.ffi.QTS_GetProp(this.ctx.value, handle.value, quickJSKey.value));
        const result = this.memory.heapValueHandle(ptr);
        return result;
    }
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
    setProp(handle, key, value) {
        this.runtime.assertOwned(handle);
        // free newly allocated value if key was a string or number. No-op if string was already
        // a QuickJS handle.
        this.borrowPropertyKey(key).consume((quickJSKey) => this.ffi.QTS_SetProp(this.ctx.value, handle.value, quickJSKey.value, value.value));
    }
    /**
     * [`Object.defineProperty(handle, key, descriptor)`](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Object/defineProperty).
     *
     * @param key - The property may be specified as a JSValue handle, or as a
     * Javascript string or number (which will be converted automatically to a JSValue).
     */
    defineProp(handle, key, descriptor) {
        this.runtime.assertOwned(handle);
        lifetime_1.Scope.withScope((scope) => {
            const quickJSKey = scope.manage(this.borrowPropertyKey(key));
            const value = descriptor.value || this.undefined;
            const configurable = Boolean(descriptor.configurable);
            const enumerable = Boolean(descriptor.enumerable);
            const hasValue = Boolean(descriptor.value);
            const get = descriptor.get
                ? scope.manage(this.newFunction(descriptor.get.name, descriptor.get))
                : this.undefined;
            const set = descriptor.set
                ? scope.manage(this.newFunction(descriptor.set.name, descriptor.set))
                : this.undefined;
            this.ffi.QTS_DefineProp(this.ctx.value, handle.value, quickJSKey.value, value.value, get.value, set.value, configurable, enumerable, hasValue);
        });
    }
    // Evaluation ---------------------------------------------------------------
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
    callFunction(func, thisVal, ...args) {
        this.runtime.assertOwned(func);
        const resultPtr = this.memory
            .toPointerArray(args)
            .consume((argsArrayPtr) => this.ffi.QTS_Call(this.ctx.value, func.value, thisVal.value, args.length, argsArrayPtr.value));
        const errorPtr = this.ffi.QTS_ResolveException(this.ctx.value, resultPtr);
        if (errorPtr) {
            this.ffi.QTS_FreeValuePointer(this.ctx.value, resultPtr);
            return { error: this.memory.heapValueHandle(errorPtr) };
        }
        return { value: this.memory.heapValueHandle(resultPtr) };
    }
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
    evalCode(code, filename = "eval.js", 
    /**
     * If no options are passed, a heuristic will be used to detect if `code` is
     * an ES module.
     *
     * See [[EvalFlags]] for number semantics.
     */
    options) {
        const detectModule = (options === undefined ? 1 : 0);
        const flags = (0, types_1.evalOptionsToFlags)(options);
        const resultPtr = this.memory
            .newHeapCharPointer(code)
            .consume((charHandle) => this.ffi.QTS_Eval(this.ctx.value, charHandle.value, filename, detectModule, flags));
        const errorPtr = this.ffi.QTS_ResolveException(this.ctx.value, resultPtr);
        if (errorPtr) {
            this.ffi.QTS_FreeValuePointer(this.ctx.value, resultPtr);
            return { error: this.memory.heapValueHandle(errorPtr) };
        }
        return { value: this.memory.heapValueHandle(resultPtr) };
    }
    /**
     * Throw an error in the VM, interrupted whatever current execution is in progress when execution resumes.
     * @experimental
     */
    throw(error) {
        return this.errorToHandle(error).consume((handle) => this.ffi.QTS_Throw(this.ctx.value, handle.value));
    }
    /**
     * @private
     */
    borrowPropertyKey(key) {
        if (typeof key === "number") {
            return this.newNumber(key);
        }
        if (typeof key === "string") {
            return this.newString(key);
        }
        // key is already a JSValue, but we're borrowing it. Return a static handle
        // for internal use only.
        return new lifetime_1.StaticLifetime(key.value, this.runtime);
    }
    /**
     * @private
     */
    getMemory(rt) {
        if (rt === this.rt.value) {
            return this.memory;
        }
        else {
            throw new Error("Private API. Cannot get memory from a different runtime");
        }
    }
    // Utilities ----------------------------------------------------------------
    /**
     * Dump a JSValue to Javascript in a best-effort fashion.
     * Returns `handle.toString()` if it cannot be serialized to JSON.
     */
    dump(handle) {
        this.runtime.assertOwned(handle);
        const type = this.typeof(handle);
        if (type === "string") {
            return this.getString(handle);
        }
        else if (type === "number") {
            return this.getNumber(handle);
        }
        else if (type === "bigint") {
            return this.getBigInt(handle);
        }
        else if (type === "undefined") {
            return undefined;
        }
        else if (type === "symbol") {
            return this.getSymbol(handle);
        }
        const str = this.memory.consumeJSCharPointer(this.ffi.QTS_Dump(this.ctx.value, handle.value));
        try {
            return JSON.parse(str);
        }
        catch (err) {
            return str;
        }
    }
    /**
     * Unwrap a SuccessOrFail result such as a [[VmCallResult]] or a
     * [[ExecutePendingJobsResult]], where the fail branch contains a handle to a QuickJS error value.
     * If the result is a success, returns the value.
     * If the result is an error, converts the error to a native object and throws the error.
     */
    unwrapResult(result) {
        if (result.error) {
            const context = "context" in result.error ? result.error.context : this;
            const cause = result.error.consume((error) => this.dump(error));
            if (cause && typeof cause === "object" && typeof cause.message === "string") {
                const { message, name, stack } = cause;
                const exception = new errors_1.QuickJSUnwrapError("");
                const hostStack = exception.stack;
                if (typeof name === "string") {
                    exception.name = cause.name;
                }
                if (typeof stack === "string") {
                    exception.stack = `${name}: ${message}\n${cause.stack}Host: ${hostStack}`;
                }
                Object.assign(exception, { cause, context, message });
                throw exception;
            }
            throw new errors_1.QuickJSUnwrapError(cause, context);
        }
        return result.value;
    }
    /** @private */
    getFunction(fn_id) {
        const map_id = fn_id >> 8;
        const fnMap = this.fnMaps.get(map_id);
        if (!fnMap) {
            return undefined;
        }
        return fnMap.get(fn_id);
    }
    /** @private */
    setFunction(fn_id, handle) {
        const map_id = fn_id >> 8;
        let fnMap = this.fnMaps.get(map_id);
        if (!fnMap) {
            fnMap = new Map();
            this.fnMaps.set(map_id, fnMap);
        }
        return fnMap.set(fn_id, handle);
    }
    errorToHandle(error) {
        if (error instanceof lifetime_1.Lifetime) {
            return error;
        }
        return this.newError(error);
    }
}
exports.QuickJSContext = QuickJSContext;
//# sourceMappingURL=context.js.map