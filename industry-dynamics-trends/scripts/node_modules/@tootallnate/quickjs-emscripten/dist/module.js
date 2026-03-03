"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.QuickJSWASMModule = exports.applyModuleEvalRuntimeOptions = exports.applyBaseRuntimeOptions = exports.QuickJSModuleCallbacks = void 0;
const debug_1 = require("./debug");
const errors_1 = require("./errors");
const lifetime_1 = require("./lifetime");
const runtime_1 = require("./runtime");
const types_1 = require("./types");
class QuickJSEmscriptenModuleCallbacks {
    constructor(args) {
        this.callFunction = args.callFunction;
        this.shouldInterrupt = args.shouldInterrupt;
        this.loadModuleSource = args.loadModuleSource;
        this.normalizeModule = args.normalizeModule;
    }
}
/**
 * We use static functions per module to dispatch runtime or context calls from
 * C to the host.  This class manages the indirection from a specific runtime or
 * context pointer to the appropriate callback handler.
 *
 * @private
 */
class QuickJSModuleCallbacks {
    constructor(module) {
        this.contextCallbacks = new Map();
        this.runtimeCallbacks = new Map();
        this.suspendedCount = 0;
        this.cToHostCallbacks = new QuickJSEmscriptenModuleCallbacks({
            callFunction: (asyncify, ctx, this_ptr, argc, argv, fn_id) => this.handleAsyncify(asyncify, () => {
                try {
                    const vm = this.contextCallbacks.get(ctx);
                    if (!vm) {
                        throw new Error(`QuickJSContext(ctx = ${ctx}) not found for C function call "${fn_id}"`);
                    }
                    return vm.callFunction(ctx, this_ptr, argc, argv, fn_id);
                }
                catch (error) {
                    console.error("[C to host error: returning null]", error);
                    return 0;
                }
            }),
            shouldInterrupt: (asyncify, rt) => this.handleAsyncify(asyncify, () => {
                try {
                    const vm = this.runtimeCallbacks.get(rt);
                    if (!vm) {
                        throw new Error(`QuickJSRuntime(rt = ${rt}) not found for C interrupt`);
                    }
                    return vm.shouldInterrupt(rt);
                }
                catch (error) {
                    console.error("[C to host interrupt: returning error]", error);
                    return 1;
                }
            }),
            loadModuleSource: (asyncify, rt, ctx, moduleName) => this.handleAsyncify(asyncify, () => {
                try {
                    const runtimeCallbacks = this.runtimeCallbacks.get(rt);
                    if (!runtimeCallbacks) {
                        throw new Error(`QuickJSRuntime(rt = ${rt}) not found for C module loader`);
                    }
                    const loadModule = runtimeCallbacks.loadModuleSource;
                    if (!loadModule) {
                        throw new Error(`QuickJSRuntime(rt = ${rt}) does not support module loading`);
                    }
                    return loadModule(rt, ctx, moduleName);
                }
                catch (error) {
                    console.error("[C to host module loader error: returning null]", error);
                    return 0;
                }
            }),
            normalizeModule: (asyncify, rt, ctx, moduleBaseName, moduleName) => this.handleAsyncify(asyncify, () => {
                try {
                    const runtimeCallbacks = this.runtimeCallbacks.get(rt);
                    if (!runtimeCallbacks) {
                        throw new Error(`QuickJSRuntime(rt = ${rt}) not found for C module loader`);
                    }
                    const normalizeModule = runtimeCallbacks.normalizeModule;
                    if (!normalizeModule) {
                        throw new Error(`QuickJSRuntime(rt = ${rt}) does not support module loading`);
                    }
                    return normalizeModule(rt, ctx, moduleBaseName, moduleName);
                }
                catch (error) {
                    console.error("[C to host module loader error: returning null]", error);
                    return 0;
                }
            }),
        });
        this.module = module;
        this.module.callbacks = this.cToHostCallbacks;
    }
    setRuntimeCallbacks(rt, callbacks) {
        this.runtimeCallbacks.set(rt, callbacks);
    }
    deleteRuntime(rt) {
        this.runtimeCallbacks.delete(rt);
    }
    setContextCallbacks(ctx, callbacks) {
        this.contextCallbacks.set(ctx, callbacks);
    }
    deleteContext(ctx) {
        this.contextCallbacks.delete(ctx);
    }
    handleAsyncify(asyncify, fn) {
        if (asyncify) {
            // We must always call asyncify.handleSync around our function.
            // This allows asyncify to resume suspended execution on the second call.
            // Asyncify internally can detect sync behavior, and avoid suspending.
            return asyncify.handleSleep((done) => {
                try {
                    const result = fn();
                    if (!(result instanceof Promise)) {
                        (0, debug_1.debugLog)("asyncify.handleSleep: not suspending:", result);
                        done(result);
                        return;
                    }
                    // Is promise, we intend to suspend.
                    if (this.suspended) {
                        throw new errors_1.QuickJSAsyncifyError(`Already suspended at: ${this.suspended.stack}\nAttempted to suspend at:`);
                    }
                    else {
                        this.suspended = new errors_1.QuickJSAsyncifySuspended(`(${this.suspendedCount++})`);
                        (0, debug_1.debugLog)("asyncify.handleSleep: suspending:", this.suspended);
                    }
                    result.then((resolvedResult) => {
                        this.suspended = undefined;
                        (0, debug_1.debugLog)("asyncify.handleSleep: resolved:", resolvedResult);
                        done(resolvedResult);
                    }, (error) => {
                        (0, debug_1.debugLog)("asyncify.handleSleep: rejected:", error);
                        console.error("QuickJS: cannot handle error in suspended function", error);
                        this.suspended = undefined;
                    });
                }
                catch (error) {
                    (0, debug_1.debugLog)("asyncify.handleSleep: error:", error);
                    this.suspended = undefined;
                    throw error;
                }
            });
        }
        // No asyncify - we should never return a promise.
        const value = fn();
        if (value instanceof Promise) {
            throw new Error("Promise return value not supported in non-asyncify context.");
        }
        return value;
    }
}
exports.QuickJSModuleCallbacks = QuickJSModuleCallbacks;
/**
 * Process RuntimeOptions and apply them to a QuickJSRuntime.
 * @private
 */
function applyBaseRuntimeOptions(runtime, options) {
    if (options.interruptHandler) {
        runtime.setInterruptHandler(options.interruptHandler);
    }
    if (options.maxStackSizeBytes !== undefined) {
        runtime.setMaxStackSize(options.maxStackSizeBytes);
    }
    if (options.memoryLimitBytes !== undefined) {
        runtime.setMemoryLimit(options.memoryLimitBytes);
    }
}
exports.applyBaseRuntimeOptions = applyBaseRuntimeOptions;
/**
 * Process ModuleEvalOptions and apply them to a QuickJSRuntime.
 * @private
 */
function applyModuleEvalRuntimeOptions(runtime, options) {
    if (options.moduleLoader) {
        runtime.setModuleLoader(options.moduleLoader);
    }
    if (options.shouldInterrupt) {
        runtime.setInterruptHandler(options.shouldInterrupt);
    }
    if (options.memoryLimitBytes !== undefined) {
        runtime.setMemoryLimit(options.memoryLimitBytes);
    }
    if (options.maxStackSizeBytes !== undefined) {
        runtime.setMaxStackSize(options.maxStackSizeBytes);
    }
}
exports.applyModuleEvalRuntimeOptions = applyModuleEvalRuntimeOptions;
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
class QuickJSWASMModule {
    /** @private */
    constructor(module, ffi) {
        this.module = module;
        this.ffi = ffi;
        this.callbacks = new QuickJSModuleCallbacks(module);
    }
    /**
     * Create a runtime.
     * Use the runtime to set limits on CPU and memory usage and configure module
     * loading for one or more [[QuickJSContext]]s inside the runtime.
     */
    newRuntime(options = {}) {
        const rt = new lifetime_1.Lifetime(this.ffi.QTS_NewRuntime(), undefined, (rt_ptr) => {
            this.callbacks.deleteRuntime(rt_ptr);
            this.ffi.QTS_FreeRuntime(rt_ptr);
        });
        const runtime = new runtime_1.QuickJSRuntime({
            module: this.module,
            callbacks: this.callbacks,
            ffi: this.ffi,
            rt,
        });
        applyBaseRuntimeOptions(runtime, options);
        if (options.moduleLoader) {
            runtime.setModuleLoader(options.moduleLoader);
        }
        return runtime;
    }
    /**
     * A simplified API to create a new [[QuickJSRuntime]] and a
     * [[QuickJSContext]] inside that runtime at the same time. The runtime will
     * be disposed when the context is disposed.
     */
    newContext(options = {}) {
        const runtime = this.newRuntime();
        const context = runtime.newContext({
            ...options,
            ownedLifetimes: (0, types_1.concat)(runtime, options.ownedLifetimes),
        });
        runtime.context = context;
        return context;
    }
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
    evalCode(code, options = {}) {
        return lifetime_1.Scope.withScope((scope) => {
            const vm = scope.manage(this.newContext());
            applyModuleEvalRuntimeOptions(vm.runtime, options);
            const result = vm.evalCode(code, "eval.js");
            if (options.memoryLimitBytes !== undefined) {
                // Remove memory limit so we can dump the result without exceeding it.
                vm.runtime.setMemoryLimit(-1);
            }
            if (result.error) {
                const error = vm.dump(scope.manage(result.error));
                throw error;
            }
            const value = vm.dump(scope.manage(result.value));
            return value;
        });
    }
    /**
     * Get a low-level interface to the QuickJS functions in this WebAssembly
     * module.
     * @experimental
     * @unstable No warranty is provided with this API. It could change at any time.
     * @private
     */
    getFFI() {
        return this.ffi;
    }
}
exports.QuickJSWASMModule = QuickJSWASMModule;
//# sourceMappingURL=module.js.map