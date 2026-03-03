"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.QuickJSAsyncWASMModule = void 0;
const errors_1 = require("./errors");
const lifetime_1 = require("./lifetime");
const module_1 = require("./module");
const runtime_asyncify_1 = require("./runtime-asyncify");
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
class QuickJSAsyncWASMModule extends module_1.QuickJSWASMModule {
    /** @private */
    constructor(module, ffi) {
        super(module, ffi);
        this.ffi = ffi;
        this.module = module;
    }
    /**
     * Create a new async runtime inside this WebAssembly module. All runtimes inside a
     * module are limited to a single async call at a time. For multiple
     * concurrent async actions, create multiple WebAssembly modules.
     */
    newRuntime(options = {}) {
        const rt = new lifetime_1.Lifetime(this.ffi.QTS_NewRuntime(), undefined, (rt_ptr) => {
            this.callbacks.deleteRuntime(rt_ptr);
            this.ffi.QTS_FreeRuntime(rt_ptr);
        });
        const runtime = new runtime_asyncify_1.QuickJSAsyncRuntime({
            module: this.module,
            ffi: this.ffi,
            rt,
            callbacks: this.callbacks,
        });
        (0, module_1.applyBaseRuntimeOptions)(runtime, options);
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
        const lifetimes = options.ownedLifetimes ? options.ownedLifetimes.concat([runtime]) : [runtime];
        const context = runtime.newContext({ ...options, ownedLifetimes: lifetimes });
        runtime.context = context;
        return context;
    }
    /** Synchronous evalCode is not supported. */
    evalCode() {
        throw new errors_1.QuickJSNotImplemented("QuickJSWASMModuleAsyncify.evalCode: use evalCodeAsync instead");
    }
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
    evalCodeAsync(code, options) {
        // TODO: we should really figure out generator for the Promise monad...
        return lifetime_1.Scope.withScopeAsync(async (scope) => {
            const vm = scope.manage(this.newContext());
            (0, module_1.applyModuleEvalRuntimeOptions)(vm.runtime, options);
            const result = await vm.evalCodeAsync(code, "eval.js");
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
}
exports.QuickJSAsyncWASMModule = QuickJSAsyncWASMModule;
//# sourceMappingURL=module-asyncify.js.map