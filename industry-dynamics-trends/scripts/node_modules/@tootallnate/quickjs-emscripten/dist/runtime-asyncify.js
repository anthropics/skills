"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.QuickJSAsyncRuntime = void 0;
const _1 = require(".");
const context_asyncify_1 = require("./context-asyncify");
const runtime_1 = require("./runtime");
const types_1 = require("./types");
class QuickJSAsyncRuntime extends runtime_1.QuickJSRuntime {
    /** @private */
    constructor(args) {
        super(args);
    }
    newContext(options = {}) {
        if (options.intrinsics && options.intrinsics !== types_1.DefaultIntrinsics) {
            throw new Error("TODO: Custom intrinsics are not supported yet");
        }
        const ctx = new _1.Lifetime(this.ffi.QTS_NewContext(this.rt.value), undefined, (ctx_ptr) => {
            this.contextMap.delete(ctx_ptr);
            this.callbacks.deleteContext(ctx_ptr);
            this.ffi.QTS_FreeContext(ctx_ptr);
        });
        const context = new context_asyncify_1.QuickJSAsyncContext({
            module: this.module,
            ctx,
            ffi: this.ffi,
            rt: this.rt,
            ownedLifetimes: [],
            runtime: this,
            callbacks: this.callbacks,
        });
        this.contextMap.set(ctx.value, context);
        return context;
    }
    setModuleLoader(moduleLoader, moduleNormalizer) {
        super.setModuleLoader(moduleLoader, moduleNormalizer);
    }
    /**
     * Set the max stack size for this runtime in bytes.
     * To remove the limit, set to `0`.
     *
     * Setting this limit also adjusts the global `ASYNCIFY_STACK_SIZE` for the entire {@link QuickJSAsyncWASMModule}.
     * See the [pull request](https://github.com/justjake/quickjs-emscripten/pull/114) for more details.
     */
    setMaxStackSize(stackSize) {
        return super.setMaxStackSize(stackSize);
    }
}
exports.QuickJSAsyncRuntime = QuickJSAsyncRuntime;
//# sourceMappingURL=runtime-asyncify.js.map