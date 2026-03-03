"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.QuickJSAsyncContext = void 0;
const context_1 = require("./context");
const debug_1 = require("./debug");
const types_1 = require("./types");
/**
 * Asyncified version of [[QuickJSContext]].
 *
 * *Asyncify* allows normally synchronous code to wait for asynchronous Promises
 * or callbacks. The asyncified version of QuickJSContext can wait for async
 * host functions as though they were synchronous.
 */
class QuickJSAsyncContext extends context_1.QuickJSContext {
    /**
     * Asyncified version of [[evalCode]].
     */
    async evalCodeAsync(code, filename = "eval.js", 
    /** See [[EvalFlags]] for number semantics */
    options) {
        const detectModule = (options === undefined ? 1 : 0);
        const flags = (0, types_1.evalOptionsToFlags)(options);
        let resultPtr = 0;
        try {
            resultPtr = await this.memory
                .newHeapCharPointer(code)
                .consume((charHandle) => this.ffi.QTS_Eval_MaybeAsync(this.ctx.value, charHandle.value, filename, detectModule, flags));
        }
        catch (error) {
            (0, debug_1.debugLog)("QTS_Eval_MaybeAsync threw", error);
            throw error;
        }
        const errorPtr = this.ffi.QTS_ResolveException(this.ctx.value, resultPtr);
        if (errorPtr) {
            this.ffi.QTS_FreeValuePointer(this.ctx.value, resultPtr);
            return { error: this.memory.heapValueHandle(errorPtr) };
        }
        return { value: this.memory.heapValueHandle(resultPtr) };
    }
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
    newAsyncifiedFunction(name, fn) {
        return this.newFunction(name, fn);
    }
}
exports.QuickJSAsyncContext = QuickJSAsyncContext;
//# sourceMappingURL=context-asyncify.js.map