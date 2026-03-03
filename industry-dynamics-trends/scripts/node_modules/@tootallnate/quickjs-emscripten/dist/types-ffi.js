"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.EvalFlags = exports.assertSync = void 0;
function assertSync(fn) {
    return function mustBeSync(...args) {
        const result = fn(...args);
        if (result && typeof result === "object" && result instanceof Promise) {
            throw new Error("Function unexpectedly returned a Promise");
        }
        return result;
    };
}
exports.assertSync = assertSync;
/** Bitfield options for JS_Eval() C function. */
exports.EvalFlags = {
    /** global code (default) */
    JS_EVAL_TYPE_GLOBAL: 0 << 0,
    /** module code */
    JS_EVAL_TYPE_MODULE: 1 << 0,
    /** direct call (internal use) */
    JS_EVAL_TYPE_DIRECT: 2 << 0,
    /** indirect call (internal use) */
    JS_EVAL_TYPE_INDIRECT: 3 << 0,
    JS_EVAL_TYPE_MASK: 3 << 0,
    /** force 'strict' mode */
    JS_EVAL_FLAG_STRICT: 1 << 3,
    /** force 'strip' mode */
    JS_EVAL_FLAG_STRIP: 1 << 4,
    /**
     * compile but do not run. The result is an object with a
     * JS_TAG_FUNCTION_BYTECODE or JS_TAG_MODULE tag. It can be executed
     * with JS_EvalFunction().
     */
    JS_EVAL_FLAG_COMPILE_ONLY: 1 << 5,
    /** don't include the stack frames before this eval in the Error() backtraces */
    JS_EVAL_FLAG_BACKTRACE_BARRIER: 1 << 6,
};
//# sourceMappingURL=types-ffi.js.map