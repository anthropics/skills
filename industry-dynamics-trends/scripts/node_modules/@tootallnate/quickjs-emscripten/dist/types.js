"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.concat = exports.evalOptionsToFlags = exports.DefaultIntrinsics = void 0;
const types_ffi_1 = require("./types-ffi");
const UnstableSymbol = Symbol("Unstable");
// For informational purposes
const DefaultIntrinsicsList = [
    "BaseObjects",
    "Date",
    "Eval",
    "StringNormalize",
    "RegExp",
    "JSON",
    "Proxy",
    "MapSet",
    "TypedArrays",
    "Promise",
];
/**
 * Work in progress.
 */
exports.DefaultIntrinsics = Symbol("DefaultIntrinsics");
/** Convert [[ContextEvalOptions]] to a bitfield flags */
function evalOptionsToFlags(evalOptions) {
    if (typeof evalOptions === "number") {
        return evalOptions;
    }
    if (evalOptions === undefined) {
        return 0;
    }
    const { type, strict, strip, compileOnly, backtraceBarrier } = evalOptions;
    let flags = 0;
    if (type === "global")
        flags |= types_ffi_1.EvalFlags.JS_EVAL_TYPE_GLOBAL;
    if (type === "module")
        flags |= types_ffi_1.EvalFlags.JS_EVAL_TYPE_MODULE;
    if (strict)
        flags |= types_ffi_1.EvalFlags.JS_EVAL_FLAG_STRICT;
    if (strip)
        flags |= types_ffi_1.EvalFlags.JS_EVAL_FLAG_STRIP;
    if (compileOnly)
        flags |= types_ffi_1.EvalFlags.JS_EVAL_FLAG_COMPILE_ONLY;
    if (backtraceBarrier)
        flags |= types_ffi_1.EvalFlags.JS_EVAL_FLAG_BACKTRACE_BARRIER;
    return flags;
}
exports.evalOptionsToFlags = evalOptionsToFlags;
function concat(...values) {
    let result = [];
    for (const value of values) {
        if (value !== undefined) {
            result = result.concat(value);
        }
    }
    return result;
}
exports.concat = concat;
//# sourceMappingURL=types.js.map