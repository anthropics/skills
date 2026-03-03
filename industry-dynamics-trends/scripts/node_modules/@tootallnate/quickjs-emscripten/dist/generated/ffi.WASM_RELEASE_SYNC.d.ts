import { QuickJSEmscriptenModule } from "../emscripten-types";
import { JSRuntimePointer, JSContextPointer, JSContextPointerPointer, JSValuePointer, JSValueConstPointer, JSValuePointerPointer, JSValueConstPointerPointer, BorrowedHeapCharPointer, OwnedHeapCharPointer, JSBorrowedCharPointer, JSVoidPointer, EvalFlags, EvalDetectModule } from "../types-ffi";
/**
 * Low-level FFI bindings to QuickJS's Emscripten module.
 * See instead [[QuickJSContext]], the public Javascript interface exposed by this
 * library.
 *
 * @unstable The FFI interface is considered private and may change.
 */
export declare class QuickJSFFI {
    private module;
    constructor(module: QuickJSEmscriptenModule);
    /** Set at compile time. */
    readonly DEBUG = false;
    QTS_Throw: (ctx: JSContextPointer, error: JSValuePointer | JSValueConstPointer) => JSValuePointer;
    QTS_NewError: (ctx: JSContextPointer) => JSValuePointer;
    QTS_RuntimeSetMemoryLimit: (rt: JSRuntimePointer, limit: number) => void;
    QTS_RuntimeComputeMemoryUsage: (rt: JSRuntimePointer, ctx: JSContextPointer) => JSValuePointer;
    QTS_RuntimeDumpMemoryUsage: (rt: JSRuntimePointer) => OwnedHeapCharPointer;
    QTS_RecoverableLeakCheck: () => number;
    QTS_BuildIsSanitizeLeak: () => number;
    QTS_RuntimeSetMaxStackSize: (rt: JSRuntimePointer, stack_size: number) => void;
    QTS_GetUndefined: () => JSValueConstPointer;
    QTS_GetNull: () => JSValueConstPointer;
    QTS_GetFalse: () => JSValueConstPointer;
    QTS_GetTrue: () => JSValueConstPointer;
    QTS_NewRuntime: () => JSRuntimePointer;
    QTS_FreeRuntime: (rt: JSRuntimePointer) => void;
    QTS_NewContext: (rt: JSRuntimePointer) => JSContextPointer;
    QTS_FreeContext: (ctx: JSContextPointer) => void;
    QTS_FreeValuePointer: (ctx: JSContextPointer, value: JSValuePointer) => void;
    QTS_FreeValuePointerRuntime: (rt: JSRuntimePointer, value: JSValuePointer) => void;
    QTS_FreeVoidPointer: (ctx: JSContextPointer, ptr: JSVoidPointer) => void;
    QTS_FreeCString: (ctx: JSContextPointer, str: JSBorrowedCharPointer) => void;
    QTS_DupValuePointer: (ctx: JSContextPointer, val: JSValuePointer | JSValueConstPointer) => JSValuePointer;
    QTS_NewObject: (ctx: JSContextPointer) => JSValuePointer;
    QTS_NewObjectProto: (ctx: JSContextPointer, proto: JSValuePointer | JSValueConstPointer) => JSValuePointer;
    QTS_NewArray: (ctx: JSContextPointer) => JSValuePointer;
    QTS_NewFloat64: (ctx: JSContextPointer, num: number) => JSValuePointer;
    QTS_GetFloat64: (ctx: JSContextPointer, value: JSValuePointer | JSValueConstPointer) => number;
    QTS_NewString: (ctx: JSContextPointer, string: BorrowedHeapCharPointer) => JSValuePointer;
    QTS_GetString: (ctx: JSContextPointer, value: JSValuePointer | JSValueConstPointer) => JSBorrowedCharPointer;
    QTS_NewSymbol: (ctx: JSContextPointer, description: BorrowedHeapCharPointer, isGlobal: number) => JSValuePointer;
    QTS_GetSymbolDescriptionOrKey: (ctx: JSContextPointer, value: JSValuePointer | JSValueConstPointer) => JSBorrowedCharPointer;
    QTS_IsGlobalSymbol: (ctx: JSContextPointer, value: JSValuePointer | JSValueConstPointer) => number;
    QTS_IsJobPending: (rt: JSRuntimePointer) => number;
    QTS_ExecutePendingJob: (rt: JSRuntimePointer, maxJobsToExecute: number, lastJobContext: JSContextPointerPointer) => JSValuePointer;
    QTS_GetProp: (ctx: JSContextPointer, this_val: JSValuePointer | JSValueConstPointer, prop_name: JSValuePointer | JSValueConstPointer) => JSValuePointer;
    QTS_SetProp: (ctx: JSContextPointer, this_val: JSValuePointer | JSValueConstPointer, prop_name: JSValuePointer | JSValueConstPointer, prop_value: JSValuePointer | JSValueConstPointer) => void;
    QTS_DefineProp: (ctx: JSContextPointer, this_val: JSValuePointer | JSValueConstPointer, prop_name: JSValuePointer | JSValueConstPointer, prop_value: JSValuePointer | JSValueConstPointer, get: JSValuePointer | JSValueConstPointer, set: JSValuePointer | JSValueConstPointer, configurable: boolean, enumerable: boolean, has_value: boolean) => void;
    QTS_Call: (ctx: JSContextPointer, func_obj: JSValuePointer | JSValueConstPointer, this_obj: JSValuePointer | JSValueConstPointer, argc: number, argv_ptrs: JSValueConstPointerPointer) => JSValuePointer;
    QTS_ResolveException: (ctx: JSContextPointer, maybe_exception: JSValuePointer) => JSValuePointer;
    QTS_Dump: (ctx: JSContextPointer, obj: JSValuePointer | JSValueConstPointer) => JSBorrowedCharPointer;
    QTS_Eval: (ctx: JSContextPointer, js_code: BorrowedHeapCharPointer, filename: string, detectModule: EvalDetectModule, evalFlags: EvalFlags) => JSValuePointer;
    QTS_Typeof: (ctx: JSContextPointer, value: JSValuePointer | JSValueConstPointer) => OwnedHeapCharPointer;
    QTS_GetGlobalObject: (ctx: JSContextPointer) => JSValuePointer;
    QTS_NewPromiseCapability: (ctx: JSContextPointer, resolve_funcs_out: JSValuePointerPointer) => JSValuePointer;
    QTS_TestStringArg: (string: string) => void;
    QTS_BuildIsDebug: () => number;
    QTS_BuildIsAsyncify: () => number;
    QTS_NewFunction: (ctx: JSContextPointer, func_id: number, name: string) => JSValuePointer;
    QTS_ArgvGetJSValueConstPointer: (argv: JSValuePointer | JSValueConstPointer, index: number) => JSValueConstPointer;
    QTS_RuntimeEnableInterruptHandler: (rt: JSRuntimePointer) => void;
    QTS_RuntimeDisableInterruptHandler: (rt: JSRuntimePointer) => void;
    QTS_RuntimeEnableModuleLoader: (rt: JSRuntimePointer, use_custom_normalize: number) => void;
    QTS_RuntimeDisableModuleLoader: (rt: JSRuntimePointer) => void;
}
