/**
 * interface.c
 *
 * We primarily use JSValue* (pointer to JSValue) when communicating with the
 * host javascript environment, because pointers are trivial to use for calls
 * into emscripten because they're just a number!
 *
 * As with the quickjs.h API, a JSValueConst* value is "borrowed" and should
 * not be freed. A JSValue* is "owned" and should be freed by the owner.
 *
 * Functions starting with "QTS_" are exported by generate.ts to:
 * - interface.h for native C code.
 * - ffi.ts for emscripten.
 *
 * We support building the following build outputs:
 *
 * ## 1. Native machine code
 * For internal development testing purposes.
 *
 * ## 2. WASM via Emscripten
 * For general production use.
 *
 * ## 3. Experimental: Asyncified WASM via Emscripten with -s ASYNCIFY=1.
 * This variant supports treating async host Javascript calls as synchronous
 * from the perspective of the WASM c code.
 *
 * The way this works is described here:
 * https://emscripten.org/docs/porting/asyncify.html
 *
 * In this variant, any call into our C code could return a promise if it ended
 * up suspended. We mark the methods we suspect might suspend due to users' code
 * as returning MaybeAsync(T). This information is ignored for the regular
 * build.
 */

#ifdef __EMSCRIPTEN__
#include <emscripten.h>
#endif

#include <math.h>  // For NAN
#include <stdbool.h>
#include <stdio.h>
#include <string.h>
#ifdef QTS_SANITIZE_LEAK
#include <sanitizer/lsan_interface.h>
#endif

#include "../quickjs/cutils.h"
#include "../quickjs/quickjs-libc.h"
#include "../quickjs/quickjs.h"

#define PKG "quickjs-emscripten: "

#ifdef QTS_DEBUG_MODE
#define QTS_DEBUG(msg) qts_log(msg);
#define QTS_DUMP(value) qts_dump(ctx, value);
#else
#define QTS_DEBUG(msg) ;
#define QTS_DUMP(value) ;
#endif

/**
 * Signal to our FFI code generator that this string argument should be passed as a pointer
 * allocated by the caller on the heap, not a JS string on the stack.
 * https://github.com/emscripten-core/emscripten/issues/6860#issuecomment-405818401
 */
#define BorrowedHeapChar const char
#define OwnedHeapChar char
#define JSBorrowedChar const char

/**
 * Signal to our FFI code generator that this function should be called
 * asynchronously when compiled with ASYNCIFY.
 */
#define MaybeAsync(T) T

/**
 * Signal to our FFI code generator that this function is only available in
 * ASYNCIFY builds.
 */
#define AsyncifyOnly(T) T

#define JSVoid void

#define EvalFlags int
#define EvalDetectModule int

void qts_log(char *msg) {
  fputs(PKG, stderr);
  fputs(msg, stderr);
  fputs("\n", stderr);
}

void qts_dump(JSContext *ctx, JSValueConst value) {
  const char *str = JS_ToCString(ctx, value);
  if (!str) {
    QTS_DEBUG("QTS_DUMP: can't dump");
    return;
  }
  fputs(str, stderr);
  JS_FreeCString(ctx, str);
  putchar('\n');
}

void copy_prop_if_needed(JSContext *ctx, JSValueConst dest, JSValueConst src, const char *prop_name) {
  JSAtom prop_atom = JS_NewAtom(ctx, prop_name);
  JSValue dest_prop = JS_GetProperty(ctx, dest, prop_atom);
  if (JS_IsUndefined(dest_prop)) {
    JSValue src_prop = JS_GetProperty(ctx, src, prop_atom);
    if (!JS_IsUndefined(src_prop) && !JS_IsException(src_prop)) {
      JS_SetProperty(ctx, dest, prop_atom, src_prop);
    }
  } else {
    JS_FreeValue(ctx, dest_prop);
  }
  JS_FreeAtom(ctx, prop_atom);
}

JSValue *jsvalue_to_heap(JSValueConst value) {
  JSValue *result = malloc(sizeof(JSValue));
  if (result) {
    // Could be better optimized, but at -0z / -ftlo, it
    // appears to produce the same binary code as a memcpy.
    *result = value;
  }
  return result;
}

JSValue *QTS_Throw(JSContext *ctx, JSValueConst *error) {
  JSValue copy = JS_DupValue(ctx, *error);
  return jsvalue_to_heap(JS_Throw(ctx, copy));
}

JSValue *QTS_NewError(JSContext *ctx) {
  return jsvalue_to_heap(JS_NewError(ctx));
}

/**
 * Limits.
 */

/**
 * Memory limit. Set to -1 to disable.
 */
void QTS_RuntimeSetMemoryLimit(JSRuntime *rt, size_t limit) {
  JS_SetMemoryLimit(rt, limit);
}

/**
 * Memory diagnostics
 */

JSValue *QTS_RuntimeComputeMemoryUsage(JSRuntime *rt, JSContext *ctx) {
  JSMemoryUsage s;
  JS_ComputeMemoryUsage(rt, &s);

  // Note that we're going to allocate more memory just to report the memory usage.
  // A more sound approach would be to bind JSMemoryUsage struct directly - but that's
  // a lot of work. This should be okay in the mean time.
  JSValue result = JS_NewObject(ctx);

  // Manually generated via editor-fu from JSMemoryUsage struct definition in quickjs.h
  JS_SetPropertyStr(ctx, result, "malloc_limit", JS_NewInt64(ctx, s.malloc_limit));
  JS_SetPropertyStr(ctx, result, "memory_used_size", JS_NewInt64(ctx, s.memory_used_size));
  JS_SetPropertyStr(ctx, result, "malloc_count", JS_NewInt64(ctx, s.malloc_count));
  JS_SetPropertyStr(ctx, result, "memory_used_count", JS_NewInt64(ctx, s.memory_used_count));
  JS_SetPropertyStr(ctx, result, "atom_count", JS_NewInt64(ctx, s.atom_count));
  JS_SetPropertyStr(ctx, result, "atom_size", JS_NewInt64(ctx, s.atom_size));
  JS_SetPropertyStr(ctx, result, "str_count", JS_NewInt64(ctx, s.str_count));
  JS_SetPropertyStr(ctx, result, "str_size", JS_NewInt64(ctx, s.str_size));
  JS_SetPropertyStr(ctx, result, "obj_count", JS_NewInt64(ctx, s.obj_count));
  JS_SetPropertyStr(ctx, result, "obj_size", JS_NewInt64(ctx, s.obj_size));
  JS_SetPropertyStr(ctx, result, "prop_count", JS_NewInt64(ctx, s.prop_count));
  JS_SetPropertyStr(ctx, result, "prop_size", JS_NewInt64(ctx, s.prop_size));
  JS_SetPropertyStr(ctx, result, "shape_count", JS_NewInt64(ctx, s.shape_count));
  JS_SetPropertyStr(ctx, result, "shape_size", JS_NewInt64(ctx, s.shape_size));
  JS_SetPropertyStr(ctx, result, "js_func_count", JS_NewInt64(ctx, s.js_func_count));
  JS_SetPropertyStr(ctx, result, "js_func_size", JS_NewInt64(ctx, s.js_func_size));
  JS_SetPropertyStr(ctx, result, "js_func_code_size", JS_NewInt64(ctx, s.js_func_code_size));
  JS_SetPropertyStr(ctx, result, "js_func_pc2line_count", JS_NewInt64(ctx, s.js_func_pc2line_count));
  JS_SetPropertyStr(ctx, result, "js_func_pc2line_size", JS_NewInt64(ctx, s.js_func_pc2line_size));
  JS_SetPropertyStr(ctx, result, "c_func_count", JS_NewInt64(ctx, s.c_func_count));
  JS_SetPropertyStr(ctx, result, "array_count", JS_NewInt64(ctx, s.array_count));
  JS_SetPropertyStr(ctx, result, "fast_array_count", JS_NewInt64(ctx, s.fast_array_count));
  JS_SetPropertyStr(ctx, result, "fast_array_elements", JS_NewInt64(ctx, s.fast_array_elements));
  JS_SetPropertyStr(ctx, result, "binary_object_count", JS_NewInt64(ctx, s.binary_object_count));
  JS_SetPropertyStr(ctx, result, "binary_object_size", JS_NewInt64(ctx, s.binary_object_size));

  return jsvalue_to_heap(result);
}

OwnedHeapChar *QTS_RuntimeDumpMemoryUsage(JSRuntime *rt) {
  char *result = malloc(sizeof(char) * 1024);
  FILE *memfile = fmemopen(result, 1024, "w");
  JSMemoryUsage s;
  JS_ComputeMemoryUsage(rt, &s);
  JS_DumpMemoryUsage(memfile, &s, rt);
  fclose(memfile);
  return result;
}

int QTS_RecoverableLeakCheck() {
#ifdef QTS_SANITIZE_LEAK
  return __lsan_do_recoverable_leak_check();
#else
  return 0;
#endif
}

int QTS_BuildIsSanitizeLeak() {
#ifdef QTS_SANITIZE_LEAK
  return 1;
#else
  return 0;
#endif
}

#ifdef QTS_ASYNCIFY
EM_JS(void, set_asyncify_stack_size, (size_t size), {
  Asyncify.StackSize = size || 81920;
});
#endif

/**
 * Set the stack size limit, in bytes. Set to 0 to disable.
 */
void QTS_RuntimeSetMaxStackSize(JSRuntime *rt, size_t stack_size) {
#ifdef QTS_ASYNCIFY
  set_asyncify_stack_size(stack_size);
#endif
  JS_SetMaxStackSize(rt, stack_size);
}

/**
 * Constant pointers. Because we always use JSValue* from the host Javascript environment,
 * we need helper fuctions to return pointers to these constants.
 */

JSValueConst QTS_Undefined = JS_UNDEFINED;
JSValueConst *QTS_GetUndefined() {
  return &QTS_Undefined;
}

JSValueConst QTS_Null = JS_NULL;
JSValueConst *QTS_GetNull() {
  return &QTS_Null;
}

JSValueConst QTS_False = JS_FALSE;
JSValueConst *QTS_GetFalse() {
  return &QTS_False;
}

JSValueConst QTS_True = JS_TRUE;
JSValueConst *QTS_GetTrue() {
  return &QTS_True;
}

/**
 * Standard FFI functions
 */

JSRuntime *QTS_NewRuntime() {
  return JS_NewRuntime();
}

void QTS_FreeRuntime(JSRuntime *rt) {
  JS_FreeRuntime(rt);
}

JSContext *QTS_NewContext(JSRuntime *rt) {
  return JS_NewContext(rt);
}

void QTS_FreeContext(JSContext *ctx) {
  JS_FreeContext(ctx);
}

void QTS_FreeValuePointer(JSContext *ctx, JSValue *value) {
  JS_FreeValue(ctx, *value);
  free(value);
}

void QTS_FreeValuePointerRuntime(JSRuntime *rt, JSValue *value) {
  JS_FreeValueRT(rt, *value);
  free(value);
}

void QTS_FreeVoidPointer(JSContext *ctx, JSVoid *ptr) {
  js_free(ctx, ptr);
}

void QTS_FreeCString(JSContext *ctx, JSBorrowedChar *str) {
  JS_FreeCString(ctx, str);
}

JSValue *QTS_DupValuePointer(JSContext *ctx, JSValueConst *val) {
  return jsvalue_to_heap(JS_DupValue(ctx, *val));
}

JSValue *QTS_NewObject(JSContext *ctx) {
  return jsvalue_to_heap(JS_NewObject(ctx));
}

JSValue *QTS_NewObjectProto(JSContext *ctx, JSValueConst *proto) {
  return jsvalue_to_heap(JS_NewObjectProto(ctx, *proto));
}

JSValue *QTS_NewArray(JSContext *ctx) {
  return jsvalue_to_heap(JS_NewArray(ctx));
}

JSValue *QTS_NewFloat64(JSContext *ctx, double num) {
  return jsvalue_to_heap(JS_NewFloat64(ctx, num));
}

double QTS_GetFloat64(JSContext *ctx, JSValueConst *value) {
  double result = NAN;
  JS_ToFloat64(ctx, &result, *value);
  return result;
}

JSValue *QTS_NewString(JSContext *ctx, BorrowedHeapChar *string) {
  return jsvalue_to_heap(JS_NewString(ctx, string));
}

JSBorrowedChar *QTS_GetString(JSContext *ctx, JSValueConst *value) {
  return JS_ToCString(ctx, *value);
}

JSValue qts_get_symbol_key(JSContext *ctx, JSValueConst *value) {
  JSValue global = JS_GetGlobalObject(ctx);
  JSValue Symbol = JS_GetPropertyStr(ctx, global, "Symbol");
  JS_FreeValue(ctx, global);

  JSValue Symbol_keyFor = JS_GetPropertyStr(ctx, Symbol, "keyFor");
  JSValue key = JS_Call(ctx, Symbol_keyFor, Symbol, 1, value);
  JS_FreeValue(ctx, Symbol_keyFor);
  JS_FreeValue(ctx, Symbol);
  return key;
}

JSValue *QTS_NewSymbol(JSContext *ctx, BorrowedHeapChar *description, int isGlobal) {
  JSValue global = JS_GetGlobalObject(ctx);
  JSValue Symbol = JS_GetPropertyStr(ctx, global, "Symbol");
  JS_FreeValue(ctx, global);
  JSValue descriptionValue = JS_NewString(ctx, description);
  JSValue symbol;

  if (isGlobal != 0) {
    JSValue Symbol_for = JS_GetPropertyStr(ctx, Symbol, "for");
    symbol = JS_Call(ctx, Symbol_for, Symbol, 1, &descriptionValue);
    JS_FreeValue(ctx, descriptionValue);
    JS_FreeValue(ctx, Symbol_for);
    JS_FreeValue(ctx, Symbol);
    return jsvalue_to_heap(symbol);
  }

  symbol = JS_Call(ctx, Symbol, JS_UNDEFINED, 1, &descriptionValue);
  JS_FreeValue(ctx, descriptionValue);
  JS_FreeValue(ctx, Symbol);

  return jsvalue_to_heap(symbol);
}

MaybeAsync(JSBorrowedChar *) QTS_GetSymbolDescriptionOrKey(JSContext *ctx, JSValueConst *value) {
  JSBorrowedChar *result;

  JSValue key = qts_get_symbol_key(ctx, value);
  if (!JS_IsUndefined(key)) {
    result = JS_ToCString(ctx, key);
    JS_FreeValue(ctx, key);
    return result;
  }

  JSValue description = JS_GetPropertyStr(ctx, *value, "description");
  result = JS_ToCString(ctx, description);
  JS_FreeValue(ctx, description);
  return result;
}

int QTS_IsGlobalSymbol(JSContext *ctx, JSValueConst *value) {
  JSValue key = qts_get_symbol_key(ctx, value);
  int undefined = JS_IsUndefined(key);
  JS_FreeValue(ctx, key);

  if (undefined) {
    return 0;
  } else {
    return 1;
  }
}

int QTS_IsJobPending(JSRuntime *rt) {
  return JS_IsJobPending(rt);
}

/*
  runs pending jobs (Promises/async functions) until it encounters
  an exception or it executed the passed maxJobsToExecute jobs.

  Passing a negative value will run the loop until there are no more
  pending jobs or an exception happened

  Returns the executed number of jobs or the exception encountered
*/
MaybeAsync(JSValue *) QTS_ExecutePendingJob(JSRuntime *rt, int maxJobsToExecute, JSContext **lastJobContext) {
  JSContext *pctx;
  int status = 1;
  int executed = 0;
  while (executed != maxJobsToExecute && status == 1) {
    status = JS_ExecutePendingJob(rt, &pctx);
    if (status == -1) {
      *lastJobContext = pctx;
      return jsvalue_to_heap(JS_GetException(pctx));
    } else if (status == 1) {
      *lastJobContext = pctx;
      executed++;
    }
  }
#ifdef QTS_DEBUG_MODE
  char msg[500];
  sprintf(msg, "QTS_ExecutePendingJob(executed: %d, pctx: %p, lastJobExecuted: %p)", executed, pctx, *lastJobContext);
  QTS_DEBUG(msg)
#endif
  return jsvalue_to_heap(JS_NewFloat64(pctx, executed));
}

MaybeAsync(JSValue *) QTS_GetProp(JSContext *ctx, JSValueConst *this_val, JSValueConst *prop_name) {
  JSAtom prop_atom = JS_ValueToAtom(ctx, *prop_name);
  JSValue prop_val = JS_GetProperty(ctx, *this_val, prop_atom);
  JS_FreeAtom(ctx, prop_atom);
  return jsvalue_to_heap(prop_val);
}

MaybeAsync(void) QTS_SetProp(JSContext *ctx, JSValueConst *this_val, JSValueConst *prop_name, JSValueConst *prop_value) {
  JSAtom prop_atom = JS_ValueToAtom(ctx, *prop_name);
  JSValue extra_prop_value = JS_DupValue(ctx, *prop_value);
  // TODO: should we use DefineProperty internally if this object doesn't have the property yet?
  JS_SetProperty(ctx, *this_val, prop_atom, extra_prop_value);  // consumes extra_prop_value
  JS_FreeAtom(ctx, prop_atom);
}

void QTS_DefineProp(JSContext *ctx, JSValueConst *this_val, JSValueConst *prop_name, JSValueConst *prop_value, JSValueConst *get, JSValueConst *set, bool configurable, bool enumerable, bool has_value) {
  JSAtom prop_atom = JS_ValueToAtom(ctx, *prop_name);

  int flags = 0;
  if (configurable) {
    flags = flags | JS_PROP_CONFIGURABLE;
    if (has_value) {
      flags = flags | JS_PROP_HAS_CONFIGURABLE;
    }
  }
  if (enumerable) {
    flags = flags | JS_PROP_ENUMERABLE;
    if (has_value) {
      flags = flags | JS_PROP_HAS_ENUMERABLE;
    }
  }
  if (!JS_IsUndefined(*get)) {
    flags = flags | JS_PROP_HAS_GET;
  }
  if (!JS_IsUndefined(*set)) {
    flags = flags | JS_PROP_HAS_SET;
  }
  if (has_value) {
    flags = flags | JS_PROP_HAS_VALUE;
  }

  JS_DefineProperty(ctx, *this_val, prop_atom, *prop_value, *get, *set, flags);
  JS_FreeAtom(ctx, prop_atom);
}

MaybeAsync(JSValue *) QTS_Call(JSContext *ctx, JSValueConst *func_obj, JSValueConst *this_obj, int argc, JSValueConst **argv_ptrs) {
  // convert array of pointers to array of values
  JSValueConst argv[argc];
  int i;
  for (i = 0; i < argc; i++) {
    argv[i] = *(argv_ptrs[i]);
  }

  return jsvalue_to_heap(JS_Call(ctx, *func_obj, *this_obj, argc, argv));
}

/**
 * If maybe_exception is an exception, get the error.
 * Otherwise, return NULL.
 */
JSValue *QTS_ResolveException(JSContext *ctx, JSValue *maybe_exception) {
  if (JS_IsException(*maybe_exception)) {
    return jsvalue_to_heap(JS_GetException(ctx));
  }

  return NULL;
}

MaybeAsync(JSBorrowedChar *) QTS_Dump(JSContext *ctx, JSValueConst *obj) {
  JSValue obj_json_value = JS_JSONStringify(ctx, *obj, JS_UNDEFINED, JS_UNDEFINED);
  if (!JS_IsException(obj_json_value)) {
    const char *obj_json_chars = JS_ToCString(ctx, obj_json_value);
    JS_FreeValue(ctx, obj_json_value);
    if (obj_json_chars != NULL) {
      JSValue enumerable_props = JS_ParseJSON(ctx, obj_json_chars, strlen(obj_json_chars), "<dump>");
      JS_FreeCString(ctx, obj_json_chars);
      if (!JS_IsException(enumerable_props)) {
        // Copy common non-enumerable props for different object types.
        // Errors:
        copy_prop_if_needed(ctx, enumerable_props, *obj, "name");
        copy_prop_if_needed(ctx, enumerable_props, *obj, "message");
        copy_prop_if_needed(ctx, enumerable_props, *obj, "stack");

        // Serialize again.
        JSValue enumerable_json = JS_JSONStringify(ctx, enumerable_props, JS_UNDEFINED, JS_UNDEFINED);
        JS_FreeValue(ctx, enumerable_props);

        JSBorrowedChar *result = QTS_GetString(ctx, &enumerable_json);
        JS_FreeValue(ctx, enumerable_json);
        return result;
      }
    }
  }

#ifdef QTS_DEBUG_MODE
  qts_log("Error dumping JSON:");
  js_std_dump_error(ctx);
#endif

  // Fallback: convert to string
  return QTS_GetString(ctx, obj);
}

MaybeAsync(JSValue *) QTS_Eval(JSContext *ctx, BorrowedHeapChar *js_code, const char *filename, EvalDetectModule detectModule, EvalFlags evalFlags) {
  size_t js_code_len = strlen(js_code);

  if (detectModule) {
    if (JS_DetectModule((const char *)js_code, js_code_len)) {
      QTS_DEBUG("QTS_Eval: Detected module = true");
      evalFlags |= JS_EVAL_TYPE_MODULE;
    } else {
      QTS_DEBUG("QTS_Eval: Detected module = false");
    }
  } else {
    QTS_DEBUG("QTS_Eval: do not detect module");
  }

  return jsvalue_to_heap(JS_Eval(ctx, js_code, strlen(js_code), filename, evalFlags));
}

OwnedHeapChar *QTS_Typeof(JSContext *ctx, JSValueConst *value) {
  const char *result = "unknown";
  uint32_t tag = JS_VALUE_GET_TAG(*value);

  if (JS_IsNumber(*value)) {
    result = "number";
  } else if (JS_IsBigInt(ctx, *value)) {
    result = "bigint";
  } else if (JS_IsBigFloat(*value)) {
    result = "bigfloat";
  } else if (JS_IsBigDecimal(*value)) {
    result = "bigdecimal";
  } else if (JS_IsFunction(ctx, *value)) {
    result = "function";
  } else if (JS_IsBool(*value)) {
    result = "boolean";
  } else if (JS_IsNull(*value)) {
    result = "object";
  } else if (JS_IsUndefined(*value)) {
    result = "undefined";
  } else if (JS_IsUninitialized(*value)) {
    result = "undefined";
  } else if (JS_IsString(*value)) {
    result = "string";
  } else if (JS_IsSymbol(*value)) {
    result = "symbol";
  } else if (JS_IsObject(*value)) {
    result = "object";
  }

  char *out = strdup(result);
  return out;
}

JSValue *QTS_GetGlobalObject(JSContext *ctx) {
  return jsvalue_to_heap(JS_GetGlobalObject(ctx));
}

JSValue *QTS_NewPromiseCapability(JSContext *ctx, JSValue **resolve_funcs_out) {
  JSValue resolve_funcs[2];
  JSValue promise = JS_NewPromiseCapability(ctx, resolve_funcs);
  resolve_funcs_out[0] = jsvalue_to_heap(resolve_funcs[0]);
  resolve_funcs_out[1] = jsvalue_to_heap(resolve_funcs[1]);
  return jsvalue_to_heap(promise);
}

void QTS_TestStringArg(const char *string) {
  // pass
}

int QTS_BuildIsDebug() {
#ifdef QTS_DEBUG_MODE
  return 1;
#else
  return 0;
#endif
}

int QTS_BuildIsAsyncify() {
#ifdef QTS_ASYNCIFY
  return 1;
#else
  return 0;
#endif
}

// ----------------------------------------------------------------------------
// Module loading helpers

// ----------------------------------------------------------------------------
// C -> Host Callbacks
// Note: inside EM_JS, we need to use ['...'] subscript syntax for accessing JS
// objects, because in optimized builds, Closure compiler will mangle all the
// names.

// -------------------
// function: C -> Host
#ifdef __EMSCRIPTEN__
EM_JS(MaybeAsync(JSValue *), qts_host_call_function, (JSContext * ctx, JSValueConst *this_ptr, int argc, JSValueConst *argv, uint32_t magic_func_id), {
#ifdef QTS_ASYNCIFY
  const asyncify = {['handleSleep'] : Asyncify.handleSleep};
#else
  const asyncify = undefined;
#endif
  return Module['callbacks']['callFunction'](asyncify, ctx, this_ptr, argc, argv, magic_func_id);
});
#endif

// Function: QuickJS -> C
JSValue qts_call_function(JSContext *ctx, JSValueConst this_val, int argc, JSValueConst *argv, int magic) {
  JSValue *result_ptr = qts_host_call_function(ctx, &this_val, argc, argv, magic);
  if (result_ptr == NULL) {
    return JS_UNDEFINED;
  }
  JSValue result = *result_ptr;
  free(result_ptr);
  return result;
}

// Function: Host -> QuickJS
JSValue *QTS_NewFunction(JSContext *ctx, uint32_t func_id, const char *name) {
#ifdef QTS_DEBUG_MODE
  char msg[500];
  sprintf(msg, "new_function(name: %s, magic: %d)", name, func_id);
  QTS_DEBUG(msg)
#endif
  JSValue func_obj = JS_NewCFunctionMagic(
      /* context */ ctx,
      /* JSCFunctionMagic* */ &qts_call_function,
      /* name */ name,
      /* min argc */ 0,
      /* function type */ JS_CFUNC_generic_magic,
      /* magic: fn id */ func_id);
  return jsvalue_to_heap(func_obj);
}

JSValueConst *QTS_ArgvGetJSValueConstPointer(JSValueConst *argv, int index) {
  return &argv[index];
}

// --------------------
// interrupt: C -> Host
#ifdef __EMSCRIPTEN__
EM_JS(int, qts_host_interrupt_handler, (JSRuntime * rt), {
  // Async not supported here.
  // #ifdef QTS_ASYNCIFY
  //   const asyncify = Asyncify;
  // #else
  const asyncify = undefined;
  // #endif
  return Module['callbacks']['shouldInterrupt'](asyncify, rt);
});
#endif

// interrupt: QuickJS -> C
int qts_interrupt_handler(JSRuntime *rt, void *_unused) {
  return qts_host_interrupt_handler(rt);
}

// interrupt: Host -> QuickJS
void QTS_RuntimeEnableInterruptHandler(JSRuntime *rt) {
  JS_SetInterruptHandler(rt, &qts_interrupt_handler, NULL);
}

void QTS_RuntimeDisableInterruptHandler(JSRuntime *rt) {
  JS_SetInterruptHandler(rt, NULL, NULL);
}

// --------------------
// load module: C -> Host
// TODO: a future version can support host returning JSModuleDef* directly;
// for now we only support loading module source code.

/*
The module loading model under ASYNCIFY is convoluted. We need to make sure we
never have an async request running concurrently for loading modules.

The first implemenation looked like this:

C                                  HOST                      SUSPENDED
qts_host_load_module(name) ------>                            false
                                   call rt.loadModule(name)   false
                                   Start async load module    false
                                   Suspend C                  true
                                   Async load complete        true
            < ---------------      QTS_CompileModule(source)  true
QTS_Eval(source, COMPILE_ONLY)                                true
Loaded module has import                                      true
qts_host_load_module(dep) ------->                            true
                                  call rt.loadModule(dep)     true
                                  Start async load module     true
                                  ALREADY SUSPENDED, CRASH

We can solve this in two different ways:

1. Return to C as soon as we async load the module source.
   That way, we unsuspend before calling QTS_CompileModule.
2. Once we load the module, use a new API to detect and async
   load the module's downstream dependencies. This way
   they're loaded synchronously so we don't need to suspend "again".

Probably we could optimize (2) to make it more performant, eg with parallel
loading, but (1) seems much easier to implement in the sort run.
*/

JSModuleDef *qts_compile_module(JSContext *ctx, const char *module_name, BorrowedHeapChar *module_body) {
#ifdef QTS_DEBUG_MODE
  char msg[500];
  sprintf(msg, "QTS_CompileModule(ctx: %p, name: %s, bodyLength: %lu)", ctx, module_name, strlen(module_body));
  QTS_DEBUG(msg)
#endif
  JSValue func_val = JS_Eval(ctx, module_body, strlen(module_body), module_name, JS_EVAL_TYPE_MODULE | JS_EVAL_FLAG_COMPILE_ONLY);
  if (JS_IsException(func_val)) {
    return NULL;
  }
  // TODO: Is exception ok?
  // TODO: set import.meta?
  JSModuleDef *module = JS_VALUE_GET_PTR(func_val);
  JS_FreeValue(ctx, func_val);
  return module;
}

#ifdef __EMSCRIPTEN__
EM_JS(MaybeAsync(char *), qts_host_load_module_source, (JSRuntime * rt, JSContext *ctx, const char *module_name), {
#ifdef QTS_ASYNCIFY
  const asyncify = {['handleSleep'] : Asyncify.handleSleep};
#else
  const asyncify = undefined;
#endif
  // https://emscripten.org/docs/api_reference/preamble.js.html#UTF8ToString
  const moduleNameString = UTF8ToString(module_name);
  return Module['callbacks']['loadModuleSource'](asyncify, rt, ctx, moduleNameString);
});

EM_JS(MaybeAsync(char *), qts_host_normalize_module, (JSRuntime * rt, JSContext *ctx, const char *module_base_name, const char *module_name), {
#ifdef QTS_ASYNCIFY
  const asyncify = {['handleSleep'] : Asyncify.handleSleep};
#else
  const asyncify = undefined;
#endif
  // https://emscripten.org/docs/api_reference/preamble.js.html#UTF8ToString
  const moduleBaseNameString = UTF8ToString(module_base_name);
  const moduleNameString = UTF8ToString(module_name);
  return Module['callbacks']['normalizeModule'](asyncify, rt, ctx, moduleBaseNameString, moduleNameString);
});
#endif

// load module: QuickJS -> C
// See js_module_loader in quickjs/quickjs-libc.c:567
JSModuleDef *qts_load_module(JSContext *ctx, const char *module_name, void *_unused) {
  JSRuntime *rt = JS_GetRuntime(ctx);
#ifdef QTS_DEBUG_MODE
  char msg[500];
  sprintf(msg, "qts_load_module(rt: %p, ctx: %p, name: %s)", rt, ctx, module_name);
  QTS_DEBUG(msg)
#endif
  char *module_source = qts_host_load_module_source(rt, ctx, module_name);
  if (module_source == NULL) {
    return NULL;
  }

  JSModuleDef *module = qts_compile_module(ctx, module_name, module_source);
  free(module_source);
  return module;
}

char *qts_normalize_module(JSContext *ctx, const char *module_base_name, const char *module_name, void *_unused) {
  JSRuntime *rt = JS_GetRuntime(ctx);
#ifdef QTS_DEBUG_MODE
  char msg[500];
  sprintf(msg, "qts_normalize_module(rt: %p, ctx: %p, base_name: %s, name: %s)", rt, ctx, module_base_name, module_name);
  QTS_DEBUG(msg)
#endif
  char *em_module_name = qts_host_normalize_module(rt, ctx, module_base_name, module_name);
  char *js_module_name = js_strdup(ctx, em_module_name);
  free(em_module_name);
  return js_module_name;
}

// Load module: Host -> QuickJS
void QTS_RuntimeEnableModuleLoader(JSRuntime *rt, int use_custom_normalize) {
  JSModuleNormalizeFunc *module_normalize = NULL; /* use default name normalizer */
  if (use_custom_normalize) {
    module_normalize = &qts_normalize_module;
  }
  JS_SetModuleLoaderFunc(rt, module_normalize, &qts_load_module, NULL);
}

void QTS_RuntimeDisableModuleLoader(JSRuntime *rt) {
  JS_SetModuleLoaderFunc(rt, NULL, NULL, NULL);
}