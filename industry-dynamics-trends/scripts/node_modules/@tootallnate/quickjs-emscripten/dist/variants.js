"use strict";
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __setModuleDefault = (this && this.__setModuleDefault) || (Object.create ? (function(o, v) {
    Object.defineProperty(o, "default", { enumerable: true, value: v });
}) : function(o, v) {
    o["default"] = v;
});
var __importStar = (this && this.__importStar) || function (mod) {
    if (mod && mod.__esModule) return mod;
    var result = {};
    if (mod != null) for (var k in mod) if (k !== "default" && Object.prototype.hasOwnProperty.call(mod, k)) __createBinding(result, mod, k);
    __setModuleDefault(result, mod);
    return result;
};
Object.defineProperty(exports, "__esModule", { value: true });
exports.RELEASE_ASYNC = exports.DEBUG_ASYNC = exports.RELEASE_SYNC = exports.DEBUG_SYNC = exports.memoizePromiseFactory = exports.newQuickJSAsyncWASMModule = exports.newQuickJSWASMModule = void 0;
const esmHelpers_1 = require("./esmHelpers");
/**
 * Create a new, completely isolated WebAssembly module containing the QuickJS library.
 * See the documentation on [[QuickJSWASMModule]].
 *
 * Note that there is a hard limit on the number of WebAssembly modules in older
 * versions of v8:
 * https://bugs.chromium.org/p/v8/issues/detail?id=12076
 */
async function newQuickJSWASMModule(
/**
 * Optionally, pass a {@link SyncBuildVariant} to construct a different WebAssembly module.
 */
variant = exports.RELEASE_SYNC) {
    const [wasmModuleLoader, QuickJSFFI, { QuickJSWASMModule }] = await Promise.all([
        variant.importModuleLoader(),
        variant.importFFI(),
        Promise.resolve().then(() => __importStar(require("./module.js"))).then(esmHelpers_1.unwrapTypescript),
    ]);
    const wasmModule = await wasmModuleLoader();
    wasmModule.type = "sync";
    const ffi = new QuickJSFFI(wasmModule);
    return new QuickJSWASMModule(wasmModule, ffi);
}
exports.newQuickJSWASMModule = newQuickJSWASMModule;
/**
 * Create a new, completely isolated WebAssembly module containing a version of the QuickJS library
 * compiled with Emscripten's [ASYNCIFY](https://emscripten.org/docs/porting/asyncify.html) transform.
 *
 * This version of the library offers features that enable synchronous code
 * inside the VM to interact with asynchronous code in the host environment.
 * See the documentation on [[QuickJSAsyncWASMModule]], [[QuickJSAsyncRuntime]],
 * and [[QuickJSAsyncContext]].
 *
 * Note that there is a hard limit on the number of WebAssembly modules in older
 * versions of v8:
 * https://bugs.chromium.org/p/v8/issues/detail?id=12076
 */
async function newQuickJSAsyncWASMModule(
/**
 * Optionally, pass a {@link AsyncBuildVariant} to construct a different WebAssembly module.
 */
variant = exports.RELEASE_ASYNC) {
    const [wasmModuleLoader, QuickJSAsyncFFI, { QuickJSAsyncWASMModule }] = await Promise.all([
        variant.importModuleLoader(),
        variant.importFFI(),
        Promise.resolve().then(() => __importStar(require("./module-asyncify.js"))).then(esmHelpers_1.unwrapTypescript),
    ]);
    const wasmModule = await wasmModuleLoader();
    wasmModule.type = "async";
    const ffi = new QuickJSAsyncFFI(wasmModule);
    return new QuickJSAsyncWASMModule(wasmModule, ffi);
}
exports.newQuickJSAsyncWASMModule = newQuickJSAsyncWASMModule;
/**
 * Helper intended to memoize the creation of a WebAssembly module.
 * ```typescript
 * const getDebugModule = memoizePromiseFactory(() => newQuickJSWASMModule(DEBUG_SYNC))
 * ```
 */
function memoizePromiseFactory(fn) {
    let promise;
    return () => {
        return (promise ?? (promise = fn()));
    };
}
exports.memoizePromiseFactory = memoizePromiseFactory;
/**
 * This build variant is compiled with `-fsanitize=leak`. It instruments all
 * memory allocations and when combined with sourcemaps, can present stack trace
 * locations where memory leaks occur.
 *
 * See [[TestQuickJSWASMModule]] which provides access to the leak sanitizer via
 * {@link TestQuickJSWASMModule.assertNoMemoryAllocated}.
 *
 * The downside is that it's 100-1000x slower than the other variants.
 * Suggested use case: automated testing, regression testing, and interactive
 * debugging.
 */
exports.DEBUG_SYNC = {
    type: "sync",
    async importFFI() {
        throw new Error("not implemented");
        // const mod = await import("./generated/ffi.WASM_DEBUG_SYNC.js")
        // return unwrapTypescript(mod).QuickJSFFI
    },
    async importModuleLoader() {
        throw new Error("not implemented");
        // const mod = await import("./generated/emscripten-module.WASM_DEBUG_SYNC.js")
        // return unwrapJavascript(mod).default
    },
};
/**
 * This is the default (synchronous) build variant.
 * {@link getQuickJS} returns a memoized instance of this build variant.
 */
exports.RELEASE_SYNC = {
    type: "sync",
    async importFFI() {
        const mod = await Promise.resolve().then(() => __importStar(require("./generated/ffi.WASM_RELEASE_SYNC.js")));
        return (0, esmHelpers_1.unwrapTypescript)(mod).QuickJSFFI;
    },
    async importModuleLoader() {
        const mod = await Promise.resolve().then(() => __importStar(require("./generated/emscripten-module.WASM_RELEASE_SYNC.js")));
        return (0, esmHelpers_1.unwrapJavascript)(mod);
    },
};
/**
 * The async debug build variant may or may not have the sanitizer enabled.
 * It does print a lot of debug logs.
 *
 * Suggested use case: interactive debugging only.
 */
exports.DEBUG_ASYNC = {
    type: "async",
    async importFFI() {
        throw new Error("not implemented");
        // const mod = await import("./generated/ffi.WASM_DEBUG_ASYNCIFY.js")
        // return unwrapTypescript(mod).QuickJSAsyncFFI
    },
    async importModuleLoader() {
        throw new Error("not implemented");
        // const mod = await import("./generated/emscripten-module.WASM_DEBUG_ASYNCIFY.js")
        // return unwrapJavascript(mod).default
    },
};
/**
 * This is the default asyncified build variant.
 */
exports.RELEASE_ASYNC = {
    type: "async",
    async importFFI() {
        throw new Error("not implemented");
        // const mod = await import("./generated/ffi.WASM_RELEASE_ASYNCIFY.js")
        // return unwrapTypescript(mod).QuickJSAsyncFFI
    },
    async importModuleLoader() {
        throw new Error("not implemented");
        // const mod = await import("./generated/emscripten-module.WASM_RELEASE_ASYNCIFY.js")
        // return unwrapJavascript(mod).default
    },
};
//# sourceMappingURL=variants.js.map