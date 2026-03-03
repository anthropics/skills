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
var __exportStar = (this && this.__exportStar) || function(m, exports) {
    for (var p in m) if (p !== "default" && !Object.prototype.hasOwnProperty.call(exports, p)) __createBinding(exports, m, p);
};
var __importStar = (this && this.__importStar) || function (mod) {
    if (mod && mod.__esModule) return mod;
    var result = {};
    if (mod != null) for (var k in mod) if (k !== "default" && Object.prototype.hasOwnProperty.call(mod, k)) __createBinding(result, mod, k);
    __setModuleDefault(result, mod);
    return result;
};
Object.defineProperty(exports, "__esModule", { value: true });
exports.shouldInterruptAfterDeadline = exports.newAsyncContext = exports.newAsyncRuntime = exports.getQuickJSSync = exports.getQuickJS = exports.errors = exports.RELEASE_SYNC = exports.RELEASE_ASYNC = exports.DEBUG_SYNC = exports.DEBUG_ASYNC = exports.newQuickJSAsyncWASMModule = exports.newQuickJSWASMModule = void 0;
// Build variants
const variants_1 = require("./variants");
Object.defineProperty(exports, "newQuickJSWASMModule", { enumerable: true, get: function () { return variants_1.newQuickJSWASMModule; } });
Object.defineProperty(exports, "newQuickJSAsyncWASMModule", { enumerable: true, get: function () { return variants_1.newQuickJSAsyncWASMModule; } });
Object.defineProperty(exports, "DEBUG_ASYNC", { enumerable: true, get: function () { return variants_1.DEBUG_ASYNC; } });
Object.defineProperty(exports, "DEBUG_SYNC", { enumerable: true, get: function () { return variants_1.DEBUG_SYNC; } });
Object.defineProperty(exports, "RELEASE_ASYNC", { enumerable: true, get: function () { return variants_1.RELEASE_ASYNC; } });
Object.defineProperty(exports, "RELEASE_SYNC", { enumerable: true, get: function () { return variants_1.RELEASE_SYNC; } });
// Export helpers
__exportStar(require("./vm-interface"), exports);
__exportStar(require("./lifetime"), exports);
/** Collects the informative errors this library may throw. */
exports.errors = __importStar(require("./errors"));
__exportStar(require("./deferred-promise"), exports);
__exportStar(require("./module-test"), exports);
let singleton = undefined;
let singletonPromise = undefined;
/**
 * Get a shared singleton {@link QuickJSWASMModule}. Use this to evaluate code
 * or create Javascript environments.
 *
 * This is the top-level entrypoint for the quickjs-emscripten library.
 *
 * If you need strictest possible isolation guarantees, you may create a
 * separate {@link QuickJSWASMModule} via {@link newQuickJSWASMModule}.
 *
 * To work with the asyncified version of this library, see these functions:
 *
 * - {@link newAsyncRuntime}.
 * - {@link newAsyncContext}.
 * - {@link newQuickJSAsyncWASMModule}.
 */
async function getQuickJS() {
    singletonPromise ?? (singletonPromise = (0, variants_1.newQuickJSWASMModule)().then((instance) => {
        singleton = instance;
        return instance;
    }));
    return await singletonPromise;
}
exports.getQuickJS = getQuickJS;
/**
 * Provides synchronous access to the shared {@link QuickJSWASMModule} instance returned by {@link getQuickJS}, as long as
 * least once.
 * @throws If called before `getQuickJS` resolves.
 */
function getQuickJSSync() {
    if (!singleton) {
        throw new Error("QuickJS not initialized. Await getQuickJS() at least once.");
    }
    return singleton;
}
exports.getQuickJSSync = getQuickJSSync;
/**
 * Create a new [[QuickJSAsyncRuntime]] in a separate WebAssembly module.
 *
 * Each runtime is isolated in a separate WebAssembly module, so that errors in
 * one runtime cannot contaminate another runtime, and each runtime can execute
 * an asynchronous action without conflicts.
 *
 * Note that there is a hard limit on the number of WebAssembly modules in older
 * versions of v8:
 * https://bugs.chromium.org/p/v8/issues/detail?id=12076
 */
async function newAsyncRuntime(options) {
    const module = await (0, variants_1.newQuickJSAsyncWASMModule)();
    return module.newRuntime(options);
}
exports.newAsyncRuntime = newAsyncRuntime;
/**
 * Create a new [[QuickJSAsyncContext]] (with an associated runtime) in an
 * separate WebAssembly module.
 *
 * Each context is isolated in a separate WebAssembly module, so that errors in
 * one runtime cannot contaminate another runtime, and each runtime can execute
 * an asynchronous action without conflicts.
 *
 * Note that there is a hard limit on the number of WebAssembly modules in older
 * versions of v8:
 * https://bugs.chromium.org/p/v8/issues/detail?id=12076
 */
async function newAsyncContext(options) {
    const module = await (0, variants_1.newQuickJSAsyncWASMModule)();
    return module.newContext(options);
}
exports.newAsyncContext = newAsyncContext;
/**
 * Returns an interrupt handler that interrupts Javascript execution after a deadline time.
 *
 * @param deadline - Interrupt execution if it's still running after this time.
 *   Number values are compared against `Date.now()`
 */
function shouldInterruptAfterDeadline(deadline) {
    const deadlineAsNumber = typeof deadline === "number" ? deadline : deadline.getTime();
    return function () {
        return Date.now() > deadlineAsNumber;
    };
}
exports.shouldInterruptAfterDeadline = shouldInterruptAfterDeadline;
//# sourceMappingURL=index.js.map