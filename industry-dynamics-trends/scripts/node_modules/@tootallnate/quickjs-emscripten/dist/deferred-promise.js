"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.QuickJSDeferredPromise = void 0;
/**
 * QuickJSDeferredPromise wraps a QuickJS promise [[handle]] and allows
 * [[resolve]]ing or [[reject]]ing that promise. Use it to bridge asynchronous
 * code on the host to APIs inside a QuickJSContext.
 *
 * Managing the lifetime of promises is tricky. There are three
 * [[QuickJSHandle]]s inside of each deferred promise object: (1) the promise
 * itself, (2) the `resolve` callback, and (3) the `reject` callback.
 *
 * - If the promise will be fulfilled before the end of it's [[owner]]'s lifetime,
 *   the only cleanup necessary is `deferred.handle.dispose()`, because
 *   calling [[resolve]] or [[reject]] will dispose of both callbacks automatically.
 *
 * - As the return value of a [[VmFunctionImplementation]], return [[handle]],
 *   and ensure that either [[resolve]] or [[reject]] will be called. No other
 *   clean-up is necessary.
 *
 * - In other cases, call [[dispose]], which will dispose [[handle]] as well as the
 *   QuickJS handles that back [[resolve]] and [[reject]]. For this object,
 *   [[dispose]] is idempotent.
 */
class QuickJSDeferredPromise {
    /**
     * Use [[QuickJSContext.newPromise]] to create a new promise instead of calling
     * this constructor directly.
     * @unstable
     */
    constructor(args) {
        /**
         * Resolve [[handle]] with the given value, if any.
         * Calling this method after calling [[dispose]] is a no-op.
         *
         * Note that after resolving a promise, you may need to call
         * [[QuickJSContext.executePendingJobs]] to propagate the result to the promise's
         * callbacks.
         */
        this.resolve = (value) => {
            if (!this.resolveHandle.alive) {
                return;
            }
            this.context
                .unwrapResult(this.context.callFunction(this.resolveHandle, this.context.undefined, value || this.context.undefined))
                .dispose();
            this.disposeResolvers();
            this.onSettled();
        };
        /**
         * Reject [[handle]] with the given value, if any.
         * Calling this method after calling [[dispose]] is a no-op.
         *
         * Note that after rejecting a promise, you may need to call
         * [[QuickJSContext.executePendingJobs]] to propagate the result to the promise's
         * callbacks.
         */
        this.reject = (value) => {
            if (!this.rejectHandle.alive) {
                return;
            }
            this.context
                .unwrapResult(this.context.callFunction(this.rejectHandle, this.context.undefined, value || this.context.undefined))
                .dispose();
            this.disposeResolvers();
            this.onSettled();
        };
        this.dispose = () => {
            if (this.handle.alive) {
                this.handle.dispose();
            }
            this.disposeResolvers();
        };
        this.context = args.context;
        this.owner = args.context.runtime;
        this.handle = args.promiseHandle;
        this.settled = new Promise((resolve) => {
            this.onSettled = resolve;
        });
        this.resolveHandle = args.resolveHandle;
        this.rejectHandle = args.rejectHandle;
    }
    get alive() {
        return this.handle.alive || this.resolveHandle.alive || this.rejectHandle.alive;
    }
    disposeResolvers() {
        if (this.resolveHandle.alive) {
            this.resolveHandle.dispose();
        }
        if (this.rejectHandle.alive) {
            this.rejectHandle.dispose();
        }
    }
}
exports.QuickJSDeferredPromise = QuickJSDeferredPromise;
//# sourceMappingURL=deferred-promise.js.map