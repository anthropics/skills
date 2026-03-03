"use strict";
/**
 * @license
 * Copyright 2023 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
Object.defineProperty(exports, "__esModule", { value: true });
exports.SuppressedError = exports.AsyncDisposableStack = exports.AsyncDisposableStackPolyfill = exports.DisposableStack = exports.DisposableStackPolyfill = exports.asyncDisposeSymbol = exports.disposeSymbol = void 0;
Symbol.dispose ??= Symbol('dispose');
Symbol.asyncDispose ??= Symbol('asyncDispose');
/**
 * @internal
 */
exports.disposeSymbol = Symbol.dispose;
/**
 * @internal
 */
exports.asyncDisposeSymbol = Symbol.asyncDispose;
/**
 * @internal
 */
class DisposableStackPolyfill {
    #disposed = false;
    #stack = [];
    /**
     * Returns a value indicating whether the stack has been disposed.
     */
    get disposed() {
        return this.#disposed;
    }
    /**
     * Alias for `[Symbol.dispose]()`.
     */
    dispose() {
        this[exports.disposeSymbol]();
    }
    /**
     * Adds a disposable resource to the top of stack, returning the resource.
     * Has no effect if provided `null` or `undefined`.
     *
     * @param value - A `Disposable` object, `null`, or `undefined`.
     * `null` and `undefined` will not be added, but will be returned.
     * @returns The provided `value`.
     */
    use(value) {
        if (value && typeof value[exports.disposeSymbol] === 'function') {
            this.#stack.push(value);
        }
        return value;
    }
    /**
     * Adds a non-disposable resource and a disposal callback to the top of the stack.
     *
     * @param value - A resource to be disposed.
     * @param onDispose - A callback invoked to dispose the provided value.
     * Will be invoked with `value` as the first parameter.
     * @returns The provided `value`.
     */
    adopt(value, onDispose) {
        this.#stack.push({
            [exports.disposeSymbol]() {
                onDispose(value);
            },
        });
        return value;
    }
    /**
     * Add a disposal callback to the top of the stack to be invoked when stack is disposed.
     * @param onDispose - A callback to invoke when this object is disposed.
     */
    defer(onDispose) {
        this.#stack.push({
            [exports.disposeSymbol]() {
                onDispose();
            },
        });
    }
    /**
     * Move all resources out of this stack and into a new `DisposableStack`, and
     * marks this stack as disposed.
     * @returns The new `DisposableStack`.
     *
     * @example
     *
     * ```ts
     * class C {
     *   #res1: Disposable;
     *   #res2: Disposable;
     *   #disposables: DisposableStack;
     *   constructor() {
     *     // stack will be disposed when exiting constructor for any reason
     *     using stack = new DisposableStack();
     *
     *     // get first resource
     *     this.#res1 = stack.use(getResource1());
     *
     *     // get second resource. If this fails, both `stack` and `#res1` will be disposed.
     *     this.#res2 = stack.use(getResource2());
     *
     *     // all operations succeeded, move resources out of `stack` so that
     *     // they aren't disposed when constructor exits
     *     this.#disposables = stack.move();
     *   }
     *
     *   [disposeSymbol]() {
     *     this.#disposables.dispose();
     *   }
     * }
     * ```
     */
    move() {
        if (this.#disposed) {
            throw new ReferenceError('A disposed stack can not use anything new');
        }
        const stack = new DisposableStackPolyfill();
        stack.#stack = this.#stack;
        this.#stack = [];
        this.#disposed = true;
        return stack;
    }
    /**
     * Disposes each resource in the stack in last-in-first-out (LIFO) manner.
     */
    [exports.disposeSymbol]() {
        if (this.#disposed) {
            return;
        }
        this.#disposed = true;
        const errors = [];
        for (const resource of this.#stack.reverse()) {
            try {
                resource[exports.disposeSymbol]();
            }
            catch (e) {
                errors.push(e);
            }
        }
        if (errors.length === 1) {
            throw errors[0];
        }
        else if (errors.length > 1) {
            let suppressed = null;
            for (const error of errors) {
                if (suppressed === null) {
                    suppressed = error;
                }
                else {
                    suppressed = new SuppressedErrorPolyfill(error, suppressed);
                }
            }
            throw suppressed;
        }
    }
    [Symbol.toStringTag] = 'DisposableStack';
}
exports.DisposableStackPolyfill = DisposableStackPolyfill;
/**
 * @internal
 */
exports.DisposableStack = globalThis.DisposableStack ?? DisposableStackPolyfill;
/**
 * @internal
 */
class AsyncDisposableStackPolyfill {
    #disposed = false;
    #stack = [];
    /**
     * Returns a value indicating whether the stack has been disposed.
     */
    get disposed() {
        return this.#disposed;
    }
    /**
     * Alias for `[Symbol.asyncDispose]()`.
     */
    async disposeAsync() {
        await this[exports.asyncDisposeSymbol]();
    }
    /**
     * Adds a AsyncDisposable resource to the top of stack, returning the resource.
     * Has no effect if provided `null` or `undefined`.
     *
     * @param value - A `AsyncDisposable` object, `null`, or `undefined`.
     * `null` and `undefined` will not be added, but will be returned.
     * @returns The provided `value`.
     */
    use(value) {
        if (value) {
            const asyncDispose = value[exports.asyncDisposeSymbol];
            const dispose = value[exports.disposeSymbol];
            if (typeof asyncDispose === 'function') {
                this.#stack.push(value);
            }
            else if (typeof dispose === 'function') {
                this.#stack.push({
                    [exports.asyncDisposeSymbol]: async () => {
                        value[exports.disposeSymbol]();
                    },
                });
            }
        }
        return value;
    }
    /**
     * Adds a non-disposable resource and a disposal callback to the top of the stack.
     *
     * @param value - A resource to be disposed.
     * @param onDispose - A callback invoked to dispose the provided value.
     * Will be invoked with `value` as the first parameter.
     * @returns The provided `value`.
     */
    adopt(value, onDispose) {
        this.#stack.push({
            [exports.asyncDisposeSymbol]() {
                return onDispose(value);
            },
        });
        return value;
    }
    /**
     * Add a disposal callback to the top of the stack to be invoked when stack is disposed.
     * @param onDispose - A callback to invoke when this object is disposed.
     */
    defer(onDispose) {
        this.#stack.push({
            [exports.asyncDisposeSymbol]() {
                return onDispose();
            },
        });
    }
    /**
     * Move all resources out of this stack and into a new `DisposableStack`, and
     * marks this stack as disposed.
     * @returns The new `AsyncDisposableStack`.
     *
     * @example
     *
     * ```ts
     * class C {
     *   #res1: Disposable;
     *   #res2: Disposable;
     *   #disposables: DisposableStack;
     *   constructor() {
     *     // stack will be disposed when exiting constructor for any reason
     *     using stack = new DisposableStack();
     *
     *     // get first resource
     *     this.#res1 = stack.use(getResource1());
     *
     *     // get second resource. If this fails, both `stack` and `#res1` will be disposed.
     *     this.#res2 = stack.use(getResource2());
     *
     *     // all operations succeeded, move resources out of `stack` so that
     *     // they aren't disposed when constructor exits
     *     this.#disposables = stack.move();
     *   }
     *
     *   [disposeSymbol]() {
     *     this.#disposables.dispose();
     *   }
     * }
     * ```
     */
    move() {
        if (this.#disposed) {
            throw new ReferenceError('A disposed stack can not use anything new');
        }
        const stack = new AsyncDisposableStackPolyfill();
        stack.#stack = this.#stack;
        this.#stack = [];
        this.#disposed = true;
        return stack;
    }
    /**
     * Disposes each resource in the stack in last-in-first-out (LIFO) manner.
     */
    async [exports.asyncDisposeSymbol]() {
        if (this.#disposed) {
            return;
        }
        this.#disposed = true;
        const errors = [];
        for (const resource of this.#stack.reverse()) {
            try {
                await resource[exports.asyncDisposeSymbol]();
            }
            catch (e) {
                errors.push(e);
            }
        }
        if (errors.length === 1) {
            throw errors[0];
        }
        else if (errors.length > 1) {
            let suppressed = null;
            for (const error of errors) {
                if (suppressed === null) {
                    suppressed = error;
                }
                else {
                    suppressed = new SuppressedErrorPolyfill(error, suppressed);
                }
            }
            throw suppressed;
        }
    }
    [Symbol.toStringTag] = 'AsyncDisposableStack';
}
exports.AsyncDisposableStackPolyfill = AsyncDisposableStackPolyfill;
/**
 * @internal
 */
exports.AsyncDisposableStack = globalThis.AsyncDisposableStack ?? AsyncDisposableStackPolyfill;
/**
 * @internal
 * Represents an error that occurs when multiple errors are thrown during
 * the disposal of resources. This class encapsulates the primary error and
 * any suppressed errors that occurred subsequently.
 */
class SuppressedErrorPolyfill extends Error {
    #error;
    #suppressed;
    constructor(error, suppressed, message = 'An error was suppressed during disposal') {
        super(message);
        this.name = 'SuppressedError';
        this.#error = error;
        this.#suppressed = suppressed;
    }
    /**
     * The primary error that occurred during disposal.
     */
    get error() {
        return this.#error;
    }
    /**
     * The suppressed error i.e. the error that was suppressed
     * because it occurred later in the flow after the original error.
     */
    get suppressed() {
        return this.#suppressed;
    }
}
/**
 * @internal
 */
exports.SuppressedError = globalThis.SuppressedError ?? SuppressedErrorPolyfill;
//# sourceMappingURL=disposable.js.map