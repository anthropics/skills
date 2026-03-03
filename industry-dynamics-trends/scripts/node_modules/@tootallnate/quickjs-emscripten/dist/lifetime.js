"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.Scope = exports.WeakLifetime = exports.StaticLifetime = exports.Lifetime = void 0;
const asyncify_helpers_1 = require("./asyncify-helpers");
const debug_1 = require("./debug");
const errors_1 = require("./errors");
/**
 * A lifetime prevents access to a value after the lifetime has been
 * [[dispose]]ed.
 *
 * Typically, quickjs-emscripten uses Lifetimes to protect C memory pointers.
 */
class Lifetime {
    /**
     * When the Lifetime is disposed, it will call `disposer(_value)`. Use the
     * disposer function to implement whatever cleanup needs to happen at the end
     * of `value`'s lifetime.
     *
     * `_owner` is not used or controlled by the lifetime. It's just metadata for
     * the creator.
     */
    constructor(_value, copier, disposer, _owner) {
        this._value = _value;
        this.copier = copier;
        this.disposer = disposer;
        this._owner = _owner;
        this._alive = true;
        this._constructorStack = debug_1.QTS_DEBUG ? new Error("Lifetime constructed").stack : undefined;
    }
    get alive() {
        return this._alive;
    }
    /**
     * The value this Lifetime protects. You must never retain the value - it
     * may become invalid, leading to memory errors.
     *
     * @throws If the lifetime has been [[dispose]]d already.
     */
    get value() {
        this.assertAlive();
        return this._value;
    }
    get owner() {
        return this._owner;
    }
    get dupable() {
        return !!this.copier;
    }
    /**
     * Create a new handle pointing to the same [[value]].
     */
    dup() {
        this.assertAlive();
        if (!this.copier) {
            throw new Error("Non-dupable lifetime");
        }
        return new Lifetime(this.copier(this._value), this.copier, this.disposer, this._owner);
    }
    consume(map) {
        this.assertAlive();
        const result = map(this);
        this.dispose();
        return result;
    }
    /**
     * Dispose of [[value]] and perform cleanup.
     */
    dispose() {
        this.assertAlive();
        if (this.disposer) {
            this.disposer(this._value);
        }
        this._alive = false;
    }
    assertAlive() {
        if (!this.alive) {
            if (this._constructorStack) {
                throw new errors_1.QuickJSUseAfterFree(`Lifetime not alive\n${this._constructorStack}\nLifetime used`);
            }
            throw new errors_1.QuickJSUseAfterFree("Lifetime not alive");
        }
    }
}
exports.Lifetime = Lifetime;
/**
 * A Lifetime that lives forever. Used for constants.
 */
class StaticLifetime extends Lifetime {
    constructor(value, owner) {
        super(value, undefined, undefined, owner);
    }
    // Static lifetime doesn't need a copier to be copiable
    get dupable() {
        return true;
    }
    // Copy returns the same instance.
    dup() {
        return this;
    }
    // Dispose does nothing.
    dispose() { }
}
exports.StaticLifetime = StaticLifetime;
/**
 * A Lifetime that does not own its `value`. A WeakLifetime never calls its
 * `disposer` function, but can be `dup`ed to produce regular lifetimes that
 * do.
 *
 * Used for function arguments.
 */
class WeakLifetime extends Lifetime {
    constructor(value, copier, disposer, owner) {
        // We don't care if the disposer doesn't support freeing T
        super(value, copier, disposer, owner);
    }
    dispose() {
        this._alive = false;
    }
}
exports.WeakLifetime = WeakLifetime;
function scopeFinally(scope, blockError) {
    // console.log('scopeFinally', scope, blockError)
    let disposeError;
    try {
        scope.dispose();
    }
    catch (error) {
        disposeError = error;
    }
    if (blockError && disposeError) {
        Object.assign(blockError, {
            message: `${blockError.message}\n Then, failed to dispose scope: ${disposeError.message}`,
            disposeError,
        });
        throw blockError;
    }
    if (blockError || disposeError) {
        throw blockError || disposeError;
    }
}
/**
 * Scope helps reduce the burden of manually tracking and disposing of
 * Lifetimes. See [[withScope]]. and [[withScopeAsync]].
 */
class Scope {
    constructor() {
        this._disposables = new Lifetime(new Set());
    }
    /**
     * Run `block` with a new Scope instance that will be disposed after the block returns.
     * Inside `block`, call `scope.manage` on each lifetime you create to have the lifetime
     * automatically disposed after the block returns.
     *
     * @warning Do not use with async functions. Instead, use [[withScopeAsync]].
     */
    static withScope(block) {
        const scope = new Scope();
        let blockError;
        try {
            return block(scope);
        }
        catch (error) {
            blockError = error;
            throw error;
        }
        finally {
            scopeFinally(scope, blockError);
        }
    }
    static withScopeMaybeAsync(_this, block) {
        return (0, asyncify_helpers_1.maybeAsync)(undefined, function* (awaited) {
            const scope = new Scope();
            let blockError;
            try {
                return yield* awaited.of(block.call(_this, awaited, scope));
            }
            catch (error) {
                blockError = error;
                throw error;
            }
            finally {
                scopeFinally(scope, blockError);
            }
        });
    }
    /**
     * Run `block` with a new Scope instance that will be disposed after the
     * block's returned promise settles. Inside `block`, call `scope.manage` on each
     * lifetime you create to have the lifetime automatically disposed after the
     * block returns.
     */
    static async withScopeAsync(block) {
        const scope = new Scope();
        let blockError;
        try {
            return await block(scope);
        }
        catch (error) {
            blockError = error;
            throw error;
        }
        finally {
            scopeFinally(scope, blockError);
        }
    }
    /**
     * Track `lifetime` so that it is disposed when this scope is disposed.
     */
    manage(lifetime) {
        this._disposables.value.add(lifetime);
        return lifetime;
    }
    get alive() {
        return this._disposables.alive;
    }
    dispose() {
        const lifetimes = Array.from(this._disposables.value.values()).reverse();
        for (const lifetime of lifetimes) {
            if (lifetime.alive) {
                lifetime.dispose();
            }
        }
        this._disposables.dispose();
    }
}
exports.Scope = Scope;
//# sourceMappingURL=lifetime.js.map