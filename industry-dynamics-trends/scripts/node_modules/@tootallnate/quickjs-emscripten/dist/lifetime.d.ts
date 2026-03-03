import { MaybeAsyncBlock } from "./asyncify-helpers";
import type { QuickJSHandle } from "./types";
/**
 * An object that can be disposed.
 * [[Lifetime]] is the canonical implementation of Disposable.
 * Use [[Scope]] to manage cleaning up multiple disposables.
 */
export interface Disposable {
    /**
     * Dispose of the underlying resources used by this object.
     */
    dispose(): void;
    /**
     * @returns true if the object is alive
     * @returns false after the object has been [[dispose]]d
     */
    alive: boolean;
}
/**
 * A lifetime prevents access to a value after the lifetime has been
 * [[dispose]]ed.
 *
 * Typically, quickjs-emscripten uses Lifetimes to protect C memory pointers.
 */
export declare class Lifetime<T, TCopy = never, Owner = never> implements Disposable {
    protected readonly _value: T;
    protected readonly copier?: ((value: T | TCopy) => TCopy) | undefined;
    protected readonly disposer?: ((value: T | TCopy) => void) | undefined;
    protected readonly _owner?: Owner | undefined;
    protected _alive: boolean;
    protected _constructorStack: string | undefined;
    /**
     * When the Lifetime is disposed, it will call `disposer(_value)`. Use the
     * disposer function to implement whatever cleanup needs to happen at the end
     * of `value`'s lifetime.
     *
     * `_owner` is not used or controlled by the lifetime. It's just metadata for
     * the creator.
     */
    constructor(_value: T, copier?: ((value: T | TCopy) => TCopy) | undefined, disposer?: ((value: T | TCopy) => void) | undefined, _owner?: Owner | undefined);
    get alive(): boolean;
    /**
     * The value this Lifetime protects. You must never retain the value - it
     * may become invalid, leading to memory errors.
     *
     * @throws If the lifetime has been [[dispose]]d already.
     */
    get value(): T;
    get owner(): Owner | undefined;
    get dupable(): boolean;
    /**
     * Create a new handle pointing to the same [[value]].
     */
    dup(): Lifetime<TCopy, TCopy, Owner>;
    /**
     * Call `map` with this lifetime, then dispose the lifetime.
     * @return the result of `map(this)`.
     */
    consume<O>(map: (lifetime: this) => O): O;
    consume<O>(map: (lifetime: QuickJSHandle) => O): O;
    /**
     * Dispose of [[value]] and perform cleanup.
     */
    dispose(): void;
    private assertAlive;
}
/**
 * A Lifetime that lives forever. Used for constants.
 */
export declare class StaticLifetime<T, Owner = never> extends Lifetime<T, T, Owner> {
    constructor(value: T, owner?: Owner);
    get dupable(): boolean;
    dup(): this;
    dispose(): void;
}
/**
 * A Lifetime that does not own its `value`. A WeakLifetime never calls its
 * `disposer` function, but can be `dup`ed to produce regular lifetimes that
 * do.
 *
 * Used for function arguments.
 */
export declare class WeakLifetime<T, TCopy = never, Owner = never> extends Lifetime<T, TCopy, Owner> {
    constructor(value: T, copier?: (value: T | TCopy) => TCopy, disposer?: (value: TCopy) => void, owner?: Owner);
    dispose(): void;
}
/**
 * Scope helps reduce the burden of manually tracking and disposing of
 * Lifetimes. See [[withScope]]. and [[withScopeAsync]].
 */
export declare class Scope implements Disposable {
    /**
     * Run `block` with a new Scope instance that will be disposed after the block returns.
     * Inside `block`, call `scope.manage` on each lifetime you create to have the lifetime
     * automatically disposed after the block returns.
     *
     * @warning Do not use with async functions. Instead, use [[withScopeAsync]].
     */
    static withScope<R>(block: (scope: Scope) => R): R;
    static withScopeMaybeAsync<Return, This, Yielded>(_this: This, block: MaybeAsyncBlock<Return, This, Yielded, [Scope]>): Return | Promise<Return>;
    /**
     * Run `block` with a new Scope instance that will be disposed after the
     * block's returned promise settles. Inside `block`, call `scope.manage` on each
     * lifetime you create to have the lifetime automatically disposed after the
     * block returns.
     */
    static withScopeAsync<R>(block: (scope: Scope) => Promise<R>): Promise<R>;
    private _disposables;
    /**
     * Track `lifetime` so that it is disposed when this scope is disposed.
     */
    manage<T extends Disposable>(lifetime: T): T;
    get alive(): boolean;
    dispose(): void;
}
