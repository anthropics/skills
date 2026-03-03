declare function awaitYield<T>(value: T | Promise<T>): Generator<T | Promise<T>, T, T>;
declare function awaitYieldOf<T, Yielded>(generator: Generator<Yielded | Promise<Yielded>, T, Yielded>): Generator<T | Promise<T>, T, T>;
export type AwaitYield = typeof awaitYield & {
    of: typeof awaitYieldOf;
};
/**
 * Create a function that may or may not be async, using a generator
 *
 * Within the generator, call `yield* awaited(maybePromise)` to await a value
 * that may or may not be a promise.
 *
 * If the inner function never yields a promise, it will return synchronously.
 */
export declare function maybeAsyncFn<
/** Function arguments */
Args extends any[], This, 
/** Function return type */
Return, 
/** Yields to unwrap */
Yielded>(that: This, fn: (this: This, awaited: AwaitYield, ...args: Args) => Generator<Yielded | Promise<Yielded>, Return, Yielded>): (...args: Args) => Return | Promise<Return>;
export type MaybeAsyncBlock<Return, This, Yielded, Args extends any[] = []> = (this: This, awaited: AwaitYield, ...args: Args) => Generator<Yielded | Promise<Yielded>, Return, Yielded>;
export declare function maybeAsync<Return, This, Yielded>(that: This, startGenerator: (this: This, await: AwaitYield) => Generator<Yielded | Promise<Yielded>, Return, Yielded>): Return | Promise<Return>;
export declare function awaitEachYieldedPromise<Yielded, Returned>(gen: Generator<Yielded | Promise<Yielded>, Returned, Yielded>): Returned | Promise<Returned>;
export {};
