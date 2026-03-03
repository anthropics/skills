// Project: https://github.com/isaacs/node-lru-cache
// Based initially on @types/lru-cache
// https://github.com/DefinitelyTyped/DefinitelyTyped
// used under the terms of the MIT License, shown below.
//
// DefinitelyTyped license:
// ------
// MIT License
//
// Copyright (c) Microsoft Corporation.
//
// Permission is hereby granted, free of charge, to any person obtaining a
// copy of this software and associated documentation files (the "Software"),
// to deal in the Software without restriction, including without limitation
// the rights to use, copy, modify, merge, publish, distribute, sublicense,
// and/or sell copies of the Software, and to permit persons to whom the
// Software is furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included
// in all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
// EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
// MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
// IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
// CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
// TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
// SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE
// ------
//
// Changes by Isaac Z. Schlueter released under the terms found in the
// LICENSE file within this project.

/**
 * Integer greater than 0, representing some number of milliseconds, or the
 * time at which a TTL started counting from.
 */
declare type LRUMilliseconds = number

/**
 * An integer greater than 0, reflecting the calculated size of items
 */
declare type LRUSize = number

/**
 * An integer greater than 0, reflecting a number of items
 */
declare type LRUCount = number

declare class LRUCache<K, V> implements Iterable<[K, V]> {
  constructor(options: LRUCache.Options<K, V>)

  /**
   * Number of items in the cache.
   * Alias for {@link size}
   *
   * @deprecated since 7.0 use {@link size} instead
   */
  public readonly length: LRUCount

  public readonly max: LRUCount
  public readonly maxSize: LRUSize
  public readonly maxEntrySize: LRUSize
  public readonly sizeCalculation:
    | LRUCache.SizeCalculator<K, V>
    | undefined
  public readonly dispose: LRUCache.Disposer<K, V>
  /**
   * @since 7.4.0
   */
  public readonly disposeAfter: LRUCache.Disposer<K, V> | null
  public readonly noDisposeOnSet: boolean
  public readonly ttl: LRUMilliseconds
  public readonly ttlResolution: LRUMilliseconds
  public readonly ttlAutopurge: boolean
  public readonly allowStale: boolean
  public readonly updateAgeOnGet: boolean
  /**
   * @since 7.11.0
   */
  public readonly noDeleteOnStaleGet: boolean
  /**
   * @since 7.6.0
   */
  public readonly fetchMethod: LRUCache.Fetcher<K, V> | null

  /**
   * The total number of items held in the cache at the current moment.
   */
  public readonly size: LRUCount

  /**
   * The total size of items in cache when using size tracking.
   */
  public readonly calculatedSize: LRUSize

  /**
   * Add a value to the cache.
   */
  public set(
    key: K,
    value: V,
    options?: LRUCache.SetOptions<K, V>
  ): this

  /**
   * Return a value from the cache. Will update the recency of the cache entry
   * found.
   *
   * If the key is not found, {@link get} will return `undefined`. This can be
   * confusing when setting values specifically to `undefined`, as in
   * `cache.set(key, undefined)`. Use {@link has} to determine whether a key is
   * present in the cache at all.
   */
  public get(key: K, options?: LRUCache.GetOptions<V>): V | undefined

  /**
   * Like {@link get} but doesn't update recency or delete stale items.
   * Returns `undefined` if the item is stale, unless {@link allowStale} is set
   * either on the cache or in the options object.
   */
  public peek(key: K, options?: LRUCache.PeekOptions): V | undefined

  /**
   * Check if a key is in the cache, without updating the recency of use.
   * Will return false if the item is stale, even though it is technically
   * in the cache.
   *
   * Will not update item age unless {@link updateAgeOnHas} is set in the
   * options or constructor.
   */
  public has(key: K, options?: LRUCache.HasOptions<V>): boolean

  /**
   * Deletes a key out of the cache.
   * Returns true if the key was deleted, false otherwise.
   */
  public delete(key: K): boolean

  /**
   * Clear the cache entirely, throwing away all values.
   */
  public clear(): void

  /**
   * Delete any stale entries. Returns true if anything was removed, false
   * otherwise.
   */
  public purgeStale(): boolean

  /**
   * Find a value for which the supplied fn method returns a truthy value,
   * similar to Array.find().  fn is called as fn(value, key, cache).
   */
  public find(
    callbackFn: (
      value: V,
      key: K,
      cache: this
    ) => boolean | undefined | void,
    options?: LRUCache.GetOptions<V>
  ): V | undefined

  /**
   * Call the supplied function on each item in the cache, in order from
   * most recently used to least recently used.  fn is called as
   * fn(value, key, cache).  Does not update age or recenty of use.
   */
  public forEach<T = this>(
    callbackFn: (this: T, value: V, key: K, cache: this) => void,
    thisArg?: T
  ): void

  /**
   * The same as {@link forEach} but items are iterated over in reverse
   * order.  (ie, less recently used items are iterated over first.)
   */
  public rforEach<T = this>(
    callbackFn: (this: T, value: V, key: K, cache: this) => void,
    thisArg?: T
  ): void

  /**
   * Return a generator yielding the keys in the cache,
   * in order from most recently used to least recently used.
   */
  public keys(): Generator<K, void, void>

  /**
   * Inverse order version of {@link keys}
   *
   * Return a generator yielding the keys in the cache,
   * in order from least recently used to most recently used.
   */
  public rkeys(): Generator<K, void, void>

  /**
   * Return a generator yielding the values in the cache,
   * in order from most recently used to least recently used.
   */
  public values(): Generator<V, void, void>

  /**
   * Inverse order version of {@link values}
   *
   * Return a generator yielding the values in the cache,
   * in order from least recently used to most recently used.
   */
  public rvalues(): Generator<V, void, void>

  /**
   * Return a generator yielding `[key, value]` pairs,
   * in order from most recently used to least recently used.
   */
  public entries(): Generator<[K, V], void, void>

  /**
   * Inverse order version of {@link entries}
   *
   * Return a generator yielding `[key, value]` pairs,
   * in order from least recently used to most recently used.
   */
  public rentries(): Generator<[K, V], void, void>

  /**
   * Iterating over the cache itself yields the same results as
   * {@link entries}
   */
  public [Symbol.iterator](): Generator<[K, V], void, void>

  /**
   * Return an array of [key, entry] objects which can be passed to
   * cache.load()
   */
  public dump(): Array<[K, LRUCache.Entry<V>]>

  /**
   * Reset the cache and load in the items in entries in the order listed.
   * Note that the shape of the resulting cache may be different if the
   * same options are not used in both caches.
   */
  public load(
    cacheEntries: ReadonlyArray<[K, LRUCache.Entry<V>]>
  ): void

  /**
   * Evict the least recently used item, returning its value or `undefined`
   * if cache is empty.
   */
  public pop(): V | undefined

  /**
   * Deletes a key out of the cache.
   *
   * @deprecated since 7.0 use delete() instead
   */
  public del(key: K): boolean

  /**
   * Clear the cache entirely, throwing away all values.
   *
   * @deprecated since 7.0 use clear() instead
   */
  public reset(): void

  /**
   * Manually iterates over the entire cache proactively pruning old entries.
   *
   * @deprecated since 7.0 use purgeStale() instead
   */
  public prune(): boolean

  /**
   * Make an asynchronous cached fetch using the {@link fetchMethod} function.
   *
   * If multiple fetches for the same key are issued, then they will all be
   * coalesced into a single call to fetchMethod.
   *
   * Note that this means that handling options such as
   * {@link allowStaleOnFetchAbort}, {@link signal}, and
   * {@link allowStaleOnFetchRejection} will be determined by the FIRST fetch()
   * call for a given key.
   *
   * This is a known (fixable) shortcoming which will be addresed on when
   * someone complains about it, as the fix would involve added complexity and
   * may not be worth the costs for this edge case.
   *
   * since: 7.6.0
   */
  public fetch(
    key: K,
    options?: LRUCache.FetchOptions<K, V>
  ): Promise<V>

  /**
   * since: 7.6.0
   */
  public getRemainingTTL(key: K): LRUMilliseconds
}

declare namespace LRUCache {
  type DisposeReason = 'evict' | 'set' | 'delete'

  type SizeCalculator<K, V> = (value: V, key: K) => LRUSize
  type Disposer<K, V> = (
    value: V,
    key: K,
    reason: DisposeReason
  ) => void
  type Fetcher<K, V> = (
    key: K,
    staleValue: V | undefined,
    options: FetcherOptions<K, V>
  ) => Promise<V | void | undefined> | V | void | undefined

  interface DeprecatedOptions<K, V> {
    /**
     * alias for ttl
     *
     * @deprecated since 7.0 use options.ttl instead
     */
    maxAge?: LRUMilliseconds

    /**
     * alias for {@link sizeCalculation}
     *
     * @deprecated since 7.0 use {@link sizeCalculation} instead
     */
    length?: SizeCalculator<K, V>

    /**
     * alias for allowStale
     *
     * @deprecated since 7.0 use options.allowStale instead
     */
    stale?: boolean
  }

  interface LimitedByCount {
    /**
     * The number of most recently used items to keep.
     * Note that we may store fewer items than this if maxSize is hit.
     */
    max: LRUCount
  }

  type MaybeMaxEntrySizeLimit<K, V> =
    | {
        /**
         * The maximum allowed size for any single item in the cache.
         *
         * If a larger item is passed to {@link set} or returned by a
         * {@link fetchMethod}, then it will not be stored in the cache.
         */
        maxEntrySize: LRUSize
        sizeCalculation?: SizeCalculator<K, V>
      }
    | {}

  interface LimitedBySize<K, V> {
    /**
     * If you wish to track item size, you must provide a maxSize
     * note that we still will only keep up to max *actual items*,
     * if max is set, so size tracking may cause fewer than max items
     * to be stored.  At the extreme, a single item of maxSize size
     * will cause everything else in the cache to be dropped when it
     * is added.  Use with caution!
     *
     * Note also that size tracking can negatively impact performance,
     * though for most cases, only minimally.
     */
    maxSize: LRUSize

    /**
     * Function to calculate size of items.  Useful if storing strings or
     * buffers or other items where memory size depends on the object itself.
     *
     * Items larger than {@link maxEntrySize} will not be stored in the cache.
     *
     * Note that when {@link maxSize} or {@link maxEntrySize} are set, every
     * item added MUST have a size specified, either via a `sizeCalculation` in
     * the constructor, or `sizeCalculation` or {@link size} options to
     * {@link set}.
     */
    sizeCalculation?: SizeCalculator<K, V>
  }

  interface LimitedByTTL {
    /**
     * Max time in milliseconds for items to live in cache before they are
     * considered stale.  Note that stale items are NOT preemptively removed
     * by default, and MAY live in the cache, contributing to its LRU max,
     * long after they have expired.
     *
     * Also, as this cache is optimized for LRU/MRU operations, some of
     * the staleness/TTL checks will reduce performance, as they will incur
     * overhead by deleting items.
     *
     * Must be an integer number of ms, defaults to 0, which means "no TTL"
     */
    ttl: LRUMilliseconds

    /**
     * Boolean flag to tell the cache to not update the TTL when
     * setting a new value for an existing key (ie, when updating a value
     * rather than inserting a new value).  Note that the TTL value is
     * _always_ set (if provided) when adding a new entry into the cache.
     *
     * @default false
     * @since 7.4.0
     */
    noUpdateTTL?: boolean

    /**
     * Minimum amount of time in ms in which to check for staleness.
     * Defaults to 1, which means that the current time is checked
     * at most once per millisecond.
     *
     * Set to 0 to check the current time every time staleness is tested.
     * (This reduces performance, and is theoretically unnecessary.)
     *
     * Setting this to a higher value will improve performance somewhat
     * while using ttl tracking, albeit at the expense of keeping stale
     * items around a bit longer than their TTLs would indicate.
     *
     * @default 1
     * @since 7.1.0
     */
    ttlResolution?: LRUMilliseconds

    /**
     * Preemptively remove stale items from the cache.
     * Note that this may significantly degrade performance,
     * especially if the cache is storing a large number of items.
     * It is almost always best to just leave the stale items in
     * the cache, and let them fall out as new items are added.
     *
     * Note that this means that {@link allowStale} is a bit pointless,
     * as stale items will be deleted almost as soon as they expire.
     *
     * Use with caution!
     *
     * @default false
     * @since 7.1.0
     */
    ttlAutopurge?: boolean

    /**
     * Return stale items from {@link get} before disposing of them.
     * Return stale values from {@link fetch} while performing a call
     * to the {@link fetchMethod} in the background.
     *
     * @default false
     */
    allowStale?: boolean

    /**
     * Update the age of items on {@link get}, renewing their TTL
     *
     * @default false
     */
    updateAgeOnGet?: boolean

    /**
     * Do not delete stale items when they are retrieved with {@link get}.
     * Note that the {@link get} return value will still be `undefined` unless
     * allowStale is true.
     *
     * @default false
     * @since 7.11.0
     */
    noDeleteOnStaleGet?: boolean

    /**
     * Update the age of items on {@link has}, renewing their TTL
     *
     * @default false
     */
    updateAgeOnHas?: boolean
  }

  type SafetyBounds<K, V> =
    | LimitedByCount
    | LimitedBySize<K, V>
    | LimitedByTTL

  // options shared by all three of the limiting scenarios
  interface SharedOptions<K, V> {
    /**
     * Function that is called on items when they are dropped from the cache.
     * This can be handy if you want to close file descriptors or do other
     * cleanup tasks when items are no longer accessible. Called with `key,
     * value`.  It's called before actually removing the item from the
     * internal cache, so it is *NOT* safe to re-add them.
     * Use {@link disposeAfter} if you wish to dispose items after they have
     * been full removed, when it is safe to add them back to the cache.
     */
    dispose?: Disposer<K, V>

    /**
     * The same as dispose, but called *after* the entry is completely
     * removed and the cache is once again in a clean state.  It is safe to
     * add an item right back into the cache at this point.
     * However, note that it is *very* easy to inadvertently create infinite
     * recursion this way.
     *
     * @since 7.3.0
     */
    disposeAfter?: Disposer<K, V>

    /**
     * Set to true to suppress calling the dispose() function if the entry
     * key is still accessible within the cache.
     * This may be overridden by passing an options object to {@link set}.
     *
     * @default false
     */
    noDisposeOnSet?: boolean

    /**
     * Function that is used to make background asynchronous fetches.  Called
     * with `fetchMethod(key, staleValue, { signal, options, context })`.
     *
     * If `fetchMethod` is not provided, then {@link fetch} is
     * equivalent to `Promise.resolve(cache.get(key))`.
     *
     * The `fetchMethod` should ONLY return `undefined` in cases where the
     * abort controller has sent an abort signal.
     *
     * @since 7.6.0
     */
    fetchMethod?: LRUCache.Fetcher<K, V>

    /**
     * Set to true to suppress the deletion of stale data when a
     * {@link fetchMethod} throws an error or returns a rejected promise
     *
     * This may be overridden in the {@link fetchMethod}.
     *
     * @default false
     * @since 7.10.0
     */
    noDeleteOnFetchRejection?: boolean

    /**
     * Set to true to allow returning stale data when a {@link fetchMethod}
     * throws an error or returns a rejected promise. Note that this
     * differs from using {@link allowStale} in that stale data will
     * ONLY be returned in the case that the fetch fails, not any other
     * times.
     *
     * This may be overridden in the {@link fetchMethod}.
     *
     * @default false
     * @since 7.16.0
     */
    allowStaleOnFetchRejection?: boolean

    /**
     *
     * Set to true to ignore the `abort` event emitted by the `AbortSignal`
     * object passed to {@link fetchMethod}, and still cache the
     * resulting resolution value, as long as it is not `undefined`.
     *
     * When used on its own, this means aborted {@link fetch} calls are not
     * immediately resolved or rejected when they are aborted, and instead take
     * the full time to await.
     *
     * When used with {@link allowStaleOnFetchAbort}, aborted {@link fetch}
     * calls will resolve immediately to their stale cached value or
     * `undefined`, and will continue to process and eventually update the
     * cache when they resolve, as long as the resulting value is not
     * `undefined`, thus supporting a "return stale on timeout while
     * refreshing" mechanism by passing `AbortSignal.timeout(n)` as the signal.
     *
     * **Note**: regardless of this setting, an `abort` event _is still emitted
     * on the `AbortSignal` object_, so may result in invalid results when
     * passed to other underlying APIs that use AbortSignals.
     *
     * This may be overridden in the {@link fetchMethod} or the call to
     * {@link fetch}.
     *
     * @default false
     * @since 7.17.0
     */
    ignoreFetchAbort?: boolean

    /**
     * Set to true to return a stale value from the cache when the
     * `AbortSignal` passed to the {@link fetchMethod} dispatches an `'abort'`
     * event, whether user-triggered, or due to internal cache behavior.
     *
     * Unless {@link ignoreFetchAbort} is also set, the underlying
     * {@link fetchMethod} will still be considered canceled, and its return
     * value will be ignored and not cached.
     *
     * This may be overridden in the {@link fetchMethod} or the call to
     * {@link fetch}.
     *
     * @default false
     * @since 7.17.0
     */
    allowStaleOnFetchAbort?: boolean

    /**
     * Set to any value in the constructor or {@link fetch} options to
     * pass arbitrary data to the {@link fetchMethod} in the {@link context}
     * options field.
     *
     * @since 7.12.0
     */
    fetchContext?: any
  }

  type Options<K, V> = SharedOptions<K, V> &
    DeprecatedOptions<K, V> &
    SafetyBounds<K, V> &
    MaybeMaxEntrySizeLimit<K, V>

  /**
   * options which override the options set in the LRUCache constructor
   * when making calling {@link set}.
   */
  interface SetOptions<K, V> {
    /**
     * A value for the size of the entry, prevents calls to
     * {@link sizeCalculation}.
     *
     * Items larger than {@link maxEntrySize} will not be stored in the cache.
     *
     * Note that when {@link maxSize} or {@link maxEntrySize} are set, every
     * item added MUST have a size specified, either via a `sizeCalculation` in
     * the constructor, or {@link sizeCalculation} or `size` options to
     * {@link set}.
     */
    size?: LRUSize
    /**
     * Overrides the {@link sizeCalculation} method set in the constructor.
     *
     * Items larger than {@link maxEntrySize} will not be stored in the cache.
     *
     * Note that when {@link maxSize} or {@link maxEntrySize} are set, every
     * item added MUST have a size specified, either via a `sizeCalculation` in
     * the constructor, or `sizeCalculation` or {@link size} options to
     * {@link set}.
     */
    sizeCalculation?: SizeCalculator<K, V>
    ttl?: LRUMilliseconds
    start?: LRUMilliseconds
    noDisposeOnSet?: boolean
    noUpdateTTL?: boolean
    status?: Status<V>
  }

  /**
   * options which override the options set in the LRUCAche constructor
   * when calling {@link has}.
   */
  interface HasOptions<V> {
    updateAgeOnHas?: boolean
    status: Status<V>
  }

  /**
   * options which override the options set in the LRUCache constructor
   * when calling {@link get}.
   */
  interface GetOptions<V> {
    allowStale?: boolean
    updateAgeOnGet?: boolean
    noDeleteOnStaleGet?: boolean
    status?: Status<V>
  }

  /**
   * options which override the options set in the LRUCache constructor
   * when calling {@link peek}.
   */
  interface PeekOptions {
    allowStale?: boolean
  }

  /**
   * Options object passed to the {@link fetchMethod}
   *
   * May be mutated by the {@link fetchMethod} to affect the behavior of the
   * resulting {@link set} operation on resolution, or in the case of
   * {@link noDeleteOnFetchRejection}, {@link ignoreFetchAbort}, and
   * {@link allowStaleOnFetchRejection}, the handling of failure.
   */
  interface FetcherFetchOptions<K, V> {
    allowStale?: boolean
    updateAgeOnGet?: boolean
    noDeleteOnStaleGet?: boolean
    size?: LRUSize
    sizeCalculation?: SizeCalculator<K, V>
    ttl?: LRUMilliseconds
    noDisposeOnSet?: boolean
    noUpdateTTL?: boolean
    noDeleteOnFetchRejection?: boolean
    allowStaleOnFetchRejection?: boolean
    ignoreFetchAbort?: boolean
    allowStaleOnFetchAbort?: boolean
    status?: Status<V>
  }

  /**
   * Status object that may be passed to {@link fetch}, {@link get},
   * {@link set}, and {@link has}.
   */
  interface Status<V> {
    /**
     * The status of a set() operation.
     *
     * - add: the item was not found in the cache, and was added
     * - update: the item was in the cache, with the same value provided
     * - replace: the item was in the cache, and replaced
     * - miss: the item was not added to the cache for some reason
     */
    set?: 'add' | 'update' | 'replace' | 'miss'

    /**
     * the ttl stored for the item, or undefined if ttls are not used.
     */
    ttl?: LRUMilliseconds

    /**
     * the start time for the item, or undefined if ttls are not used.
     */
    start?: LRUMilliseconds

    /**
     * The timestamp used for TTL calculation
     */
    now?: LRUMilliseconds

    /**
     * the remaining ttl for the item, or undefined if ttls are not used.
     */
    remainingTTL?: LRUMilliseconds

    /**
     * The calculated size for the item, if sizes are used.
     */
    size?: LRUSize

    /**
     * A flag indicating that the item was not stored, due to exceeding the
     * {@link maxEntrySize}
     */
    maxEntrySizeExceeded?: true

    /**
     * The old value, specified in the case of `set:'update'` or
     * `set:'replace'`
     */
    oldValue?: V

    /**
     * The results of a {@link has} operation
     *
     * - hit: the item was found in the cache
     * - stale: the item was found in the cache, but is stale
     * - miss: the item was not found in the cache
     */
    has?: 'hit' | 'stale' | 'miss'

    /**
     * The status of a {@link fetch} operation.
     * Note that this can change as the underlying fetch() moves through
     * various states.
     *
     * - inflight: there is another fetch() for this key which is in process
     * - get: there is no fetchMethod, so {@link get} was called.
     * - miss: the item is not in cache, and will be fetched.
     * - hit: the item is in the cache, and was resolved immediately.
     * - stale: the item is in the cache, but stale.
     * - refresh: the item is in the cache, and not stale, but
     *   {@link forceRefresh} was specified.
     */
    fetch?: 'get' | 'inflight' | 'miss' | 'hit' | 'stale' | 'refresh'

    /**
     * The {@link fetchMethod} was called
     */
    fetchDispatched?: true

    /**
     * The cached value was updated after a successful call to fetchMethod
     */
    fetchUpdated?: true

    /**
     * The reason for a fetch() rejection.  Either the error raised by the
     * {@link fetchMethod}, or the reason for an AbortSignal.
     */
    fetchError?: Error

    /**
     * The fetch received an abort signal
     */
    fetchAborted?: true

    /**
     * The abort signal received was ignored, and the fetch was allowed to
     * continue.
     */
    fetchAbortIgnored?: true

    /**
     * The fetchMethod promise resolved successfully
     */
    fetchResolved?: true

    /**
     * The fetchMethod promise was rejected
     */
    fetchRejected?: true

    /**
     * The status of a {@link get} operation.
     *
     * - fetching: The item is currently being fetched.  If a previous value is
     *   present and allowed, that will be returned.
     * - stale: The item is in the cache, and is stale.
     * - hit: the item is in the cache
     * - miss: the item is not in the cache
     */
    get?: 'stale' | 'hit' | 'miss'

    /**
     * A fetch or get operation returned a stale value.
     */
    returnedStale?: true
  }

  /**
   * options which override the options set in the LRUCache constructor
   * when calling {@link fetch}.
   *
   * This is the union of GetOptions and SetOptions, plus
   * {@link noDeleteOnFetchRejection}, {@link allowStaleOnFetchRejection},
   * {@link forceRefresh}, and {@link fetchContext}
   */
  interface FetchOptions<K, V> extends FetcherFetchOptions<K, V> {
    forceRefresh?: boolean
    fetchContext?: any
    signal?: AbortSignal
    status?: Status<V>
  }

  interface FetcherOptions<K, V> {
    signal: AbortSignal
    options: FetcherFetchOptions<K, V>
    /**
     * Object provided in the {@link fetchContext} option
     */
    context: any
  }

  interface Entry<V> {
    value: V
    ttl?: LRUMilliseconds
    size?: LRUSize
    start?: LRUMilliseconds
  }
}

export = LRUCache
