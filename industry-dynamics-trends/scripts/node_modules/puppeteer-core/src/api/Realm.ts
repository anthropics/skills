/**
 * @license
 * Copyright 2023 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */

import type {TimeoutSettings} from '../common/TimeoutSettings.js';
import type {
  EvaluateFunc,
  HandleFor,
  InnerLazyParams,
} from '../common/types.js';
import {TaskManager, WaitTask} from '../common/WaitTask.js';
import {disposeSymbol} from '../util/disposable.js';

import type {ElementHandle} from './ElementHandle.js';
import type {Environment} from './Environment.js';
import type {JSHandle} from './JSHandle.js';

/**
 * @internal
 */
export abstract class Realm implements Disposable {
  protected readonly timeoutSettings: TimeoutSettings;
  readonly taskManager = new TaskManager();

  constructor(timeoutSettings: TimeoutSettings) {
    this.timeoutSettings = timeoutSettings;
  }

  abstract get environment(): Environment;

  abstract adoptHandle<T extends JSHandle<Node>>(handle: T): Promise<T>;
  abstract transferHandle<T extends JSHandle<Node>>(handle: T): Promise<T>;
  abstract evaluateHandle<
    Params extends unknown[],
    Func extends EvaluateFunc<Params> = EvaluateFunc<Params>,
  >(
    pageFunction: Func | string,
    ...args: Params
  ): Promise<HandleFor<Awaited<ReturnType<Func>>>>;
  abstract evaluate<
    Params extends unknown[],
    Func extends EvaluateFunc<Params> = EvaluateFunc<Params>,
  >(
    pageFunction: Func | string,
    ...args: Params
  ): Promise<Awaited<ReturnType<Func>>>;

  async waitForFunction<
    Params extends unknown[],
    Func extends EvaluateFunc<InnerLazyParams<Params>> = EvaluateFunc<
      InnerLazyParams<Params>
    >,
  >(
    pageFunction: Func | string,
    options: {
      polling?: 'raf' | 'mutation' | number;
      timeout?: number;
      root?: ElementHandle<Node>;
      signal?: AbortSignal;
    } = {},
    ...args: Params
  ): Promise<HandleFor<Awaited<ReturnType<Func>>>> {
    const {
      polling = 'raf',
      timeout = this.timeoutSettings.timeout(),
      root,
      signal,
    } = options;
    if (typeof polling === 'number' && polling < 0) {
      throw new Error('Cannot poll with non-positive interval');
    }
    const waitTask = new WaitTask(
      this,
      {
        polling,
        root,
        timeout,
        signal,
      },
      pageFunction as unknown as
        | ((...args: unknown[]) => Promise<Awaited<ReturnType<Func>>>)
        | string,
      ...args,
    );
    return await waitTask.result;
  }

  abstract adoptBackendNode(backendNodeId?: number): Promise<JSHandle<Node>>;

  get disposed(): boolean {
    return this.#disposed;
  }

  #disposed = false;
  /** @internal */
  dispose(): void {
    this.#disposed = true;
    this.taskManager.terminateAll(
      new Error('waitForFunction failed: frame got detached.'),
    );
  }
  /** @internal */
  [disposeSymbol](): void {
    this.dispose();
  }
}
