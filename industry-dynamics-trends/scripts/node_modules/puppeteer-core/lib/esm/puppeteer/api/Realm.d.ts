/**
 * @license
 * Copyright 2023 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
import type { TimeoutSettings } from '../common/TimeoutSettings.js';
import type { EvaluateFunc, HandleFor, InnerLazyParams } from '../common/types.js';
import { TaskManager } from '../common/WaitTask.js';
import { disposeSymbol } from '../util/disposable.js';
import type { ElementHandle } from './ElementHandle.js';
import type { Environment } from './Environment.js';
import type { JSHandle } from './JSHandle.js';
/**
 * @internal
 */
export declare abstract class Realm implements Disposable {
    #private;
    protected readonly timeoutSettings: TimeoutSettings;
    readonly taskManager: TaskManager;
    constructor(timeoutSettings: TimeoutSettings);
    abstract get environment(): Environment;
    abstract adoptHandle<T extends JSHandle<Node>>(handle: T): Promise<T>;
    abstract transferHandle<T extends JSHandle<Node>>(handle: T): Promise<T>;
    abstract evaluateHandle<Params extends unknown[], Func extends EvaluateFunc<Params> = EvaluateFunc<Params>>(pageFunction: Func | string, ...args: Params): Promise<HandleFor<Awaited<ReturnType<Func>>>>;
    abstract evaluate<Params extends unknown[], Func extends EvaluateFunc<Params> = EvaluateFunc<Params>>(pageFunction: Func | string, ...args: Params): Promise<Awaited<ReturnType<Func>>>;
    waitForFunction<Params extends unknown[], Func extends EvaluateFunc<InnerLazyParams<Params>> = EvaluateFunc<InnerLazyParams<Params>>>(pageFunction: Func | string, options?: {
        polling?: 'raf' | 'mutation' | number;
        timeout?: number;
        root?: ElementHandle<Node>;
        signal?: AbortSignal;
    }, ...args: Params): Promise<HandleFor<Awaited<ReturnType<Func>>>>;
    abstract adoptBackendNode(backendNodeId?: number): Promise<JSHandle<Node>>;
    get disposed(): boolean;
    /** @internal */
    dispose(): void;
    /** @internal */
    [disposeSymbol](): void;
}
//# sourceMappingURL=Realm.d.ts.map