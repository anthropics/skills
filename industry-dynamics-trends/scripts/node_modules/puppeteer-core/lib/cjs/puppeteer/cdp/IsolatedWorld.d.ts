/**
 * @license
 * Copyright 2019 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
import type { Protocol } from 'devtools-protocol';
import type { CDPSession } from '../api/CDPSession.js';
import type { ElementHandle } from '../api/ElementHandle.js';
import type { JSHandle } from '../api/JSHandle.js';
import { Realm } from '../api/Realm.js';
import { EventEmitter } from '../common/EventEmitter.js';
import type { TimeoutSettings } from '../common/TimeoutSettings.js';
import type { EvaluateFunc, HandleFor } from '../common/types.js';
import { disposeSymbol } from '../util/disposable.js';
import type { ExecutionContext } from './ExecutionContext.js';
import type { CdpFrame } from './Frame.js';
import type { MAIN_WORLD, PUPPETEER_WORLD } from './IsolatedWorlds.js';
import type { CdpWebWorker } from './WebWorker.js';
/**
 * @internal
 */
export interface PageBinding {
    name: string;
    pptrFunction: Function;
}
/**
 * @internal
 */
export interface IsolatedWorldChart {
    [key: string]: IsolatedWorld;
    [MAIN_WORLD]: IsolatedWorld;
    [PUPPETEER_WORLD]: IsolatedWorld;
}
/**
 * @internal
 */
export type IsolatedWorldEmitter = EventEmitter<{
    context: ExecutionContext;
    disposed: undefined;
    consoleapicalled: Protocol.Runtime.ConsoleAPICalledEvent;
    /** Emitted when a binding that is not installed by the ExecutionContext is called. */
    bindingcalled: Protocol.Runtime.BindingCalledEvent;
}>;
/**
 * @internal
 */
export declare class IsolatedWorld extends Realm {
    #private;
    constructor(frameOrWorker: CdpFrame | CdpWebWorker, timeoutSettings: TimeoutSettings);
    get environment(): CdpFrame | CdpWebWorker;
    get client(): CDPSession;
    get emitter(): IsolatedWorldEmitter;
    setContext(context: ExecutionContext): void;
    hasContext(): boolean;
    get context(): ExecutionContext | undefined;
    evaluateHandle<Params extends unknown[], Func extends EvaluateFunc<Params> = EvaluateFunc<Params>>(pageFunction: Func | string, ...args: Params): Promise<HandleFor<Awaited<ReturnType<Func>>>>;
    evaluate<Params extends unknown[], Func extends EvaluateFunc<Params> = EvaluateFunc<Params>>(pageFunction: Func | string, ...args: Params): Promise<Awaited<ReturnType<Func>>>;
    adoptBackendNode(backendNodeId?: Protocol.DOM.BackendNodeId): Promise<JSHandle<Node>>;
    adoptHandle<T extends JSHandle<Node>>(handle: T): Promise<T>;
    transferHandle<T extends JSHandle<Node>>(handle: T): Promise<T>;
    /**
     * @internal
     */
    createCdpHandle(remoteObject: Protocol.Runtime.RemoteObject): JSHandle | ElementHandle<Node>;
    [disposeSymbol](): void;
}
//# sourceMappingURL=IsolatedWorld.d.ts.map