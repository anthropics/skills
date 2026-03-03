/**
 * @license
 * Copyright 2018 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
import type { Protocol } from 'devtools-protocol';
import { type CDPSession } from '../api/CDPSession.js';
import type { Realm } from '../api/Realm.js';
import { TargetType } from '../api/Target.js';
import { WebWorker } from '../api/WebWorker.js';
import { IsolatedWorld } from './IsolatedWorld.js';
import type { NetworkManager } from './NetworkManager.js';
/**
 * @internal
 */
export type ConsoleAPICalledCallback = (world: IsolatedWorld, event: Protocol.Runtime.ConsoleAPICalledEvent) => void;
/**
 * @internal
 */
export type ExceptionThrownCallback = (event: Protocol.Runtime.ExceptionThrownEvent) => void;
/**
 * @internal
 */
export declare class CdpWebWorker extends WebWorker {
    #private;
    constructor(client: CDPSession, url: string, targetId: string, targetType: TargetType, consoleAPICalled: ConsoleAPICalledCallback, exceptionThrown: ExceptionThrownCallback, networkManager?: NetworkManager);
    mainRealm(): Realm;
    get client(): CDPSession;
    close(): Promise<void>;
}
//# sourceMappingURL=WebWorker.d.ts.map