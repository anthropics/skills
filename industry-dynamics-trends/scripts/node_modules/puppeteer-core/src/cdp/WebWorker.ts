/**
 * @license
 * Copyright 2018 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
import type {Protocol} from 'devtools-protocol';

import {CDPSessionEvent, type CDPSession} from '../api/CDPSession.js';
import type {Realm} from '../api/Realm.js';
import {TargetType} from '../api/Target.js';
import {WebWorker} from '../api/WebWorker.js';
import {TimeoutSettings} from '../common/TimeoutSettings.js';
import {debugError} from '../common/util.js';

import {ExecutionContext} from './ExecutionContext.js';
import {IsolatedWorld} from './IsolatedWorld.js';
import type {NetworkManager} from './NetworkManager.js';

/**
 * @internal
 */
export type ConsoleAPICalledCallback = (
  world: IsolatedWorld,
  event: Protocol.Runtime.ConsoleAPICalledEvent,
) => void;

/**
 * @internal
 */
export type ExceptionThrownCallback = (
  event: Protocol.Runtime.ExceptionThrownEvent,
) => void;

/**
 * @internal
 */
export class CdpWebWorker extends WebWorker {
  #world: IsolatedWorld;
  #client: CDPSession;
  readonly #id: string;
  readonly #targetType: TargetType;

  constructor(
    client: CDPSession,
    url: string,
    targetId: string,
    targetType: TargetType,
    consoleAPICalled: ConsoleAPICalledCallback,
    exceptionThrown: ExceptionThrownCallback,
    networkManager?: NetworkManager,
  ) {
    super(url);
    this.#id = targetId;
    this.#client = client;
    this.#targetType = targetType;
    this.#world = new IsolatedWorld(this, new TimeoutSettings());

    this.#client.once('Runtime.executionContextCreated', async event => {
      this.#world.setContext(
        new ExecutionContext(client, event.context, this.#world),
      );
    });
    this.#world.emitter.on('consoleapicalled', async event => {
      try {
        return consoleAPICalled(this.#world, event);
      } catch (err) {
        debugError(err);
      }
    });
    this.#client.on('Runtime.exceptionThrown', exceptionThrown);
    this.#client.once(CDPSessionEvent.Disconnected, () => {
      this.#world.dispose();
    });

    // This might fail if the target is closed before we receive all execution contexts.
    networkManager?.addClient(this.#client).catch(debugError);
    this.#client.send('Runtime.enable').catch(debugError);
  }

  mainRealm(): Realm {
    return this.#world;
  }

  get client(): CDPSession {
    return this.#client;
  }

  override async close(): Promise<void> {
    switch (this.#targetType) {
      case TargetType.SERVICE_WORKER: {
        // For service workers we need to close the target and detach to allow
        // the worker to stop.
        await this.client.connection()?.send('Target.closeTarget', {
          targetId: this.#id,
        });
        await this.client.connection()?.send('Target.detachFromTarget', {
          sessionId: this.client.id(),
        });
        break;
      }
      case TargetType.SHARED_WORKER: {
        await this.client.connection()?.send('Target.closeTarget', {
          targetId: this.#id,
        });
        break;
      }
      default:
        await this.evaluate(() => {
          self.close();
        });
    }
  }
}
