/**
 * @license
 * Copyright 2023 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
import { TaskManager, WaitTask } from '../common/WaitTask.js';
import { disposeSymbol } from '../util/disposable.js';
/**
 * @internal
 */
export class Realm {
    timeoutSettings;
    taskManager = new TaskManager();
    constructor(timeoutSettings) {
        this.timeoutSettings = timeoutSettings;
    }
    async waitForFunction(pageFunction, options = {}, ...args) {
        const { polling = 'raf', timeout = this.timeoutSettings.timeout(), root, signal, } = options;
        if (typeof polling === 'number' && polling < 0) {
            throw new Error('Cannot poll with non-positive interval');
        }
        const waitTask = new WaitTask(this, {
            polling,
            root,
            timeout,
            signal,
        }, pageFunction, ...args);
        return await waitTask.result;
    }
    get disposed() {
        return this.#disposed;
    }
    #disposed = false;
    /** @internal */
    dispose() {
        this.#disposed = true;
        this.taskManager.terminateAll(new Error('waitForFunction failed: frame got detached.'));
    }
    /** @internal */
    [disposeSymbol]() {
        this.dispose();
    }
}
//# sourceMappingURL=Realm.js.map