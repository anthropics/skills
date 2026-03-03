"use strict";
/**
 * @license
 * Copyright 2023 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
Object.defineProperty(exports, "__esModule", { value: true });
exports.Realm = void 0;
const WaitTask_js_1 = require("../common/WaitTask.js");
const disposable_js_1 = require("../util/disposable.js");
/**
 * @internal
 */
class Realm {
    timeoutSettings;
    taskManager = new WaitTask_js_1.TaskManager();
    constructor(timeoutSettings) {
        this.timeoutSettings = timeoutSettings;
    }
    async waitForFunction(pageFunction, options = {}, ...args) {
        const { polling = 'raf', timeout = this.timeoutSettings.timeout(), root, signal, } = options;
        if (typeof polling === 'number' && polling < 0) {
            throw new Error('Cannot poll with non-positive interval');
        }
        const waitTask = new WaitTask_js_1.WaitTask(this, {
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
    [disposable_js_1.disposeSymbol]() {
        this.dispose();
    }
}
exports.Realm = Realm;
//# sourceMappingURL=Realm.js.map