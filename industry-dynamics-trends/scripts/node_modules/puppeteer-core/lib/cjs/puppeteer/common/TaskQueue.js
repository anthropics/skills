"use strict";
/**
 * @license
 * Copyright 2020 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
Object.defineProperty(exports, "__esModule", { value: true });
exports.TaskQueue = void 0;
/**
 * @internal
 */
class TaskQueue {
    #chain;
    constructor() {
        this.#chain = Promise.resolve();
    }
    postTask(task) {
        const result = this.#chain.then(task);
        this.#chain = result.then(() => {
            return undefined;
        }, () => {
            return undefined;
        });
        return result;
    }
}
exports.TaskQueue = TaskQueue;
//# sourceMappingURL=TaskQueue.js.map