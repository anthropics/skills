"use strict";
/**
 * @license
 * Copyright 2019 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
Object.defineProperty(exports, "__esModule", { value: true });
exports.TimeoutSettings = void 0;
const DEFAULT_TIMEOUT = 30000;
/**
 * @internal
 */
class TimeoutSettings {
    #defaultTimeout;
    #defaultNavigationTimeout;
    constructor() {
        this.#defaultTimeout = null;
        this.#defaultNavigationTimeout = null;
    }
    setDefaultTimeout(timeout) {
        this.#defaultTimeout = timeout;
    }
    setDefaultNavigationTimeout(timeout) {
        this.#defaultNavigationTimeout = timeout;
    }
    navigationTimeout() {
        if (this.#defaultNavigationTimeout !== null) {
            return this.#defaultNavigationTimeout;
        }
        if (this.#defaultTimeout !== null) {
            return this.#defaultTimeout;
        }
        return DEFAULT_TIMEOUT;
    }
    timeout() {
        if (this.#defaultTimeout !== null) {
            return this.#defaultTimeout;
        }
        return DEFAULT_TIMEOUT;
    }
}
exports.TimeoutSettings = TimeoutSettings;
//# sourceMappingURL=TimeoutSettings.js.map