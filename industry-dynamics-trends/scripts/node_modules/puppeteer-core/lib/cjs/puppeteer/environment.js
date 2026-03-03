"use strict";
/**
 * @license
 * Copyright 2020 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
Object.defineProperty(exports, "__esModule", { value: true });
exports.environment = exports.isNode = void 0;
/**
 * @internal
 */
exports.isNode = !!(typeof process !== 'undefined' && process.version);
/**
 * Holder for environment dependencies. These dependencies cannot
 * be used during the module instantiation.
 */
exports.environment = {
    value: {
        get fs() {
            throw new Error('fs is not available in this environment');
        },
        get ScreenRecorder() {
            throw new Error('ScreenRecorder is not available in this environment');
        },
    },
};
//# sourceMappingURL=environment.js.map