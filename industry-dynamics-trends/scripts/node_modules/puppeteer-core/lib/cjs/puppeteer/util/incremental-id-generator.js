"use strict";
/**
 * @license
 * Copyright 2024 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
Object.defineProperty(exports, "__esModule", { value: true });
exports.createIncrementalIdGenerator = createIncrementalIdGenerator;
/**
 * @internal
 */
function createIncrementalIdGenerator() {
    let id = 0;
    return () => {
        if (id === Number.MAX_SAFE_INTEGER) {
            id = 0;
        }
        return ++id;
    };
}
//# sourceMappingURL=incremental-id-generator.js.map