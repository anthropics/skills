"use strict";
/**
 * @license
 * Copyright 2022 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
Object.defineProperty(exports, "__esModule", { value: true });
exports.ariaQuerySelectorAll = exports.ariaQuerySelector = void 0;
/**
 * @internal
 */
const ariaQuerySelector = (root, selector) => {
    // In Firefox sandboxes globalThis !== window and we expose bindings on globalThis.
    return globalThis.__ariaQuerySelector(root, selector);
};
exports.ariaQuerySelector = ariaQuerySelector;
/**
 * @internal
 */
const ariaQuerySelectorAll = async function* (root, selector) {
    // In Firefox sandboxes globalThis !== window and we expose bindings on globalThis.
    yield* await globalThis.__ariaQuerySelectorAll(root, selector);
};
exports.ariaQuerySelectorAll = ariaQuerySelectorAll;
//# sourceMappingURL=ARIAQuerySelector.js.map