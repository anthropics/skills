"use strict";
/**
 * @license
 * Copyright 2024 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
Object.defineProperty(exports, "__esModule", { value: true });
exports.cssQuerySelectorAll = exports.cssQuerySelector = void 0;
/**
 * @internal
 */
const cssQuerySelector = (root, selector) => {
    // @ts-expect-error assume element root
    return root.querySelector(selector);
};
exports.cssQuerySelector = cssQuerySelector;
/**
 * @internal
 */
const cssQuerySelectorAll = function (root, selector) {
    // @ts-expect-error assume element root
    return root.querySelectorAll(selector);
};
exports.cssQuerySelectorAll = cssQuerySelectorAll;
//# sourceMappingURL=CSSSelector.js.map