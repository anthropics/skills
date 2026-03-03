"use strict";
/**
 * @license
 * Copyright 2023 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
Object.defineProperty(exports, "__esModule", { value: true });
exports.CSSQueryHandler = void 0;
const QueryHandler_js_1 = require("./QueryHandler.js");
/**
 * @internal
 */
class CSSQueryHandler extends QueryHandler_js_1.QueryHandler {
    static querySelector = (element, selector, { cssQuerySelector }) => {
        return cssQuerySelector(element, selector);
    };
    static querySelectorAll = (element, selector, { cssQuerySelectorAll }) => {
        return cssQuerySelectorAll(element, selector);
    };
}
exports.CSSQueryHandler = CSSQueryHandler;
//# sourceMappingURL=CSSQueryHandler.js.map