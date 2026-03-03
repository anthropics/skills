"use strict";
/**
 * @license
 * Copyright 2023 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
Object.defineProperty(exports, "__esModule", { value: true });
exports.PQueryHandler = void 0;
const QueryHandler_js_1 = require("./QueryHandler.js");
/**
 * @internal
 */
class PQueryHandler extends QueryHandler_js_1.QueryHandler {
    static querySelectorAll = (element, selector, { pQuerySelectorAll }) => {
        return pQuerySelectorAll(element, selector);
    };
    static querySelector = (element, selector, { pQuerySelector }) => {
        return pQuerySelector(element, selector);
    };
}
exports.PQueryHandler = PQueryHandler;
//# sourceMappingURL=PQueryHandler.js.map