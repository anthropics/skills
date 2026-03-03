"use strict";
/**
 * @license
 * Copyright 2023 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
Object.defineProperty(exports, "__esModule", { value: true });
exports.PierceQueryHandler = void 0;
const QueryHandler_js_1 = require("./QueryHandler.js");
/**
 * @internal
 */
class PierceQueryHandler extends QueryHandler_js_1.QueryHandler {
    static querySelector = (element, selector, { pierceQuerySelector }) => {
        return pierceQuerySelector(element, selector);
    };
    static querySelectorAll = (element, selector, { pierceQuerySelectorAll }) => {
        return pierceQuerySelectorAll(element, selector);
    };
}
exports.PierceQueryHandler = PierceQueryHandler;
//# sourceMappingURL=PierceQueryHandler.js.map