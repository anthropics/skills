"use strict";
/**
 * @license
 * Copyright 2023 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
Object.defineProperty(exports, "__esModule", { value: true });
exports.TextQueryHandler = void 0;
const QueryHandler_js_1 = require("./QueryHandler.js");
/**
 * @internal
 */
class TextQueryHandler extends QueryHandler_js_1.QueryHandler {
    static querySelectorAll = (element, selector, { textQuerySelectorAll }) => {
        return textQuerySelectorAll(element, selector);
    };
}
exports.TextQueryHandler = TextQueryHandler;
//# sourceMappingURL=TextQueryHandler.js.map