"use strict";
/**
 * @license
 * Copyright 2022 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
Object.defineProperty(exports, "__esModule", { value: true });
exports.textQuerySelectorAll = void 0;
const TextContent_js_1 = require("./TextContent.js");
/**
 * Queries the given node for all nodes matching the given text selector.
 *
 * @internal
 */
const textQuerySelectorAll = function* (root, selector) {
    let yielded = false;
    for (const node of root.childNodes) {
        if (node instanceof Element && (0, TextContent_js_1.isSuitableNodeForTextMatching)(node)) {
            let matches;
            if (!node.shadowRoot) {
                matches = (0, exports.textQuerySelectorAll)(node, selector);
            }
            else {
                matches = (0, exports.textQuerySelectorAll)(node.shadowRoot, selector);
            }
            for (const match of matches) {
                yield match;
                yielded = true;
            }
        }
    }
    if (yielded) {
        return;
    }
    if (root instanceof Element && (0, TextContent_js_1.isSuitableNodeForTextMatching)(root)) {
        const textContent = (0, TextContent_js_1.createTextContent)(root);
        if (textContent.full.includes(selector)) {
            yield root;
        }
    }
};
exports.textQuerySelectorAll = textQuerySelectorAll;
//# sourceMappingURL=TextQuerySelector.js.map