"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.checkVisibility = void 0;
exports.pierce = pierce;
exports.pierceAll = pierceAll;
/**
 * @license
 * Copyright 2024 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
const HIDDEN_VISIBILITY_VALUES = ['hidden', 'collapse'];
/**
 * @internal
 */
const checkVisibility = (node, visible) => {
    if (!node) {
        return visible === false;
    }
    if (visible === undefined) {
        return node;
    }
    const element = (node.nodeType === Node.TEXT_NODE ? node.parentElement : node);
    const style = window.getComputedStyle(element);
    const isVisible = style &&
        !HIDDEN_VISIBILITY_VALUES.includes(style.visibility) &&
        !isBoundingBoxEmpty(element);
    return visible === isVisible ? node : false;
};
exports.checkVisibility = checkVisibility;
function isBoundingBoxEmpty(element) {
    const rect = element.getBoundingClientRect();
    return rect.width === 0 || rect.height === 0;
}
const hasShadowRoot = (node) => {
    return 'shadowRoot' in node && node.shadowRoot instanceof ShadowRoot;
};
/**
 * @internal
 */
function* pierce(root) {
    if (hasShadowRoot(root)) {
        yield root.shadowRoot;
    }
    else {
        yield root;
    }
}
/**
 * @internal
 */
function* pierceAll(root) {
    root = pierce(root).next().value;
    yield root;
    const walkers = [document.createTreeWalker(root, NodeFilter.SHOW_ELEMENT)];
    for (const walker of walkers) {
        let node;
        while ((node = walker.nextNode())) {
            if (!node.shadowRoot) {
                continue;
            }
            yield node.shadowRoot;
            walkers.push(document.createTreeWalker(node.shadowRoot, NodeFilter.SHOW_ELEMENT));
        }
    }
}
//# sourceMappingURL=util.js.map