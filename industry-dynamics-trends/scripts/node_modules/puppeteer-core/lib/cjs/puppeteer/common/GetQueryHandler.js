"use strict";
/**
 * @license
 * Copyright 2023 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
Object.defineProperty(exports, "__esModule", { value: true });
exports.getQueryHandlerAndSelector = getQueryHandlerAndSelector;
const AriaQueryHandler_js_1 = require("./AriaQueryHandler.js");
const CSSQueryHandler_js_1 = require("./CSSQueryHandler.js");
const CustomQueryHandler_js_1 = require("./CustomQueryHandler.js");
const PierceQueryHandler_js_1 = require("./PierceQueryHandler.js");
const PQueryHandler_js_1 = require("./PQueryHandler.js");
const PSelectorParser_js_1 = require("./PSelectorParser.js");
const TextQueryHandler_js_1 = require("./TextQueryHandler.js");
const XPathQueryHandler_js_1 = require("./XPathQueryHandler.js");
const BUILTIN_QUERY_HANDLERS = {
    aria: AriaQueryHandler_js_1.ARIAQueryHandler,
    pierce: PierceQueryHandler_js_1.PierceQueryHandler,
    xpath: XPathQueryHandler_js_1.XPathQueryHandler,
    text: TextQueryHandler_js_1.TextQueryHandler,
};
const QUERY_SEPARATORS = ['=', '/'];
/**
 * @internal
 */
function getQueryHandlerAndSelector(selector) {
    for (const handlerMap of [
        CustomQueryHandler_js_1.customQueryHandlers.names().map(name => {
            return [name, CustomQueryHandler_js_1.customQueryHandlers.get(name)];
        }),
        Object.entries(BUILTIN_QUERY_HANDLERS),
    ]) {
        for (const [name, QueryHandler] of handlerMap) {
            for (const separator of QUERY_SEPARATORS) {
                const prefix = `${name}${separator}`;
                if (selector.startsWith(prefix)) {
                    selector = selector.slice(prefix.length);
                    return {
                        updatedSelector: selector,
                        polling: name === 'aria' ? "raf" /* PollingOptions.RAF */ : "mutation" /* PollingOptions.MUTATION */,
                        QueryHandler,
                    };
                }
            }
        }
    }
    try {
        const [pSelector, isPureCSS, hasPseudoClasses, hasAria] = (0, PSelectorParser_js_1.parsePSelectors)(selector);
        if (isPureCSS) {
            return {
                updatedSelector: selector,
                polling: hasPseudoClasses
                    ? "raf" /* PollingOptions.RAF */
                    : "mutation" /* PollingOptions.MUTATION */,
                QueryHandler: CSSQueryHandler_js_1.CSSQueryHandler,
            };
        }
        return {
            updatedSelector: JSON.stringify(pSelector),
            polling: hasAria ? "raf" /* PollingOptions.RAF */ : "mutation" /* PollingOptions.MUTATION */,
            QueryHandler: PQueryHandler_js_1.PQueryHandler,
        };
    }
    catch {
        return {
            updatedSelector: selector,
            polling: "mutation" /* PollingOptions.MUTATION */,
            QueryHandler: CSSQueryHandler_js_1.CSSQueryHandler,
        };
    }
}
//# sourceMappingURL=GetQueryHandler.js.map