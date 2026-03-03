"use strict";
/**
 * @license
 * Copyright 2023 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
Object.defineProperty(exports, "__esModule", { value: true });
exports.BidiWorkerTarget = exports.BidiFrameTarget = exports.BidiPageTarget = exports.BidiBrowserTarget = void 0;
const Target_js_1 = require("../api/Target.js");
const Errors_js_1 = require("../common/Errors.js");
const Page_js_1 = require("./Page.js");
/**
 * @internal
 */
class BidiBrowserTarget extends Target_js_1.Target {
    #browser;
    constructor(browser) {
        super();
        this.#browser = browser;
    }
    asPage() {
        throw new Errors_js_1.UnsupportedOperation();
    }
    url() {
        return '';
    }
    createCDPSession() {
        throw new Errors_js_1.UnsupportedOperation();
    }
    type() {
        return Target_js_1.TargetType.BROWSER;
    }
    browser() {
        return this.#browser;
    }
    browserContext() {
        return this.#browser.defaultBrowserContext();
    }
    opener() {
        throw new Errors_js_1.UnsupportedOperation();
    }
}
exports.BidiBrowserTarget = BidiBrowserTarget;
/**
 * @internal
 */
class BidiPageTarget extends Target_js_1.Target {
    #page;
    constructor(page) {
        super();
        this.#page = page;
    }
    async page() {
        return this.#page;
    }
    async asPage() {
        return Page_js_1.BidiPage.from(this.browserContext(), this.#page.mainFrame().browsingContext);
    }
    url() {
        return this.#page.url();
    }
    createCDPSession() {
        return this.#page.createCDPSession();
    }
    type() {
        return Target_js_1.TargetType.PAGE;
    }
    browser() {
        return this.browserContext().browser();
    }
    browserContext() {
        return this.#page.browserContext();
    }
    opener() {
        throw new Errors_js_1.UnsupportedOperation();
    }
}
exports.BidiPageTarget = BidiPageTarget;
/**
 * @internal
 */
class BidiFrameTarget extends Target_js_1.Target {
    #frame;
    #page;
    constructor(frame) {
        super();
        this.#frame = frame;
    }
    async page() {
        if (this.#page === undefined) {
            this.#page = Page_js_1.BidiPage.from(this.browserContext(), this.#frame.browsingContext);
        }
        return this.#page;
    }
    async asPage() {
        return Page_js_1.BidiPage.from(this.browserContext(), this.#frame.browsingContext);
    }
    url() {
        return this.#frame.url();
    }
    createCDPSession() {
        return this.#frame.createCDPSession();
    }
    type() {
        return Target_js_1.TargetType.PAGE;
    }
    browser() {
        return this.browserContext().browser();
    }
    browserContext() {
        return this.#frame.page().browserContext();
    }
    opener() {
        throw new Errors_js_1.UnsupportedOperation();
    }
}
exports.BidiFrameTarget = BidiFrameTarget;
/**
 * @internal
 */
class BidiWorkerTarget extends Target_js_1.Target {
    #worker;
    constructor(worker) {
        super();
        this.#worker = worker;
    }
    async page() {
        throw new Errors_js_1.UnsupportedOperation();
    }
    async asPage() {
        throw new Errors_js_1.UnsupportedOperation();
    }
    url() {
        return this.#worker.url();
    }
    createCDPSession() {
        throw new Errors_js_1.UnsupportedOperation();
    }
    type() {
        return Target_js_1.TargetType.OTHER;
    }
    browser() {
        return this.browserContext().browser();
    }
    browserContext() {
        return this.#worker.frame.page().browserContext();
    }
    opener() {
        throw new Errors_js_1.UnsupportedOperation();
    }
}
exports.BidiWorkerTarget = BidiWorkerTarget;
//# sourceMappingURL=Target.js.map