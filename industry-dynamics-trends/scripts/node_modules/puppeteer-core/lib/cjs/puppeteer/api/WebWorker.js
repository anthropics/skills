"use strict";
/**
 * @license
 * Copyright 2018 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
Object.defineProperty(exports, "__esModule", { value: true });
exports.WebWorker = void 0;
const Errors_js_1 = require("../common/Errors.js");
const EventEmitter_js_1 = require("../common/EventEmitter.js");
const TimeoutSettings_js_1 = require("../common/TimeoutSettings.js");
const util_js_1 = require("../common/util.js");
/**
 * This class represents a
 * {@link https://developer.mozilla.org/en-US/docs/Web/API/Web_Workers_API | WebWorker}.
 *
 * @remarks
 * The events `workercreated` and `workerdestroyed` are emitted on the page
 * object to signal the worker lifecycle.
 *
 * @example
 *
 * ```ts
 * page.on('workercreated', worker =>
 *   console.log('Worker created: ' + worker.url()),
 * );
 * page.on('workerdestroyed', worker =>
 *   console.log('Worker destroyed: ' + worker.url()),
 * );
 *
 * console.log('Current workers:');
 * for (const worker of page.workers()) {
 *   console.log('  ' + worker.url());
 * }
 * ```
 *
 * @public
 */
class WebWorker extends EventEmitter_js_1.EventEmitter {
    /**
     * @internal
     */
    timeoutSettings = new TimeoutSettings_js_1.TimeoutSettings();
    #url;
    /**
     * @internal
     */
    constructor(url) {
        super();
        this.#url = url;
    }
    /**
     * The URL of this web worker.
     */
    url() {
        return this.#url;
    }
    /**
     * Evaluates a given function in the {@link WebWorker | worker}.
     *
     * @remarks If the given function returns a promise,
     * {@link WebWorker.evaluate | evaluate} will wait for the promise to resolve.
     *
     * As a rule of thumb, if the return value of the given function is more
     * complicated than a JSON object (e.g. most classes), then
     * {@link WebWorker.evaluate | evaluate} will _likely_ return some truncated
     * value (or `{}`). This is because we are not returning the actual return
     * value, but a deserialized version as a result of transferring the return
     * value through a protocol to Puppeteer.
     *
     * In general, you should use
     * {@link WebWorker.evaluateHandle | evaluateHandle} if
     * {@link WebWorker.evaluate | evaluate} cannot serialize the return value
     * properly or you need a mutable {@link JSHandle | handle} to the return
     * object.
     *
     * @param func - Function to be evaluated.
     * @param args - Arguments to pass into `func`.
     * @returns The result of `func`.
     */
    async evaluate(func, ...args) {
        func = (0, util_js_1.withSourcePuppeteerURLIfNone)(this.evaluate.name, func);
        return await this.mainRealm().evaluate(func, ...args);
    }
    /**
     * Evaluates a given function in the {@link WebWorker | worker}.
     *
     * @remarks If the given function returns a promise,
     * {@link WebWorker.evaluate | evaluate} will wait for the promise to resolve.
     *
     * In general, you should use
     * {@link WebWorker.evaluateHandle | evaluateHandle} if
     * {@link WebWorker.evaluate | evaluate} cannot serialize the return value
     * properly or you need a mutable {@link JSHandle | handle} to the return
     * object.
     *
     * @param func - Function to be evaluated.
     * @param args - Arguments to pass into `func`.
     * @returns A {@link JSHandle | handle} to the return value of `func`.
     */
    async evaluateHandle(func, ...args) {
        func = (0, util_js_1.withSourcePuppeteerURLIfNone)(this.evaluateHandle.name, func);
        return await this.mainRealm().evaluateHandle(func, ...args);
    }
    async close() {
        throw new Errors_js_1.UnsupportedOperation('WebWorker.close() is not supported');
    }
}
exports.WebWorker = WebWorker;
//# sourceMappingURL=WebWorker.js.map