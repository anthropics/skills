"use strict";
/**
 * @license
 * Copyright 2026 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
Object.defineProperty(exports, "__esModule", { value: true });
exports.DefaultProvider = void 0;
const browser_data_js_1 = require("./browser-data/browser-data.js");
/**
 * Default provider implementation that uses default sources.
 * This is the standard provider used by Puppeteer.
 *
 * @public
 */
class DefaultProvider {
    #baseUrl;
    constructor(baseUrl) {
        this.#baseUrl = baseUrl;
    }
    supports(_options) {
        // Default provider supports all browsers
        return true;
    }
    getDownloadUrl(options) {
        return this.#getDownloadUrl(options.browser, options.platform, options.buildId);
    }
    #getDownloadUrl(browser, platform, buildId) {
        return new URL(browser_data_js_1.downloadUrls[browser](platform, buildId, this.#baseUrl));
    }
    getExecutablePath(options) {
        return browser_data_js_1.executablePathByBrowser[options.browser](options.platform, options.buildId);
    }
    getName() {
        return 'DefaultProvider';
    }
}
exports.DefaultProvider = DefaultProvider;
//# sourceMappingURL=DefaultProvider.js.map