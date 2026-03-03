"use strict";
/**
 * @license
 * Copyright 2026 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
const node_assert_1 = __importDefault(require("node:assert"));
const main_js_1 = require("./main.js");
describe('DefaultProvider', () => {
    let provider;
    beforeEach(() => {
        provider = new main_js_1.DefaultProvider();
    });
    describe('constructor', () => {
        it('should create provider with default base URL', () => {
            const defaultProvider = new main_js_1.DefaultProvider();
            (0, node_assert_1.default)(defaultProvider instanceof main_js_1.DefaultProvider);
        });
        it('should create provider with custom base URL', () => {
            const customBaseUrl = 'https://custom.example.com/';
            const customProvider = new main_js_1.DefaultProvider(customBaseUrl);
            (0, node_assert_1.default)(customProvider instanceof main_js_1.DefaultProvider);
        });
    });
    describe('BrowserProvider interface compliance', () => {
        it('should implement supports method', () => {
            node_assert_1.default.strictEqual(typeof provider.supports, 'function');
        });
        it('should implement getDownloadUrl method', () => {
            node_assert_1.default.strictEqual(typeof provider.getDownloadUrl, 'function');
        });
        it('should implement getExecutablePath method', () => {
            node_assert_1.default.strictEqual(typeof provider.getExecutablePath, 'function');
        });
    });
    describe('basic functionality', () => {
        it('should handle different browsers', () => {
            // Test with a known build ID that should exist
            const result = provider.supports({
                browser: main_js_1.Browser.CHROME,
                platform: main_js_1.BrowserPlatform.LINUX,
                buildId: '120.0.6099.109',
            });
            // Chrome for Testing supports all browsers
            node_assert_1.default.strictEqual(result, true);
        });
        it('should handle different platforms', () => {
            const result = provider.supports({
                browser: main_js_1.Browser.CHROME,
                platform: main_js_1.BrowserPlatform.MAC,
                buildId: '120.0.6099.109',
            });
            // Chrome for Testing supports all platforms
            node_assert_1.default.strictEqual(result, true);
        });
        it('should handle ChromeDriver', () => {
            const result = provider.supports({
                browser: main_js_1.Browser.CHROMEDRIVER,
                platform: main_js_1.BrowserPlatform.LINUX,
                buildId: '120.0.6099.109',
            });
            // Chrome for Testing supports all browsers
            node_assert_1.default.strictEqual(result, true);
        });
        it('should return URL for valid build', () => {
            const result = provider.getDownloadUrl({
                browser: main_js_1.Browser.CHROME,
                platform: main_js_1.BrowserPlatform.LINUX,
                buildId: '120.0.6099.109',
            });
            (0, node_assert_1.default)(result instanceof URL);
            (0, node_assert_1.default)(result.toString().includes('120.0.6099.109'));
        });
    });
});
//# sourceMappingURL=DefaultProvider.spec.js.map