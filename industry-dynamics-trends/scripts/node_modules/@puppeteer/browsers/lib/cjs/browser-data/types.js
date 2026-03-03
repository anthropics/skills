"use strict";
/**
 * @license
 * Copyright 2023 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
Object.defineProperty(exports, "__esModule", { value: true });
exports.ChromeReleaseChannel = exports.BrowserTag = exports.BrowserPlatform = exports.Browser = void 0;
/**
 * Supported browsers.
 *
 * @public
 */
var Browser;
(function (Browser) {
    Browser["CHROME"] = "chrome";
    Browser["CHROMEHEADLESSSHELL"] = "chrome-headless-shell";
    Browser["CHROMIUM"] = "chromium";
    Browser["FIREFOX"] = "firefox";
    Browser["CHROMEDRIVER"] = "chromedriver";
})(Browser || (exports.Browser = Browser = {}));
/**
 * Platform names used to identify a OS platform x architecture combination in the way
 * that is relevant for the browser download.
 *
 * @public
 */
var BrowserPlatform;
(function (BrowserPlatform) {
    BrowserPlatform["LINUX"] = "linux";
    BrowserPlatform["LINUX_ARM"] = "linux_arm";
    BrowserPlatform["MAC"] = "mac";
    BrowserPlatform["MAC_ARM"] = "mac_arm";
    BrowserPlatform["WIN32"] = "win32";
    BrowserPlatform["WIN64"] = "win64";
})(BrowserPlatform || (exports.BrowserPlatform = BrowserPlatform = {}));
/**
 * Enum describing a release channel for a browser.
 *
 * You can use this in combination with {@link resolveBuildId} to resolve
 * a build ID based on a release channel.
 *
 * @public
 */
var BrowserTag;
(function (BrowserTag) {
    BrowserTag["CANARY"] = "canary";
    BrowserTag["NIGHTLY"] = "nightly";
    BrowserTag["BETA"] = "beta";
    BrowserTag["DEV"] = "dev";
    BrowserTag["DEVEDITION"] = "devedition";
    BrowserTag["STABLE"] = "stable";
    BrowserTag["ESR"] = "esr";
    BrowserTag["LATEST"] = "latest";
})(BrowserTag || (exports.BrowserTag = BrowserTag = {}));
/**
 * @public
 */
var ChromeReleaseChannel;
(function (ChromeReleaseChannel) {
    ChromeReleaseChannel["STABLE"] = "stable";
    ChromeReleaseChannel["DEV"] = "dev";
    ChromeReleaseChannel["CANARY"] = "canary";
    ChromeReleaseChannel["BETA"] = "beta";
})(ChromeReleaseChannel || (exports.ChromeReleaseChannel = ChromeReleaseChannel = {}));
//# sourceMappingURL=types.js.map