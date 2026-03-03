"use strict";
/**
 * @license
 * Copyright 2023 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
Object.defineProperty(exports, "__esModule", { value: true });
exports.buildArchiveFilename = exports.DefaultProvider = exports.BrowserTag = exports.InstalledBrowser = exports.Cache = exports.CLI = exports.resolveDefaultUserDataDir = exports.getVersionComparator = exports.createProfile = exports.ChromeReleaseChannel = exports.BrowserPlatform = exports.Browser = exports.resolveBuildId = exports.detectBrowserPlatform = exports.getDownloadUrl = exports.uninstall = exports.canDownload = exports.getInstalledBrowsers = exports.makeProgressCallback = exports.install = exports.Process = exports.WEBDRIVER_BIDI_WEBSOCKET_ENDPOINT_REGEX = exports.CDP_WEBSOCKET_ENDPOINT_REGEX = exports.TimeoutError = exports.computeSystemExecutablePath = exports.computeExecutablePath = exports.launch = void 0;
var launch_js_1 = require("./launch.js");
Object.defineProperty(exports, "launch", { enumerable: true, get: function () { return launch_js_1.launch; } });
Object.defineProperty(exports, "computeExecutablePath", { enumerable: true, get: function () { return launch_js_1.computeExecutablePath; } });
Object.defineProperty(exports, "computeSystemExecutablePath", { enumerable: true, get: function () { return launch_js_1.computeSystemExecutablePath; } });
Object.defineProperty(exports, "TimeoutError", { enumerable: true, get: function () { return launch_js_1.TimeoutError; } });
Object.defineProperty(exports, "CDP_WEBSOCKET_ENDPOINT_REGEX", { enumerable: true, get: function () { return launch_js_1.CDP_WEBSOCKET_ENDPOINT_REGEX; } });
Object.defineProperty(exports, "WEBDRIVER_BIDI_WEBSOCKET_ENDPOINT_REGEX", { enumerable: true, get: function () { return launch_js_1.WEBDRIVER_BIDI_WEBSOCKET_ENDPOINT_REGEX; } });
Object.defineProperty(exports, "Process", { enumerable: true, get: function () { return launch_js_1.Process; } });
var install_js_1 = require("./install.js");
Object.defineProperty(exports, "install", { enumerable: true, get: function () { return install_js_1.install; } });
Object.defineProperty(exports, "makeProgressCallback", { enumerable: true, get: function () { return install_js_1.makeProgressCallback; } });
Object.defineProperty(exports, "getInstalledBrowsers", { enumerable: true, get: function () { return install_js_1.getInstalledBrowsers; } });
Object.defineProperty(exports, "canDownload", { enumerable: true, get: function () { return install_js_1.canDownload; } });
Object.defineProperty(exports, "uninstall", { enumerable: true, get: function () { return install_js_1.uninstall; } });
Object.defineProperty(exports, "getDownloadUrl", { enumerable: true, get: function () { return install_js_1.getDownloadUrl; } });
var detectPlatform_js_1 = require("./detectPlatform.js");
Object.defineProperty(exports, "detectBrowserPlatform", { enumerable: true, get: function () { return detectPlatform_js_1.detectBrowserPlatform; } });
var browser_data_js_1 = require("./browser-data/browser-data.js");
Object.defineProperty(exports, "resolveBuildId", { enumerable: true, get: function () { return browser_data_js_1.resolveBuildId; } });
Object.defineProperty(exports, "Browser", { enumerable: true, get: function () { return browser_data_js_1.Browser; } });
Object.defineProperty(exports, "BrowserPlatform", { enumerable: true, get: function () { return browser_data_js_1.BrowserPlatform; } });
Object.defineProperty(exports, "ChromeReleaseChannel", { enumerable: true, get: function () { return browser_data_js_1.ChromeReleaseChannel; } });
Object.defineProperty(exports, "createProfile", { enumerable: true, get: function () { return browser_data_js_1.createProfile; } });
Object.defineProperty(exports, "getVersionComparator", { enumerable: true, get: function () { return browser_data_js_1.getVersionComparator; } });
Object.defineProperty(exports, "resolveDefaultUserDataDir", { enumerable: true, get: function () { return browser_data_js_1.resolveDefaultUserDataDir; } });
var CLI_js_1 = require("./CLI.js");
Object.defineProperty(exports, "CLI", { enumerable: true, get: function () { return CLI_js_1.CLI; } });
var Cache_js_1 = require("./Cache.js");
Object.defineProperty(exports, "Cache", { enumerable: true, get: function () { return Cache_js_1.Cache; } });
Object.defineProperty(exports, "InstalledBrowser", { enumerable: true, get: function () { return Cache_js_1.InstalledBrowser; } });
var types_js_1 = require("./browser-data/types.js");
Object.defineProperty(exports, "BrowserTag", { enumerable: true, get: function () { return types_js_1.BrowserTag; } });
var DefaultProvider_js_1 = require("./DefaultProvider.js");
Object.defineProperty(exports, "DefaultProvider", { enumerable: true, get: function () { return DefaultProvider_js_1.DefaultProvider; } });
var provider_js_1 = require("./provider.js");
Object.defineProperty(exports, "buildArchiveFilename", { enumerable: true, get: function () { return provider_js_1.buildArchiveFilename; } });
//# sourceMappingURL=main.js.map