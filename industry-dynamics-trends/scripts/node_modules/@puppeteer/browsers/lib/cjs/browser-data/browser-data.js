"use strict";
/**
 * @license
 * Copyright 2023 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __setModuleDefault = (this && this.__setModuleDefault) || (Object.create ? (function(o, v) {
    Object.defineProperty(o, "default", { enumerable: true, value: v });
}) : function(o, v) {
    o["default"] = v;
});
var __importStar = (this && this.__importStar) || (function () {
    var ownKeys = function(o) {
        ownKeys = Object.getOwnPropertyNames || function (o) {
            var ar = [];
            for (var k in o) if (Object.prototype.hasOwnProperty.call(o, k)) ar[ar.length] = k;
            return ar;
        };
        return ownKeys(o);
    };
    return function (mod) {
        if (mod && mod.__esModule) return mod;
        var result = {};
        if (mod != null) for (var k = ownKeys(mod), i = 0; i < k.length; i++) if (k[i] !== "default") __createBinding(result, mod, k[i]);
        __setModuleDefault(result, mod);
        return result;
    };
})();
Object.defineProperty(exports, "__esModule", { value: true });
exports.ChromeReleaseChannel = exports.BrowserPlatform = exports.Browser = exports.versionComparators = exports.executablePathByBrowser = exports.downloadPaths = exports.downloadUrls = void 0;
exports.resolveBuildId = resolveBuildId;
exports.createProfile = createProfile;
exports.resolveSystemExecutablePath = resolveSystemExecutablePath;
exports.resolveDefaultUserDataDir = resolveDefaultUserDataDir;
exports.resolveSystemExecutablePaths = resolveSystemExecutablePaths;
exports.getVersionComparator = getVersionComparator;
const chromeHeadlessShell = __importStar(require("./chrome-headless-shell.js"));
const chrome = __importStar(require("./chrome.js"));
const chromedriver = __importStar(require("./chromedriver.js"));
const chromium = __importStar(require("./chromium.js"));
const firefox = __importStar(require("./firefox.js"));
const types_js_1 = require("./types.js");
Object.defineProperty(exports, "Browser", { enumerable: true, get: function () { return types_js_1.Browser; } });
Object.defineProperty(exports, "BrowserPlatform", { enumerable: true, get: function () { return types_js_1.BrowserPlatform; } });
Object.defineProperty(exports, "ChromeReleaseChannel", { enumerable: true, get: function () { return types_js_1.ChromeReleaseChannel; } });
exports.downloadUrls = {
    [types_js_1.Browser.CHROMEDRIVER]: chromedriver.resolveDownloadUrl,
    [types_js_1.Browser.CHROMEHEADLESSSHELL]: chromeHeadlessShell.resolveDownloadUrl,
    [types_js_1.Browser.CHROME]: chrome.resolveDownloadUrl,
    [types_js_1.Browser.CHROMIUM]: chromium.resolveDownloadUrl,
    [types_js_1.Browser.FIREFOX]: firefox.resolveDownloadUrl,
};
exports.downloadPaths = {
    [types_js_1.Browser.CHROMEDRIVER]: chromedriver.resolveDownloadPath,
    [types_js_1.Browser.CHROMEHEADLESSSHELL]: chromeHeadlessShell.resolveDownloadPath,
    [types_js_1.Browser.CHROME]: chrome.resolveDownloadPath,
    [types_js_1.Browser.CHROMIUM]: chromium.resolveDownloadPath,
    [types_js_1.Browser.FIREFOX]: firefox.resolveDownloadPath,
};
exports.executablePathByBrowser = {
    [types_js_1.Browser.CHROMEDRIVER]: chromedriver.relativeExecutablePath,
    [types_js_1.Browser.CHROMEHEADLESSSHELL]: chromeHeadlessShell.relativeExecutablePath,
    [types_js_1.Browser.CHROME]: chrome.relativeExecutablePath,
    [types_js_1.Browser.CHROMIUM]: chromium.relativeExecutablePath,
    [types_js_1.Browser.FIREFOX]: firefox.relativeExecutablePath,
};
exports.versionComparators = {
    [types_js_1.Browser.CHROMEDRIVER]: chromedriver.compareVersions,
    [types_js_1.Browser.CHROMEHEADLESSSHELL]: chromeHeadlessShell.compareVersions,
    [types_js_1.Browser.CHROME]: chrome.compareVersions,
    [types_js_1.Browser.CHROMIUM]: chromium.compareVersions,
    [types_js_1.Browser.FIREFOX]: firefox.compareVersions,
};
/**
 * @internal
 */
async function resolveBuildIdForBrowserTag(browser, platform, tag) {
    switch (browser) {
        case types_js_1.Browser.FIREFOX:
            switch (tag) {
                case types_js_1.BrowserTag.LATEST:
                    return await firefox.resolveBuildId(firefox.FirefoxChannel.NIGHTLY);
                case types_js_1.BrowserTag.BETA:
                    return await firefox.resolveBuildId(firefox.FirefoxChannel.BETA);
                case types_js_1.BrowserTag.NIGHTLY:
                    return await firefox.resolveBuildId(firefox.FirefoxChannel.NIGHTLY);
                case types_js_1.BrowserTag.DEVEDITION:
                    return await firefox.resolveBuildId(firefox.FirefoxChannel.DEVEDITION);
                case types_js_1.BrowserTag.STABLE:
                    return await firefox.resolveBuildId(firefox.FirefoxChannel.STABLE);
                case types_js_1.BrowserTag.ESR:
                    return await firefox.resolveBuildId(firefox.FirefoxChannel.ESR);
                case types_js_1.BrowserTag.CANARY:
                case types_js_1.BrowserTag.DEV:
                    throw new Error(`${tag.toUpperCase()} is not available for Firefox`);
            }
        case types_js_1.Browser.CHROME: {
            switch (tag) {
                case types_js_1.BrowserTag.LATEST:
                    return await chrome.resolveBuildId(types_js_1.ChromeReleaseChannel.CANARY);
                case types_js_1.BrowserTag.BETA:
                    return await chrome.resolveBuildId(types_js_1.ChromeReleaseChannel.BETA);
                case types_js_1.BrowserTag.CANARY:
                    return await chrome.resolveBuildId(types_js_1.ChromeReleaseChannel.CANARY);
                case types_js_1.BrowserTag.DEV:
                    return await chrome.resolveBuildId(types_js_1.ChromeReleaseChannel.DEV);
                case types_js_1.BrowserTag.STABLE:
                    return await chrome.resolveBuildId(types_js_1.ChromeReleaseChannel.STABLE);
                case types_js_1.BrowserTag.NIGHTLY:
                case types_js_1.BrowserTag.DEVEDITION:
                case types_js_1.BrowserTag.ESR:
                    throw new Error(`${tag.toUpperCase()} is not available for Chrome`);
            }
        }
        case types_js_1.Browser.CHROMEDRIVER: {
            switch (tag) {
                case types_js_1.BrowserTag.LATEST:
                case types_js_1.BrowserTag.CANARY:
                    return await chromedriver.resolveBuildId(types_js_1.ChromeReleaseChannel.CANARY);
                case types_js_1.BrowserTag.BETA:
                    return await chromedriver.resolveBuildId(types_js_1.ChromeReleaseChannel.BETA);
                case types_js_1.BrowserTag.DEV:
                    return await chromedriver.resolveBuildId(types_js_1.ChromeReleaseChannel.DEV);
                case types_js_1.BrowserTag.STABLE:
                    return await chromedriver.resolveBuildId(types_js_1.ChromeReleaseChannel.STABLE);
                case types_js_1.BrowserTag.NIGHTLY:
                case types_js_1.BrowserTag.DEVEDITION:
                case types_js_1.BrowserTag.ESR:
                    throw new Error(`${tag.toUpperCase()} is not available for ChromeDriver`);
            }
        }
        case types_js_1.Browser.CHROMEHEADLESSSHELL: {
            switch (tag) {
                case types_js_1.BrowserTag.LATEST:
                case types_js_1.BrowserTag.CANARY:
                    return await chromeHeadlessShell.resolveBuildId(types_js_1.ChromeReleaseChannel.CANARY);
                case types_js_1.BrowserTag.BETA:
                    return await chromeHeadlessShell.resolveBuildId(types_js_1.ChromeReleaseChannel.BETA);
                case types_js_1.BrowserTag.DEV:
                    return await chromeHeadlessShell.resolveBuildId(types_js_1.ChromeReleaseChannel.DEV);
                case types_js_1.BrowserTag.STABLE:
                    return await chromeHeadlessShell.resolveBuildId(types_js_1.ChromeReleaseChannel.STABLE);
                case types_js_1.BrowserTag.NIGHTLY:
                case types_js_1.BrowserTag.DEVEDITION:
                case types_js_1.BrowserTag.ESR:
                    throw new Error(`${tag} is not available for chrome-headless-shell`);
            }
        }
        case types_js_1.Browser.CHROMIUM:
            switch (tag) {
                case types_js_1.BrowserTag.LATEST:
                    return await chromium.resolveBuildId(platform);
                case types_js_1.BrowserTag.NIGHTLY:
                case types_js_1.BrowserTag.CANARY:
                case types_js_1.BrowserTag.DEV:
                case types_js_1.BrowserTag.DEVEDITION:
                case types_js_1.BrowserTag.BETA:
                case types_js_1.BrowserTag.STABLE:
                case types_js_1.BrowserTag.ESR:
                    throw new Error(`${tag} is not supported for Chromium. Use 'latest' instead.`);
            }
    }
}
/**
 * @public
 */
async function resolveBuildId(browser, platform, tag) {
    const browserTag = tag;
    if (Object.values(types_js_1.BrowserTag).includes(browserTag)) {
        return await resolveBuildIdForBrowserTag(browser, platform, browserTag);
    }
    switch (browser) {
        case types_js_1.Browser.FIREFOX:
            return tag;
        case types_js_1.Browser.CHROME:
            const chromeResult = await chrome.resolveBuildId(tag);
            if (chromeResult) {
                return chromeResult;
            }
            return tag;
        case types_js_1.Browser.CHROMEDRIVER:
            const chromeDriverResult = await chromedriver.resolveBuildId(tag);
            if (chromeDriverResult) {
                return chromeDriverResult;
            }
            return tag;
        case types_js_1.Browser.CHROMEHEADLESSSHELL:
            const chromeHeadlessShellResult = await chromeHeadlessShell.resolveBuildId(tag);
            if (chromeHeadlessShellResult) {
                return chromeHeadlessShellResult;
            }
            return tag;
        case types_js_1.Browser.CHROMIUM:
            return tag;
    }
}
/**
 * @public
 */
async function createProfile(browser, opts) {
    switch (browser) {
        case types_js_1.Browser.FIREFOX:
            return await firefox.createProfile(opts);
        case types_js_1.Browser.CHROME:
        case types_js_1.Browser.CHROMIUM:
            throw new Error(`Profile creation is not support for ${browser} yet`);
    }
}
/**
 * @public
 *
 * Get's the first resolved system path
 */
function resolveSystemExecutablePath(browser, platform, channel) {
    switch (browser) {
        case types_js_1.Browser.CHROMEDRIVER:
        case types_js_1.Browser.CHROMEHEADLESSSHELL:
        case types_js_1.Browser.FIREFOX:
        case types_js_1.Browser.CHROMIUM:
            throw new Error(`System browser detection is not supported for ${browser} yet.`);
        case types_js_1.Browser.CHROME:
            return chrome.resolveSystemExecutablePaths(platform, channel)[0];
    }
}
/**
 * Returns the expected default user data dir for the given channel. It does not
 * check if the dir actually exists.
 *
 * @public
 */
function resolveDefaultUserDataDir(browser, platform, channel) {
    switch (browser) {
        case types_js_1.Browser.CHROMEDRIVER:
        case types_js_1.Browser.CHROMEHEADLESSSHELL:
        case types_js_1.Browser.FIREFOX:
        case types_js_1.Browser.CHROMIUM:
            throw new Error(`Default user dir detection is not supported for ${browser} yet.`);
        case types_js_1.Browser.CHROME:
            return chrome.resolveDefaultUserDataDir(platform, channel);
    }
}
/**
 * @internal
 *
 * Returns multiple paths where the executable may be located at on the current system
 * ordered by likelihood (based on heuristics).
 */
function resolveSystemExecutablePaths(browser, platform, channel) {
    switch (browser) {
        case types_js_1.Browser.CHROMEDRIVER:
        case types_js_1.Browser.CHROMEHEADLESSSHELL:
        case types_js_1.Browser.FIREFOX:
        case types_js_1.Browser.CHROMIUM:
            throw new Error(`System browser detection is not supported for ${browser} yet.`);
        case types_js_1.Browser.CHROME:
            return chrome.resolveSystemExecutablePaths(platform, channel);
    }
}
/**
 * Returns a version comparator for the given browser that can be used to sort
 * browser versions.
 *
 * @public
 */
function getVersionComparator(browser) {
    return exports.versionComparators[browser];
}
//# sourceMappingURL=browser-data.js.map