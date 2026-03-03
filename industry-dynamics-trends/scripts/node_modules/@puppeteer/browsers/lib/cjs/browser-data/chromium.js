"use strict";
/**
 * @license
 * Copyright 2023 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
exports.resolveDownloadUrl = resolveDownloadUrl;
exports.resolveDownloadPath = resolveDownloadPath;
exports.relativeExecutablePath = relativeExecutablePath;
exports.resolveBuildId = resolveBuildId;
exports.compareVersions = compareVersions;
const node_path_1 = __importDefault(require("node:path"));
const httpUtil_js_1 = require("../httpUtil.js");
const types_js_1 = require("./types.js");
function archive(platform, buildId) {
    switch (platform) {
        case types_js_1.BrowserPlatform.LINUX_ARM:
        case types_js_1.BrowserPlatform.LINUX:
            return 'chrome-linux';
        case types_js_1.BrowserPlatform.MAC_ARM:
        case types_js_1.BrowserPlatform.MAC:
            return 'chrome-mac';
        case types_js_1.BrowserPlatform.WIN32:
        case types_js_1.BrowserPlatform.WIN64:
            // Windows archive name changed at r591479.
            return parseInt(buildId, 10) > 591479 ? 'chrome-win' : 'chrome-win32';
    }
}
function folder(platform) {
    switch (platform) {
        case types_js_1.BrowserPlatform.LINUX_ARM:
        case types_js_1.BrowserPlatform.LINUX:
            return 'Linux_x64';
        case types_js_1.BrowserPlatform.MAC_ARM:
            return 'Mac_Arm';
        case types_js_1.BrowserPlatform.MAC:
            return 'Mac';
        case types_js_1.BrowserPlatform.WIN32:
            return 'Win';
        case types_js_1.BrowserPlatform.WIN64:
            return 'Win_x64';
    }
}
function resolveDownloadUrl(platform, buildId, baseUrl = 'https://storage.googleapis.com/chromium-browser-snapshots') {
    return `${baseUrl}/${resolveDownloadPath(platform, buildId).join('/')}`;
}
function resolveDownloadPath(platform, buildId) {
    return [folder(platform), buildId, `${archive(platform, buildId)}.zip`];
}
function relativeExecutablePath(platform, _buildId) {
    switch (platform) {
        case types_js_1.BrowserPlatform.MAC:
        case types_js_1.BrowserPlatform.MAC_ARM:
            return node_path_1.default.join('chrome-mac', 'Chromium.app', 'Contents', 'MacOS', 'Chromium');
        case types_js_1.BrowserPlatform.LINUX_ARM:
        case types_js_1.BrowserPlatform.LINUX:
            return node_path_1.default.join('chrome-linux', 'chrome');
        case types_js_1.BrowserPlatform.WIN32:
        case types_js_1.BrowserPlatform.WIN64:
            return node_path_1.default.join('chrome-win', 'chrome.exe');
    }
}
async function resolveBuildId(platform) {
    return await (0, httpUtil_js_1.getText)(new URL(`https://storage.googleapis.com/chromium-browser-snapshots/${folder(platform)}/LAST_CHANGE`));
}
function compareVersions(a, b) {
    return Number(a) - Number(b);
}
//# sourceMappingURL=chromium.js.map