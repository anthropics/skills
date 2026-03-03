"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
exports.compareVersions = exports.resolveBuildId = void 0;
exports.resolveDownloadUrl = resolveDownloadUrl;
exports.resolveDownloadPath = resolveDownloadPath;
exports.relativeExecutablePath = relativeExecutablePath;
/**
 * @license
 * Copyright 2023 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
const node_path_1 = __importDefault(require("node:path"));
const types_js_1 = require("./types.js");
function folder(platform) {
    switch (platform) {
        case types_js_1.BrowserPlatform.LINUX_ARM:
        case types_js_1.BrowserPlatform.LINUX:
            return 'linux64';
        case types_js_1.BrowserPlatform.MAC_ARM:
            return 'mac-arm64';
        case types_js_1.BrowserPlatform.MAC:
            return 'mac-x64';
        case types_js_1.BrowserPlatform.WIN32:
            return 'win32';
        case types_js_1.BrowserPlatform.WIN64:
            return 'win64';
    }
}
function resolveDownloadUrl(platform, buildId, baseUrl = 'https://storage.googleapis.com/chrome-for-testing-public') {
    return `${baseUrl}/${resolveDownloadPath(platform, buildId).join('/')}`;
}
function resolveDownloadPath(platform, buildId) {
    return [
        buildId,
        folder(platform),
        `chrome-headless-shell-${folder(platform)}.zip`,
    ];
}
function relativeExecutablePath(platform, _buildId) {
    switch (platform) {
        case types_js_1.BrowserPlatform.MAC:
        case types_js_1.BrowserPlatform.MAC_ARM:
            return node_path_1.default.join('chrome-headless-shell-' + folder(platform), 'chrome-headless-shell');
        case types_js_1.BrowserPlatform.LINUX_ARM:
        case types_js_1.BrowserPlatform.LINUX:
            return node_path_1.default.join('chrome-headless-shell-linux64', 'chrome-headless-shell');
        case types_js_1.BrowserPlatform.WIN32:
        case types_js_1.BrowserPlatform.WIN64:
            return node_path_1.default.join('chrome-headless-shell-' + folder(platform), 'chrome-headless-shell.exe');
    }
}
var chrome_js_1 = require("./chrome.js");
Object.defineProperty(exports, "resolveBuildId", { enumerable: true, get: function () { return chrome_js_1.resolveBuildId; } });
Object.defineProperty(exports, "compareVersions", { enumerable: true, get: function () { return chrome_js_1.compareVersions; } });
//# sourceMappingURL=chrome-headless-shell.js.map