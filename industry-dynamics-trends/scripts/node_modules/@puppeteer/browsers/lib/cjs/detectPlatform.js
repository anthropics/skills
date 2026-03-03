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
exports.detectBrowserPlatform = detectBrowserPlatform;
const node_os_1 = __importDefault(require("node:os"));
const browser_data_js_1 = require("./browser-data/browser-data.js");
/**
 * @public
 */
function detectBrowserPlatform() {
    const platform = node_os_1.default.platform();
    const arch = node_os_1.default.arch();
    switch (platform) {
        case 'darwin':
            return arch === 'arm64' ? browser_data_js_1.BrowserPlatform.MAC_ARM : browser_data_js_1.BrowserPlatform.MAC;
        case 'linux':
            return arch === 'arm64'
                ? browser_data_js_1.BrowserPlatform.LINUX_ARM
                : browser_data_js_1.BrowserPlatform.LINUX;
        case 'win32':
            return arch === 'x64' ||
                // Windows 11 for ARM supports x64 emulation
                (arch === 'arm64' && isWindows11(node_os_1.default.release()))
                ? browser_data_js_1.BrowserPlatform.WIN64
                : browser_data_js_1.BrowserPlatform.WIN32;
        default:
            return undefined;
    }
}
/**
 * Windows 11 is identified by the version 10.0.22000 or greater
 * @internal
 */
function isWindows11(version) {
    const parts = version.split('.');
    if (parts.length > 2) {
        const major = parseInt(parts[0], 10);
        const minor = parseInt(parts[1], 10);
        const patch = parseInt(parts[2], 10);
        return (major > 10 ||
            (major === 10 && minor > 0) ||
            (major === 10 && minor === 0 && patch >= 22000));
    }
    return false;
}
//# sourceMappingURL=detectPlatform.js.map