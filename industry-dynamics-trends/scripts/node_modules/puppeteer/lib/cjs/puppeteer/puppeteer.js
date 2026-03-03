"use strict";
/**
 * @license
 * Copyright 2017 Google Inc.
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
var __exportStar = (this && this.__exportStar) || function(m, exports) {
    for (var p in m) if (p !== "default" && !Object.prototype.hasOwnProperty.call(exports, p)) __createBinding(exports, m, p);
};
Object.defineProperty(exports, "__esModule", { value: true });
exports.trimCache = exports.launch = exports.executablePath = exports.defaultArgs = exports.connect = void 0;
__exportStar(require("puppeteer-core"), exports);
const puppeteer_core_1 = require("puppeteer-core");
const getConfiguration_js_1 = require("./getConfiguration.js");
const configuration = (0, getConfiguration_js_1.getConfiguration)();
/**
 * @public
 */
// @ts-expect-error using internal API.
const puppeteer = new puppeteer_core_1.PuppeteerNode({
    isPuppeteerCore: false,
    configuration,
});
/**
 * @public
 */
exports.connect = puppeteer.connect, 
/**
 * @public
 */
exports.defaultArgs = puppeteer.defaultArgs, 
/**
 * @public
 */
exports.executablePath = puppeteer.executablePath, 
/**
 * @public
 */
exports.launch = puppeteer.launch, 
/**
 * @public
 */
exports.trimCache = puppeteer.trimCache;
exports.default = puppeteer;
//# sourceMappingURL=puppeteer.js.map