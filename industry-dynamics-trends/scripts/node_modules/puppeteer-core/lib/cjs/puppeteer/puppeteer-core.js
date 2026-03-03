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
var __setModuleDefault = (this && this.__setModuleDefault) || (Object.create ? (function(o, v) {
    Object.defineProperty(o, "default", { enumerable: true, value: v });
}) : function(o, v) {
    o["default"] = v;
});
var __exportStar = (this && this.__exportStar) || function(m, exports) {
    for (var p in m) if (p !== "default" && !Object.prototype.hasOwnProperty.call(exports, p)) __createBinding(exports, m, p);
};
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
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
exports.launch = exports.executablePath = exports.defaultArgs = exports.connect = void 0;
__exportStar(require("./index.js"), exports);
const node_fs_1 = __importDefault(require("node:fs"));
const node_path_1 = __importDefault(require("node:path"));
const environment_js_1 = require("./environment.js");
const Puppeteer = __importStar(require("./index.js"));
// Set up Node-specific environment dependencies.
environment_js_1.environment.value = {
    fs: node_fs_1.default,
    path: node_path_1.default,
    ScreenRecorder: Puppeteer.ScreenRecorder,
};
/**
 * @public
 */
const puppeteer = new Puppeteer.PuppeteerNode({
    isPuppeteerCore: true,
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
exports.launch = puppeteer.launch;
exports.default = puppeteer;
//# sourceMappingURL=puppeteer-core.js.map