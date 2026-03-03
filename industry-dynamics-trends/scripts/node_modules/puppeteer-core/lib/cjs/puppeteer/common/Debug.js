"use strict";
/**
 * @license
 * Copyright 2020 Google Inc.
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
exports.debug = void 0;
exports.importDebug = importDebug;
exports.setLogCapture = setLogCapture;
exports.getCapturedLogs = getCapturedLogs;
const environment_js_1 = require("../environment.js");
/**
 * @internal
 */
let debugModule = null;
/**
 * @internal
 */
async function importDebug() {
    if (!debugModule) {
        debugModule = (await Promise.resolve().then(() => __importStar(require('debug')))).default;
    }
    return debugModule;
}
/**
 * A debug function that can be used in any environment.
 *
 * @remarks
 * If used in Node, it falls back to the
 * {@link https://www.npmjs.com/package/debug | debug module}. In the browser it
 * uses `console.log`.
 *
 * In Node, use the `DEBUG` environment variable to control logging:
 *
 * ```
 * DEBUG=* // logs all channels
 * DEBUG=foo // logs the `foo` channel
 * DEBUG=foo* // logs any channels starting with `foo`
 * ```
 *
 * In the browser, set `window.__PUPPETEER_DEBUG` to a string:
 *
 * ```
 * window.__PUPPETEER_DEBUG='*'; // logs all channels
 * window.__PUPPETEER_DEBUG='foo'; // logs the `foo` channel
 * window.__PUPPETEER_DEBUG='foo*'; // logs any channels starting with `foo`
 * ```
 *
 * @example
 *
 * ```
 * const log = debug('Page');
 *
 * log('new page created')
 * // logs "Page: new page created"
 * ```
 *
 * @param prefix - this will be prefixed to each log.
 * @returns a function that can be called to log to that debug channel.
 *
 * @internal
 */
const debug = (prefix) => {
    if (environment_js_1.isNode) {
        return async (...logArgs) => {
            if (captureLogs) {
                capturedLogs.push(prefix + logArgs);
            }
            (await importDebug())(prefix)(logArgs);
        };
    }
    return (...logArgs) => {
        const debugLevel = globalThis.__PUPPETEER_DEBUG;
        if (!debugLevel) {
            return;
        }
        const everythingShouldBeLogged = debugLevel === '*';
        const prefixMatchesDebugLevel = everythingShouldBeLogged ||
            /**
             * If the debug level is `foo*`, that means we match any prefix that
             * starts with `foo`. If the level is `foo`, we match only the prefix
             * `foo`.
             */
            (debugLevel.endsWith('*')
                ? prefix.startsWith(debugLevel)
                : prefix === debugLevel);
        if (!prefixMatchesDebugLevel) {
            return;
        }
        console.log(`${prefix}:`, ...logArgs);
    };
};
exports.debug = debug;
/**
 * @internal
 */
let capturedLogs = [];
/**
 * @internal
 */
let captureLogs = false;
/**
 * @internal
 */
function setLogCapture(value) {
    capturedLogs = [];
    captureLogs = value;
}
/**
 * @internal
 */
function getCapturedLogs() {
    return capturedLogs;
}
//# sourceMappingURL=Debug.js.map