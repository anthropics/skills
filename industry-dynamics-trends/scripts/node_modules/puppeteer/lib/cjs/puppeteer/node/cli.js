#!/usr/bin/env node
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
const browsers_1 = require("@puppeteer/browsers");
const revisions_js_1 = require("puppeteer-core/internal/revisions.js");
const version_js_1 = require("puppeteer-core/internal/util/version.js");
const puppeteer_js_1 = __importDefault(require("../puppeteer.js"));
const cacheDir = puppeteer_js_1.default.configuration
    .cacheDirectory;
void new browsers_1.CLI({
    cachePath: cacheDir,
    scriptName: 'puppeteer',
    version: version_js_1.packageVersion,
    prefixCommand: {
        cmd: 'browsers',
        description: 'Manage browsers of this Puppeteer installation',
    },
    allowCachePathOverride: false,
    pinnedBrowsers: {
        [browsers_1.Browser.CHROME]: {
            buildId: puppeteer_js_1.default.configuration.chrome?.version ||
                revisions_js_1.PUPPETEER_REVISIONS['chrome'] ||
                'latest',
            skipDownload: puppeteer_js_1.default.configuration.chrome
                ?.skipDownload ?? false,
        },
        [browsers_1.Browser.FIREFOX]: {
            buildId: puppeteer_js_1.default.configuration.firefox
                ?.version ||
                revisions_js_1.PUPPETEER_REVISIONS['firefox'] ||
                'latest',
            skipDownload: puppeteer_js_1.default.configuration.firefox
                ?.skipDownload ?? true,
        },
        [browsers_1.Browser.CHROMEHEADLESSSHELL]: {
            buildId: puppeteer_js_1.default.configuration['chrome-headless-shell']?.version ||
                revisions_js_1.PUPPETEER_REVISIONS['chrome-headless-shell'] ||
                'latest',
            skipDownload: puppeteer_js_1.default.configuration['chrome-headless-shell']?.skipDownload ?? false,
        },
    },
}).run(process.argv);
//# sourceMappingURL=cli.js.map