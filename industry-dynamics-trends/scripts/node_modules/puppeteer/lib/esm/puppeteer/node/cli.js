#!/usr/bin/env node
/**
 * @license
 * Copyright 2023 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
import { CLI, Browser } from '@puppeteer/browsers';
import { PUPPETEER_REVISIONS } from 'puppeteer-core/internal/revisions.js';
import { packageVersion } from 'puppeteer-core/internal/util/version.js';
import puppeteer from '../puppeteer.js';
const cacheDir = puppeteer.configuration
    .cacheDirectory;
void new CLI({
    cachePath: cacheDir,
    scriptName: 'puppeteer',
    version: packageVersion,
    prefixCommand: {
        cmd: 'browsers',
        description: 'Manage browsers of this Puppeteer installation',
    },
    allowCachePathOverride: false,
    pinnedBrowsers: {
        [Browser.CHROME]: {
            buildId: puppeteer.configuration.chrome?.version ||
                PUPPETEER_REVISIONS['chrome'] ||
                'latest',
            skipDownload: puppeteer.configuration.chrome
                ?.skipDownload ?? false,
        },
        [Browser.FIREFOX]: {
            buildId: puppeteer.configuration.firefox
                ?.version ||
                PUPPETEER_REVISIONS['firefox'] ||
                'latest',
            skipDownload: puppeteer.configuration.firefox
                ?.skipDownload ?? true,
        },
        [Browser.CHROMEHEADLESSSHELL]: {
            buildId: puppeteer.configuration['chrome-headless-shell']?.version ||
                PUPPETEER_REVISIONS['chrome-headless-shell'] ||
                'latest',
            skipDownload: puppeteer.configuration['chrome-headless-shell']?.skipDownload ?? false,
        },
    },
}).run(process.argv);
//# sourceMappingURL=cli.js.map