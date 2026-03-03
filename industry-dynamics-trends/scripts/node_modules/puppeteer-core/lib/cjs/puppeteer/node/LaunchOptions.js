"use strict";
/**
 * @license
 * Copyright 2020 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
Object.defineProperty(exports, "__esModule", { value: true });
exports.convertPuppeteerChannelToBrowsersChannel = convertPuppeteerChannelToBrowsersChannel;
const browsers_1 = require("@puppeteer/browsers");
/**
 * @internal
 */
function convertPuppeteerChannelToBrowsersChannel(channel) {
    switch (channel) {
        case 'chrome':
            return browsers_1.ChromeReleaseChannel.STABLE;
        case 'chrome-dev':
            return browsers_1.ChromeReleaseChannel.DEV;
        case 'chrome-beta':
            return browsers_1.ChromeReleaseChannel.BETA;
        case 'chrome-canary':
            return browsers_1.ChromeReleaseChannel.CANARY;
    }
}
//# sourceMappingURL=LaunchOptions.js.map