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
exports.ChromeLauncher = void 0;
exports.getFeatures = getFeatures;
exports.removeMatchingFlags = removeMatchingFlags;
const promises_1 = require("node:fs/promises");
const node_os_1 = __importDefault(require("node:os"));
const node_path_1 = __importDefault(require("node:path"));
const browsers_1 = require("@puppeteer/browsers");
const util_js_1 = require("../common/util.js");
const assert_js_1 = require("../util/assert.js");
const BrowserLauncher_js_1 = require("./BrowserLauncher.js");
const LaunchOptions_js_1 = require("./LaunchOptions.js");
const fs_js_1 = require("./util/fs.js");
/**
 * @internal
 */
class ChromeLauncher extends BrowserLauncher_js_1.BrowserLauncher {
    constructor(puppeteer) {
        super(puppeteer, 'chrome');
    }
    launch(options = {}) {
        if (this.puppeteer.configuration.logLevel === 'warn' &&
            process.platform === 'darwin' &&
            process.arch === 'x64') {
            const cpus = node_os_1.default.cpus();
            if (cpus[0]?.model.includes('Apple')) {
                console.warn([
                    '\x1B[1m\x1B[43m\x1B[30m',
                    'Degraded performance warning:\x1B[0m\x1B[33m',
                    'Launching Chrome on Mac Silicon (arm64) from an x64 Node installation results in',
                    'Rosetta translating the Chrome binary, even if Chrome is already arm64. This would',
                    'result in huge performance issues. To resolve this, you must run Puppeteer with',
                    'a version of Node built for arm64.',
                ].join('\n  '));
            }
        }
        return super.launch(options);
    }
    /**
     * @internal
     */
    async computeLaunchArguments(options = {}) {
        const { ignoreDefaultArgs = false, args = [], pipe = false, debuggingPort, channel, executablePath, } = options;
        const chromeArguments = [];
        if (!ignoreDefaultArgs) {
            chromeArguments.push(...this.defaultArgs(options));
        }
        else if (Array.isArray(ignoreDefaultArgs)) {
            chromeArguments.push(...this.defaultArgs(options).filter(arg => {
                return !ignoreDefaultArgs.includes(arg);
            }));
        }
        else {
            chromeArguments.push(...args);
        }
        if (!chromeArguments.some(argument => {
            return argument.startsWith('--remote-debugging-');
        })) {
            if (pipe) {
                (0, assert_js_1.assert)(!debuggingPort, 'Browser should be launched with either pipe or debugging port - not both.');
                chromeArguments.push('--remote-debugging-pipe');
            }
            else {
                chromeArguments.push(`--remote-debugging-port=${debuggingPort || 0}`);
            }
        }
        let isTempUserDataDir = false;
        // Check for the user data dir argument, which will always be set even
        // with a custom directory specified via the userDataDir option.
        let userDataDirIndex = chromeArguments.findIndex(arg => {
            return arg.startsWith('--user-data-dir');
        });
        if (userDataDirIndex < 0) {
            isTempUserDataDir = true;
            chromeArguments.push(`--user-data-dir=${await (0, promises_1.mkdtemp)(this.getProfilePath())}`);
            userDataDirIndex = chromeArguments.length - 1;
        }
        const userDataDir = chromeArguments[userDataDirIndex].split('=', 2)[1];
        (0, assert_js_1.assert)(typeof userDataDir === 'string', '`--user-data-dir` is malformed');
        let chromeExecutable = executablePath;
        if (!chromeExecutable) {
            (0, assert_js_1.assert)(channel || !this.puppeteer._isPuppeteerCore, `An \`executablePath\` or \`channel\` must be specified for \`puppeteer-core\``);
            chromeExecutable = channel
                ? this.executablePath(channel)
                : this.resolveExecutablePath(options.headless ?? true);
        }
        return {
            executablePath: chromeExecutable,
            args: chromeArguments,
            isTempUserDataDir,
            userDataDir,
        };
    }
    /**
     * @internal
     */
    async cleanUserDataDir(path, opts) {
        if (opts.isTemp) {
            try {
                await (0, fs_js_1.rm)(path);
            }
            catch (error) {
                (0, util_js_1.debugError)(error);
                throw error;
            }
        }
    }
    defaultArgs(options = {}) {
        // See https://github.com/GoogleChrome/chrome-launcher/blob/main/docs/chrome-flags-for-tools.md
        const userDisabledFeatures = getFeatures('--disable-features', options.args);
        if (options.args && userDisabledFeatures.length > 0) {
            removeMatchingFlags(options.args, '--disable-features');
        }
        const turnOnExperimentalFeaturesForTesting = process.env['PUPPETEER_TEST_EXPERIMENTAL_CHROME_FEATURES'] === 'true';
        // Merge default disabled features with user-provided ones, if any.
        const disabledFeatures = [
            'Translate',
            // AcceptCHFrame disabled because of crbug.com/1348106.
            'AcceptCHFrame',
            'MediaRouter',
            'OptimizationHints',
            'RenderDocument', // https://crbug.com/444150315
            ...(turnOnExperimentalFeaturesForTesting
                ? []
                : [
                    // https://crbug.com/1492053
                    'ProcessPerSiteUpToMainFrameThreshold',
                    // https://github.com/puppeteer/puppeteer/issues/10715
                    'IsolateSandboxedIframes',
                ]),
            ...userDisabledFeatures,
        ].filter(feature => {
            return feature !== '';
        });
        const userEnabledFeatures = getFeatures('--enable-features', options.args);
        if (options.args && userEnabledFeatures.length > 0) {
            removeMatchingFlags(options.args, '--enable-features');
        }
        // Merge default enabled features with user-provided ones, if any.
        const enabledFeatures = [
            'PdfOopif',
            // Add features to enable by default here.
            ...userEnabledFeatures,
        ].filter(feature => {
            return feature !== '';
        });
        const chromeArguments = [
            '--allow-pre-commit-input',
            '--disable-background-networking',
            '--disable-background-timer-throttling',
            '--disable-backgrounding-occluded-windows',
            '--disable-breakpad',
            '--disable-client-side-phishing-detection',
            '--disable-component-extensions-with-background-pages',
            '--disable-crash-reporter', // No crash reporting in CfT.
            '--disable-default-apps',
            '--disable-dev-shm-usage',
            '--disable-hang-monitor',
            '--disable-infobars',
            '--disable-ipc-flooding-protection',
            '--disable-popup-blocking',
            '--disable-prompt-on-repost',
            '--disable-renderer-backgrounding',
            '--disable-search-engine-choice-screen',
            '--disable-sync',
            '--enable-automation',
            '--export-tagged-pdf',
            '--force-color-profile=srgb',
            '--generate-pdf-document-outline',
            '--metrics-recording-only',
            '--no-first-run',
            '--password-store=basic',
            '--use-mock-keychain',
            `--disable-features=${disabledFeatures.join(',')}`,
            `--enable-features=${enabledFeatures.join(',')}`,
        ].filter(arg => {
            return arg !== '';
        });
        const { devtools = false, headless = !devtools, args = [], userDataDir, enableExtensions = false, } = options;
        if (userDataDir) {
            // If absolute (for any platform) path is given, we should not resolve it.
            chromeArguments.push(`--user-data-dir=${node_path_1.default.posix.isAbsolute(userDataDir) || node_path_1.default.win32.isAbsolute(userDataDir) ? userDataDir : node_path_1.default.resolve(userDataDir)}`);
        }
        if (devtools) {
            chromeArguments.push('--auto-open-devtools-for-tabs');
        }
        if (headless) {
            chromeArguments.push(headless === 'shell' ? '--headless' : '--headless=new', '--hide-scrollbars', '--mute-audio');
        }
        chromeArguments.push(enableExtensions
            ? '--enable-unsafe-extension-debugging'
            : '--disable-extensions');
        if (args.every(arg => {
            return arg.startsWith('-');
        })) {
            chromeArguments.push('about:blank');
        }
        chromeArguments.push(...args);
        return chromeArguments;
    }
    executablePath(channel, validatePath = true) {
        if (channel) {
            return (0, browsers_1.computeSystemExecutablePath)({
                browser: browsers_1.Browser.CHROME,
                channel: (0, LaunchOptions_js_1.convertPuppeteerChannelToBrowsersChannel)(channel),
            });
        }
        else {
            return this.resolveExecutablePath(undefined, validatePath);
        }
    }
}
exports.ChromeLauncher = ChromeLauncher;
/**
 * Extracts all features from the given command-line flag
 * (e.g. `--enable-features`, `--enable-features=`).
 *
 * Example input:
 * ["--enable-features=NetworkService,NetworkServiceInProcess", "--enable-features=Foo"]
 *
 * Example output:
 * ["NetworkService", "NetworkServiceInProcess", "Foo"]
 *
 * @internal
 */
function getFeatures(flag, options = []) {
    return options
        .filter(s => {
        return s.startsWith(flag.endsWith('=') ? flag : `${flag}=`);
    })
        .map(s => {
        return s.split(new RegExp(`${flag}=\\s*`))[1]?.trim();
    })
        .filter(s => {
        return s;
    });
}
/**
 * Removes all elements in-place from the given string array
 * that match the given command-line flag.
 *
 * @internal
 */
function removeMatchingFlags(array, flag) {
    const regex = new RegExp(`^${flag}=.*`);
    let i = 0;
    while (i < array.length) {
        if (regex.test(array[i])) {
            array.splice(i, 1);
        }
        else {
            i++;
        }
    }
    return array;
}
//# sourceMappingURL=ChromeLauncher.js.map