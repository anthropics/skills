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
exports.FirefoxLauncher = void 0;
const node_fs_1 = __importDefault(require("node:fs"));
const promises_1 = require("node:fs/promises");
const node_os_1 = __importDefault(require("node:os"));
const node_path_1 = __importDefault(require("node:path"));
const browsers_1 = require("@puppeteer/browsers");
const util_js_1 = require("../common/util.js");
const assert_js_1 = require("../util/assert.js");
const BrowserLauncher_js_1 = require("./BrowserLauncher.js");
const fs_js_1 = require("./util/fs.js");
/**
 * @internal
 */
class FirefoxLauncher extends BrowserLauncher_js_1.BrowserLauncher {
    constructor(puppeteer) {
        super(puppeteer, 'firefox');
    }
    static getPreferences(extraPrefsFirefox) {
        return {
            ...extraPrefsFirefox,
            // Force all web content to use a single content process. TODO: remove
            // this once Firefox supports mouse event dispatch from the main frame
            // context. See https://bugzilla.mozilla.org/show_bug.cgi?id=1773393.
            'fission.webContentIsolationStrategy': 0,
        };
    }
    /**
     * @internal
     */
    async computeLaunchArguments(options = {}) {
        const { ignoreDefaultArgs = false, args = [], executablePath, pipe = false, extraPrefsFirefox = {}, debuggingPort = null, } = options;
        const firefoxArguments = [];
        if (!ignoreDefaultArgs) {
            firefoxArguments.push(...this.defaultArgs(options));
        }
        else if (Array.isArray(ignoreDefaultArgs)) {
            firefoxArguments.push(...this.defaultArgs(options).filter(arg => {
                return !ignoreDefaultArgs.includes(arg);
            }));
        }
        else {
            firefoxArguments.push(...args);
        }
        if (!firefoxArguments.some(argument => {
            return argument.startsWith('--remote-debugging-');
        })) {
            if (pipe) {
                (0, assert_js_1.assert)(debuggingPort === null, 'Browser should be launched with either pipe or debugging port - not both.');
            }
            firefoxArguments.push(`--remote-debugging-port=${debuggingPort || 0}`);
        }
        let userDataDir;
        let isTempUserDataDir = true;
        // Check for the profile argument, which will always be set even
        // with a custom directory specified via the userDataDir option.
        const profileArgIndex = firefoxArguments.findIndex(arg => {
            return ['-profile', '--profile'].includes(arg);
        });
        if (profileArgIndex !== -1) {
            userDataDir = firefoxArguments[profileArgIndex + 1];
            if (!userDataDir) {
                throw new Error(`Missing value for profile command line argument`);
            }
            // When using a custom Firefox profile it needs to be populated
            // with required preferences.
            isTempUserDataDir = false;
        }
        else {
            userDataDir = await (0, promises_1.mkdtemp)(this.getProfilePath());
            firefoxArguments.push('--profile');
            firefoxArguments.push(userDataDir);
        }
        await (0, browsers_1.createProfile)(browsers_1.Browser.FIREFOX, {
            path: userDataDir,
            preferences: FirefoxLauncher.getPreferences(extraPrefsFirefox),
        });
        let firefoxExecutable;
        if (this.puppeteer._isPuppeteerCore || executablePath) {
            (0, assert_js_1.assert)(executablePath, `An \`executablePath\` must be specified for \`puppeteer-core\``);
            firefoxExecutable = executablePath;
        }
        else {
            firefoxExecutable = this.executablePath(undefined);
        }
        return {
            isTempUserDataDir,
            userDataDir,
            args: firefoxArguments,
            executablePath: firefoxExecutable,
        };
    }
    /**
     * @internal
     */
    async cleanUserDataDir(userDataDir, opts) {
        if (opts.isTemp) {
            try {
                await (0, fs_js_1.rm)(userDataDir);
            }
            catch (error) {
                (0, util_js_1.debugError)(error);
                throw error;
            }
        }
        else {
            try {
                const backupSuffix = '.puppeteer';
                const backupFiles = ['prefs.js', 'user.js'];
                const results = await Promise.allSettled(backupFiles.map(async (file) => {
                    const prefsBackupPath = node_path_1.default.join(userDataDir, file + backupSuffix);
                    if (node_fs_1.default.existsSync(prefsBackupPath)) {
                        const prefsPath = node_path_1.default.join(userDataDir, file);
                        await (0, promises_1.unlink)(prefsPath);
                        await (0, promises_1.rename)(prefsBackupPath, prefsPath);
                    }
                }));
                for (const result of results) {
                    if (result.status === 'rejected') {
                        throw result.reason;
                    }
                }
            }
            catch (error) {
                (0, util_js_1.debugError)(error);
            }
        }
    }
    executablePath(_, validatePath = true) {
        return this.resolveExecutablePath(undefined, 
        /* validatePath=*/ validatePath);
    }
    defaultArgs(options = {}) {
        const { devtools = false, headless = !devtools, args = [], userDataDir = null, } = options;
        const firefoxArguments = [];
        switch (node_os_1.default.platform()) {
            case 'darwin':
                firefoxArguments.push('--foreground');
                break;
            case 'win32':
                firefoxArguments.push('--wait-for-browser');
                break;
        }
        if (userDataDir) {
            firefoxArguments.push('--profile');
            firefoxArguments.push(userDataDir);
        }
        if (headless) {
            firefoxArguments.push('--headless');
        }
        if (devtools) {
            firefoxArguments.push('--devtools');
        }
        if (args.every(arg => {
            return arg.startsWith('-');
        })) {
            firefoxArguments.push('about:blank');
        }
        firefoxArguments.push(...args);
        return firefoxArguments;
    }
}
exports.FirefoxLauncher = FirefoxLauncher;
//# sourceMappingURL=FirefoxLauncher.js.map