"use strict";
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
exports.BrowserLauncher = void 0;
/**
 * @license
 * Copyright 2017 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
const node_fs_1 = require("node:fs");
const node_os_1 = require("node:os");
const node_path_1 = require("node:path");
const browsers_1 = require("@puppeteer/browsers");
const rxjs_js_1 = require("../../third_party/rxjs/rxjs.js");
const Browser_js_1 = require("../cdp/Browser.js");
const Connection_js_1 = require("../cdp/Connection.js");
const Errors_js_1 = require("../common/Errors.js");
const util_js_1 = require("../common/util.js");
const incremental_id_generator_js_1 = require("../util/incremental-id-generator.js");
const NodeWebSocketTransport_js_1 = require("./NodeWebSocketTransport.js");
const PipeTransport_js_1 = require("./PipeTransport.js");
/**
 * Describes a launcher - a class that is able to create and launch a browser instance.
 *
 * @public
 */
class BrowserLauncher {
    #browser;
    /**
     * @internal
     */
    puppeteer;
    /**
     * @internal
     */
    constructor(puppeteer, browser) {
        this.puppeteer = puppeteer;
        this.#browser = browser;
    }
    get browser() {
        return this.#browser;
    }
    async launch(options = {}) {
        const { dumpio = false, enableExtensions = false, env = process.env, handleSIGINT = true, handleSIGTERM = true, handleSIGHUP = true, acceptInsecureCerts = false, networkEnabled = true, defaultViewport = util_js_1.DEFAULT_VIEWPORT, downloadBehavior, slowMo = 0, timeout = 30000, waitForInitialPage = true, protocolTimeout, handleDevToolsAsPage, idGenerator = (0, incremental_id_generator_js_1.createIncrementalIdGenerator)(), } = options;
        let { protocol } = options;
        // Default to 'webDriverBiDi' for Firefox.
        if (this.#browser === 'firefox' && protocol === undefined) {
            protocol = 'webDriverBiDi';
        }
        if (this.#browser === 'firefox' && protocol === 'cdp') {
            throw new Error('Connecting to Firefox using CDP is no longer supported');
        }
        const launchArgs = await this.computeLaunchArguments({
            ...options,
            protocol,
        });
        if (!(0, node_fs_1.existsSync)(launchArgs.executablePath)) {
            throw new Error(`Browser was not found at the configured executablePath (${launchArgs.executablePath})`);
        }
        const usePipe = launchArgs.args.includes('--remote-debugging-pipe');
        const onProcessExit = async () => {
            await this.cleanUserDataDir(launchArgs.userDataDir, {
                isTemp: launchArgs.isTempUserDataDir,
            });
        };
        if (this.#browser === 'firefox' &&
            protocol === 'webDriverBiDi' &&
            usePipe) {
            throw new Error('Pipe connections are not supported with Firefox and WebDriver BiDi');
        }
        const browserProcess = (0, browsers_1.launch)({
            executablePath: launchArgs.executablePath,
            args: launchArgs.args,
            handleSIGHUP,
            handleSIGTERM,
            handleSIGINT,
            dumpio,
            env,
            pipe: usePipe,
            onExit: onProcessExit,
            signal: options.signal,
        });
        let browser;
        let cdpConnection;
        let closing = false;
        const browserCloseCallback = async () => {
            if (closing) {
                return;
            }
            closing = true;
            await this.closeBrowser(browserProcess, cdpConnection);
        };
        try {
            if (this.#browser === 'firefox') {
                browser = await this.createBiDiBrowser(browserProcess, browserCloseCallback, {
                    timeout,
                    protocolTimeout,
                    slowMo,
                    defaultViewport,
                    acceptInsecureCerts,
                    networkEnabled,
                    idGenerator,
                });
            }
            else {
                if (usePipe) {
                    cdpConnection = await this.createCdpPipeConnection(browserProcess, {
                        timeout,
                        protocolTimeout,
                        slowMo,
                        idGenerator,
                    });
                }
                else {
                    cdpConnection = await this.createCdpSocketConnection(browserProcess, {
                        timeout,
                        protocolTimeout,
                        slowMo,
                        idGenerator,
                    });
                }
                if (protocol === 'webDriverBiDi') {
                    browser = await this.createBiDiOverCdpBrowser(browserProcess, cdpConnection, browserCloseCallback, {
                        defaultViewport,
                        acceptInsecureCerts,
                        networkEnabled,
                    });
                }
                else {
                    browser = await Browser_js_1.CdpBrowser._create(cdpConnection, [], acceptInsecureCerts, defaultViewport, downloadBehavior, browserProcess.nodeProcess, browserCloseCallback, options.targetFilter, undefined, undefined, networkEnabled, handleDevToolsAsPage);
                }
            }
        }
        catch (error) {
            void browserCloseCallback();
            const logs = browserProcess.getRecentLogs().join('\n');
            if (logs.includes('Failed to create a ProcessSingleton for your profile directory') ||
                // On Windows we will not get logs due to the singleton process
                // handover. See
                // https://source.chromium.org/chromium/chromium/src/+/main:chrome/browser/process_singleton_win.cc;l=46;drc=fc7952f0422b5073515a205a04ec9c3a1ae81658
                (process.platform === 'win32' &&
                    (0, node_fs_1.existsSync)((0, node_path_1.join)(launchArgs.userDataDir, 'lockfile')))) {
                throw new Error(`The browser is already running for ${launchArgs.userDataDir}. Use a different \`userDataDir\` or stop the running browser first.`);
            }
            if (logs.includes('Missing X server') && options.headless === false) {
                throw new Error(`Missing X server to start the headful browser. Either set headless to true or use xvfb-run to run your Puppeteer script.`);
            }
            if (error instanceof browsers_1.TimeoutError) {
                throw new Errors_js_1.TimeoutError(error.message);
            }
            throw error;
        }
        if (Array.isArray(enableExtensions)) {
            if (this.#browser === 'chrome' && !usePipe) {
                throw new Error('To use `enableExtensions` with a list of paths in Chrome, you must be connected with `--remote-debugging-pipe` (`pipe: true`).');
            }
            await Promise.all([
                enableExtensions.map(path => {
                    return browser.installExtension(path);
                }),
            ]);
        }
        if (waitForInitialPage) {
            await this.waitForPageTarget(browser, timeout);
        }
        return browser;
    }
    /**
     * @internal
     */
    async closeBrowser(browserProcess, cdpConnection) {
        if (cdpConnection) {
            // Attempt to close the browser gracefully
            try {
                await cdpConnection.closeBrowser();
                await browserProcess.hasClosed();
            }
            catch (error) {
                (0, util_js_1.debugError)(error);
                await browserProcess.close();
            }
        }
        else {
            // Wait for a possible graceful shutdown.
            await (0, rxjs_js_1.firstValueFrom)((0, rxjs_js_1.race)((0, rxjs_js_1.from)(browserProcess.hasClosed()), (0, rxjs_js_1.timer)(5000).pipe((0, rxjs_js_1.map)(() => {
                return (0, rxjs_js_1.from)(browserProcess.close());
            }))));
        }
    }
    /**
     * @internal
     */
    async waitForPageTarget(browser, timeout) {
        try {
            await browser.waitForTarget(t => {
                return t.type() === 'page';
            }, { timeout });
        }
        catch (error) {
            await browser.close();
            throw error;
        }
    }
    /**
     * @internal
     */
    async createCdpSocketConnection(browserProcess, opts) {
        const browserWSEndpoint = await browserProcess.waitForLineOutput(browsers_1.CDP_WEBSOCKET_ENDPOINT_REGEX, opts.timeout);
        const transport = await NodeWebSocketTransport_js_1.NodeWebSocketTransport.create(browserWSEndpoint);
        return new Connection_js_1.Connection(browserWSEndpoint, transport, opts.slowMo, opts.protocolTimeout, 
        /* rawErrors */ false, opts.idGenerator);
    }
    /**
     * @internal
     */
    async createCdpPipeConnection(browserProcess, opts) {
        // stdio was assigned during start(), and the 'pipe' option there adds the
        // 4th and 5th items to stdio array
        const { 3: pipeWrite, 4: pipeRead } = browserProcess.nodeProcess.stdio;
        const transport = new PipeTransport_js_1.PipeTransport(pipeWrite, pipeRead);
        return new Connection_js_1.Connection('', transport, opts.slowMo, opts.protocolTimeout, 
        /* rawErrors */ false, opts.idGenerator);
    }
    /**
     * @internal
     */
    async createBiDiOverCdpBrowser(browserProcess, cdpConnection, closeCallback, opts) {
        const bidiOnly = process.env['PUPPETEER_WEBDRIVER_BIDI_ONLY'] === 'true';
        const BiDi = await Promise.resolve().then(() => __importStar(require(/* webpackIgnore: true */ '../bidi/bidi.js')));
        const bidiConnection = await BiDi.connectBidiOverCdp(cdpConnection);
        return await BiDi.BidiBrowser.create({
            connection: bidiConnection,
            // Do not provide CDP connection to Browser, if BiDi-only mode is enabled. This
            // would restrict Browser to use only BiDi endpoint.
            cdpConnection: bidiOnly ? undefined : cdpConnection,
            closeCallback,
            process: browserProcess.nodeProcess,
            defaultViewport: opts.defaultViewport,
            acceptInsecureCerts: opts.acceptInsecureCerts,
            networkEnabled: opts.networkEnabled,
        });
    }
    /**
     * @internal
     */
    async createBiDiBrowser(browserProcess, closeCallback, opts) {
        const browserWSEndpoint = (await browserProcess.waitForLineOutput(browsers_1.WEBDRIVER_BIDI_WEBSOCKET_ENDPOINT_REGEX, opts.timeout)) + '/session';
        const transport = await NodeWebSocketTransport_js_1.NodeWebSocketTransport.create(browserWSEndpoint);
        const BiDi = await Promise.resolve().then(() => __importStar(require(/* webpackIgnore: true */ '../bidi/bidi.js')));
        const bidiConnection = new BiDi.BidiConnection(browserWSEndpoint, transport, opts.idGenerator, opts.slowMo, opts.protocolTimeout);
        return await BiDi.BidiBrowser.create({
            connection: bidiConnection,
            closeCallback,
            process: browserProcess.nodeProcess,
            defaultViewport: opts.defaultViewport,
            acceptInsecureCerts: opts.acceptInsecureCerts,
            networkEnabled: opts.networkEnabled ?? true,
        });
    }
    /**
     * @internal
     */
    getProfilePath() {
        return (0, node_path_1.join)(this.puppeteer.configuration.temporaryDirectory ?? (0, node_os_1.tmpdir)(), `puppeteer_dev_${this.browser}_profile-`);
    }
    /**
     * @internal
     */
    resolveExecutablePath(headless, validatePath = true) {
        let executablePath = this.puppeteer.configuration.executablePath;
        if (executablePath) {
            if (validatePath && !(0, node_fs_1.existsSync)(executablePath)) {
                throw new Error(`Tried to find the browser at the configured path (${executablePath}), but no executable was found.`);
            }
            return executablePath;
        }
        function puppeteerBrowserToInstalledBrowser(browser, headless) {
            switch (browser) {
                case 'chrome':
                    if (headless === 'shell') {
                        return browsers_1.Browser.CHROMEHEADLESSSHELL;
                    }
                    return browsers_1.Browser.CHROME;
                case 'firefox':
                    return browsers_1.Browser.FIREFOX;
            }
            return browsers_1.Browser.CHROME;
        }
        const browserType = puppeteerBrowserToInstalledBrowser(this.browser, headless);
        executablePath = (0, browsers_1.computeExecutablePath)({
            cacheDir: this.puppeteer.defaultDownloadPath,
            browser: browserType,
            buildId: this.puppeteer.browserVersion,
        });
        if (validatePath && !(0, node_fs_1.existsSync)(executablePath)) {
            const configVersion = this.puppeteer.configuration?.[this.browser]?.version;
            if (configVersion) {
                throw new Error(`Tried to find the browser at the configured path (${executablePath}) for version ${configVersion}, but no executable was found.`);
            }
            switch (this.browser) {
                case 'chrome':
                    throw new Error(`Could not find Chrome (ver. ${this.puppeteer.browserVersion}). This can occur if either\n` +
                        ` 1. you did not perform an installation before running the script (e.g. \`npx puppeteer browsers install ${browserType}\`) or\n` +
                        ` 2. your cache path is incorrectly configured (which is: ${this.puppeteer.configuration.cacheDirectory}).\n` +
                        'For (2), check out our guide on configuring puppeteer at https://pptr.dev/guides/configuration.');
                case 'firefox':
                    throw new Error(`Could not find Firefox (rev. ${this.puppeteer.browserVersion}). This can occur if either\n` +
                        ' 1. you did not perform an installation for Firefox before running the script (e.g. `npx puppeteer browsers install firefox`) or\n' +
                        ` 2. your cache path is incorrectly configured (which is: ${this.puppeteer.configuration.cacheDirectory}).\n` +
                        'For (2), check out our guide on configuring puppeteer at https://pptr.dev/guides/configuration.');
            }
        }
        return executablePath;
    }
}
exports.BrowserLauncher = BrowserLauncher;
//# sourceMappingURL=BrowserLauncher.js.map