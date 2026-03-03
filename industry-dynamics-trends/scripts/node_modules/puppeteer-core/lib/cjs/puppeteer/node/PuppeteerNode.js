"use strict";
/**
 * @license
 * Copyright 2020 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
Object.defineProperty(exports, "__esModule", { value: true });
exports.PuppeteerNode = void 0;
const browsers_1 = require("@puppeteer/browsers");
const Puppeteer_js_1 = require("../common/Puppeteer.js");
const revisions_js_1 = require("../revisions.js");
const ChromeLauncher_js_1 = require("./ChromeLauncher.js");
const FirefoxLauncher_js_1 = require("./FirefoxLauncher.js");
/**
 * Extends the main {@link Puppeteer} class with Node specific behaviour for
 * fetching and downloading browsers.
 *
 * If you're using Puppeteer in a Node environment, this is the class you'll get
 * when you run `require('puppeteer')` (or the equivalent ES `import`).
 *
 * @remarks
 * The most common method to use is {@link PuppeteerNode.launch | launch}, which
 * is used to launch and connect to a new browser instance.
 *
 * See {@link Puppeteer | the main Puppeteer class} for methods common to all
 * environments, such as {@link Puppeteer.connect}.
 *
 * @example
 * The following is a typical example of using Puppeteer to drive automation:
 *
 * ```ts
 * import puppeteer from 'puppeteer';
 *
 * const browser = await puppeteer.launch();
 * const page = await browser.newPage();
 * await page.goto('https://www.google.com');
 * // other actions...
 * await browser.close();
 * ```
 *
 * Once you have created a `page` you have access to a large API to interact
 * with the page, navigate, or find certain elements in that page.
 * The {@link Page | `page` documentation} lists all the available methods.
 *
 * @public
 */
class PuppeteerNode extends Puppeteer_js_1.Puppeteer {
    #launcher;
    #lastLaunchedBrowser;
    /**
     * @internal
     */
    defaultBrowserRevision;
    /**
     * @internal
     */
    configuration = {};
    /**
     * @internal
     */
    constructor(settings) {
        const { configuration, ...commonSettings } = settings;
        super(commonSettings);
        if (configuration) {
            this.configuration = configuration;
        }
        switch (this.configuration.defaultBrowser) {
            case 'firefox':
                this.defaultBrowserRevision = revisions_js_1.PUPPETEER_REVISIONS.firefox;
                break;
            default:
                this.configuration.defaultBrowser = 'chrome';
                this.defaultBrowserRevision = revisions_js_1.PUPPETEER_REVISIONS.chrome;
                break;
        }
        this.connect = this.connect.bind(this);
        this.launch = this.launch.bind(this);
        this.executablePath = this.executablePath.bind(this);
        this.defaultArgs = this.defaultArgs.bind(this);
        this.trimCache = this.trimCache.bind(this);
    }
    /**
     * This method attaches Puppeteer to an existing browser instance.
     *
     * @param options - Set of configurable options to set on the browser.
     * @returns Promise which resolves to browser instance.
     */
    connect(options) {
        return super.connect(options);
    }
    /**
     * Launches a browser instance with given arguments and options when
     * specified.
     *
     * When using with `puppeteer-core`,
     * {@link LaunchOptions.executablePath | options.executablePath} or
     * {@link LaunchOptions.channel | options.channel} must be provided.
     *
     * @example
     * You can use {@link LaunchOptions.ignoreDefaultArgs | options.ignoreDefaultArgs}
     * to filter out `--mute-audio` from default arguments:
     *
     * ```ts
     * const browser = await puppeteer.launch({
     *   ignoreDefaultArgs: ['--mute-audio'],
     * });
     * ```
     *
     * @remarks
     * Puppeteer can also be used to control the Chrome browser, but it works best
     * with the version of Chrome for Testing downloaded by default.
     * There is no guarantee it will work with any other version. If Google Chrome
     * (rather than Chrome for Testing) is preferred, a
     * {@link https://www.google.com/chrome/browser/canary.html | Chrome Canary}
     * or
     * {@link https://www.chromium.org/getting-involved/dev-channel | Dev Channel}
     * build is suggested. See
     * {@link https://www.howtogeek.com/202825/what%E2%80%99s-the-difference-between-chromium-and-chrome/ | this article}
     * for a description of the differences between Chromium and Chrome.
     * {@link https://chromium.googlesource.com/chromium/src/+/lkgr/docs/chromium_browser_vs_google_chrome.md | This article}
     * describes some differences for Linux users. See
     * {@link https://developer.chrome.com/blog/chrome-for-testing/ | this doc} for the description
     * of Chrome for Testing.
     *
     * @param options - Options to configure launching behavior.
     */
    launch(options = {}) {
        const { browser = this.defaultBrowser } = options;
        this.#lastLaunchedBrowser = browser;
        switch (browser) {
            case 'chrome':
                this.defaultBrowserRevision = revisions_js_1.PUPPETEER_REVISIONS.chrome;
                break;
            case 'firefox':
                this.defaultBrowserRevision = revisions_js_1.PUPPETEER_REVISIONS.firefox;
                break;
            default:
                throw new Error(`Unknown product: ${browser}`);
        }
        this.#launcher = this.#getLauncher(browser);
        return this.#launcher.launch(options);
    }
    /**
     * @internal
     */
    #getLauncher(browser) {
        if (this.#launcher && this.#launcher.browser === browser) {
            return this.#launcher;
        }
        switch (browser) {
            case 'chrome':
                return new ChromeLauncher_js_1.ChromeLauncher(this);
            case 'firefox':
                return new FirefoxLauncher_js_1.FirefoxLauncher(this);
            default:
                throw new Error(`Unknown product: ${browser}`);
        }
    }
    executablePath(optsOrChannel) {
        if (optsOrChannel === undefined) {
            return this.#getLauncher(this.lastLaunchedBrowser).executablePath(undefined, 
            /* validatePath= */ false);
        }
        if (typeof optsOrChannel === 'string') {
            return this.#getLauncher('chrome').executablePath(optsOrChannel, 
            /* validatePath= */ false);
        }
        return this.#getLauncher(optsOrChannel.browser ?? this.lastLaunchedBrowser).resolveExecutablePath(optsOrChannel.headless, /* validatePath= */ false);
    }
    /**
     * @internal
     */
    get browserVersion() {
        return (this.configuration?.[this.lastLaunchedBrowser]?.version ??
            this.defaultBrowserRevision);
    }
    /**
     * The default download path for puppeteer. For puppeteer-core, this
     * code should never be called as it is never defined.
     *
     * @internal
     */
    get defaultDownloadPath() {
        return this.configuration.cacheDirectory;
    }
    /**
     * The name of the browser that was last launched.
     */
    get lastLaunchedBrowser() {
        return this.#lastLaunchedBrowser ?? this.defaultBrowser;
    }
    /**
     * The name of the browser that will be launched by default. For
     * `puppeteer`, this is influenced by your configuration. Otherwise, it's
     * `chrome`.
     */
    get defaultBrowser() {
        return this.configuration.defaultBrowser ?? 'chrome';
    }
    /**
     * @deprecated Do not use as this field as it does not take into account
     * multiple browsers of different types. Use
     * {@link PuppeteerNode.defaultBrowser | defaultBrowser} or
     * {@link PuppeteerNode.lastLaunchedBrowser | lastLaunchedBrowser}.
     *
     * @returns The name of the browser that is under automation.
     */
    get product() {
        return this.lastLaunchedBrowser;
    }
    /**
     * @param options - Set of configurable options to set on the browser.
     *
     * @returns The default arguments that the browser will be launched with.
     */
    defaultArgs(options = {}) {
        return this.#getLauncher(options.browser ?? this.lastLaunchedBrowser).defaultArgs(options);
    }
    /**
     * Removes all non-current Firefox and Chrome binaries in the cache directory
     * identified by the provided Puppeteer configuration. The current browser
     * version is determined by resolving PUPPETEER_REVISIONS from Puppeteer
     * unless `configuration.browserRevision` is provided.
     *
     * @remarks
     *
     * Note that the method does not check if any other Puppeteer versions
     * installed on the host that use the same cache directory require the
     * non-current binaries.
     *
     * @public
     */
    async trimCache() {
        const platform = (0, browsers_1.detectBrowserPlatform)();
        if (!platform) {
            throw new Error('The current platform is not supported.');
        }
        const cacheDir = this.configuration.cacheDirectory;
        const installedBrowsers = await (0, browsers_1.getInstalledBrowsers)({
            cacheDir,
        });
        const puppeteerBrowsers = [
            {
                product: 'chrome',
                browser: browsers_1.Browser.CHROME,
                currentBuildId: '',
            },
            {
                product: 'firefox',
                browser: browsers_1.Browser.FIREFOX,
                currentBuildId: '',
            },
        ];
        // Resolve current buildIds.
        await Promise.all(puppeteerBrowsers.map(async (item) => {
            const tag = this.configuration?.[item.product]?.version ??
                revisions_js_1.PUPPETEER_REVISIONS[item.product];
            item.currentBuildId = await (0, browsers_1.resolveBuildId)(item.browser, platform, tag);
        }));
        const currentBrowserBuilds = new Set(puppeteerBrowsers.map(browser => {
            return `${browser.browser}_${browser.currentBuildId}`;
        }));
        const currentBrowsers = new Set(puppeteerBrowsers.map(browser => {
            return browser.browser;
        }));
        for (const installedBrowser of installedBrowsers) {
            // Don't uninstall browsers that are not managed by Puppeteer yet.
            if (!currentBrowsers.has(installedBrowser.browser)) {
                continue;
            }
            // Keep the browser build used by the current Puppeteer installation.
            if (currentBrowserBuilds.has(`${installedBrowser.browser}_${installedBrowser.buildId}`)) {
                continue;
            }
            await (0, browsers_1.uninstall)({
                browser: installedBrowser.browser,
                platform,
                cacheDir,
                buildId: installedBrowser.buildId,
            });
        }
    }
}
exports.PuppeteerNode = PuppeteerNode;
//# sourceMappingURL=PuppeteerNode.js.map