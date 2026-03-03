"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.Browser = exports.WEB_PERMISSION_TO_PROTOCOL_PERMISSION = void 0;
const rxjs_js_1 = require("../../third_party/rxjs/rxjs.js");
const EventEmitter_js_1 = require("../common/EventEmitter.js");
const util_js_1 = require("../common/util.js");
const disposable_js_1 = require("../util/disposable.js");
/**
 * @internal
 */
exports.WEB_PERMISSION_TO_PROTOCOL_PERMISSION = new Map([
    ['accelerometer', 'sensors'],
    ['ambient-light-sensor', 'sensors'],
    ['background-sync', 'backgroundSync'],
    ['camera', 'videoCapture'],
    ['clipboard-read', 'clipboardReadWrite'],
    ['clipboard-sanitized-write', 'clipboardSanitizedWrite'],
    ['clipboard-write', 'clipboardReadWrite'],
    ['geolocation', 'geolocation'],
    ['gyroscope', 'sensors'],
    ['idle-detection', 'idleDetection'],
    ['keyboard-lock', 'keyboardLock'],
    ['magnetometer', 'sensors'],
    ['microphone', 'audioCapture'],
    ['midi', 'midi'],
    ['notifications', 'notifications'],
    ['payment-handler', 'paymentHandler'],
    ['persistent-storage', 'durableStorage'],
    ['pointer-lock', 'pointerLock'],
    // chrome-specific permissions we have.
    ['midi-sysex', 'midiSysex'],
]);
/**
 * {@link Browser} represents a browser instance that is either:
 *
 * - connected to via {@link Puppeteer.connect} or
 * - launched by {@link PuppeteerNode.launch}.
 *
 * {@link Browser} {@link EventEmitter.emit | emits} various events which are
 * documented in the {@link BrowserEvent} enum.
 *
 * @example Using a {@link Browser} to create a {@link Page}:
 *
 * ```ts
 * import puppeteer from 'puppeteer';
 *
 * const browser = await puppeteer.launch();
 * const page = await browser.newPage();
 * await page.goto('https://example.com');
 * await browser.close();
 * ```
 *
 * @example Disconnecting from and reconnecting to a {@link Browser}:
 *
 * ```ts
 * import puppeteer from 'puppeteer';
 *
 * const browser = await puppeteer.launch();
 * // Store the endpoint to be able to reconnect to the browser.
 * const browserWSEndpoint = browser.wsEndpoint();
 * // Disconnect puppeteer from the browser.
 * await browser.disconnect();
 *
 * // Use the endpoint to reestablish a connection
 * const browser2 = await puppeteer.connect({browserWSEndpoint});
 * // Close the browser.
 * await browser2.close();
 * ```
 *
 * @public
 */
class Browser extends EventEmitter_js_1.EventEmitter {
    /**
     * @internal
     */
    constructor() {
        super();
    }
    /**
     * Waits until a {@link Target | target} matching the given `predicate`
     * appears and returns it.
     *
     * This will look all open {@link BrowserContext | browser contexts}.
     *
     * @example Finding a target for a page opened via `window.open`:
     *
     * ```ts
     * await page.evaluate(() => window.open('https://www.example.com/'));
     * const newWindowTarget = await browser.waitForTarget(
     *   target => target.url() === 'https://www.example.com/',
     * );
     * ```
     */
    async waitForTarget(predicate, options = {}) {
        const { timeout: ms = 30000, signal } = options;
        return await (0, rxjs_js_1.firstValueFrom)((0, rxjs_js_1.merge)((0, util_js_1.fromEmitterEvent)(this, "targetcreated" /* BrowserEvent.TargetCreated */), (0, util_js_1.fromEmitterEvent)(this, "targetchanged" /* BrowserEvent.TargetChanged */), (0, rxjs_js_1.from)(this.targets())).pipe((0, util_js_1.filterAsync)(predicate), (0, rxjs_js_1.raceWith)((0, util_js_1.fromAbortSignal)(signal), (0, util_js_1.timeout)(ms))));
    }
    /**
     * Gets a list of all open {@link Page | pages} inside this {@link Browser}.
     *
     * If there are multiple {@link BrowserContext | browser contexts}, this
     * returns all {@link Page | pages} in all
     * {@link BrowserContext | browser contexts}.
     *
     * @param includeAll - experimental, setting to true includes all kinds of pages.
     *
     * @remarks Non-visible {@link Page | pages}, such as `"background_page"`,
     * will not be listed here. You can find them using {@link Target.page}.
     */
    async pages(includeAll = false) {
        const contextPages = await Promise.all(this.browserContexts().map(context => {
            return context.pages(includeAll);
        }));
        // Flatten array.
        return contextPages.reduce((acc, x) => {
            return acc.concat(x);
        }, []);
    }
    /**
     * Returns all cookies in the default {@link BrowserContext}.
     *
     * @remarks
     *
     * Shortcut for
     * {@link BrowserContext.cookies | browser.defaultBrowserContext().cookies()}.
     */
    async cookies() {
        return await this.defaultBrowserContext().cookies();
    }
    /**
     * Sets cookies in the default {@link BrowserContext}.
     *
     * @remarks
     *
     * Shortcut for
     * {@link BrowserContext.setCookie | browser.defaultBrowserContext().setCookie()}.
     */
    async setCookie(...cookies) {
        return await this.defaultBrowserContext().setCookie(...cookies);
    }
    /**
     * Removes cookies from the default {@link BrowserContext}.
     *
     * @remarks
     *
     * Shortcut for
     * {@link BrowserContext.deleteCookie | browser.defaultBrowserContext().deleteCookie()}.
     */
    async deleteCookie(...cookies) {
        return await this.defaultBrowserContext().deleteCookie(...cookies);
    }
    /**
     * Deletes cookies matching the provided filters from the default
     * {@link BrowserContext}.
     *
     * @remarks
     *
     * Shortcut for
     * {@link BrowserContext.deleteMatchingCookies |
     * browser.defaultBrowserContext().deleteMatchingCookies()}.
     */
    async deleteMatchingCookies(...filters) {
        return await this.defaultBrowserContext().deleteMatchingCookies(...filters);
    }
    /**
     * Sets the permission for a specific origin in the default
     * {@link BrowserContext}.
     *
     * @remarks
     *
     * Shortcut for
     * {@link BrowserContext.setPermission |
     * browser.defaultBrowserContext().setPermission()}.
     *
     * @param origin - The origin to set the permission for.
     * @param permission - The permission descriptor.
     * @param state - The state of the permission.
     *
     * @public
     */
    async setPermission(origin, ...permissions) {
        return await this.defaultBrowserContext().setPermission(origin, ...permissions);
    }
    /**
     * Whether Puppeteer is connected to this {@link Browser | browser}.
     *
     * @deprecated Use {@link Browser | Browser.connected}.
     */
    isConnected() {
        return this.connected;
    }
    /** @internal */
    [disposable_js_1.disposeSymbol]() {
        if (this.process()) {
            return void this.close().catch(util_js_1.debugError);
        }
        return void this.disconnect().catch(util_js_1.debugError);
    }
    /** @internal */
    [disposable_js_1.asyncDisposeSymbol]() {
        if (this.process()) {
            return this.close();
        }
        return this.disconnect();
    }
}
exports.Browser = Browser;
//# sourceMappingURL=Browser.js.map