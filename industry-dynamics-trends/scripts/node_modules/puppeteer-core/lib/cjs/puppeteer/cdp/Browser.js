"use strict";
/**
 * @license
 * Copyright 2017 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
Object.defineProperty(exports, "__esModule", { value: true });
exports.CdpBrowser = void 0;
const Browser_js_1 = require("../api/Browser.js");
const CDPSession_js_1 = require("../api/CDPSession.js");
const BrowserContext_js_1 = require("./BrowserContext.js");
const Target_js_1 = require("./Target.js");
const TargetManager_js_1 = require("./TargetManager.js");
/**
 * @internal
 */
function isDevToolsPageTarget(url) {
    return url.startsWith('devtools://devtools/bundled/devtools_app.html');
}
/**
 * @internal
 */
class CdpBrowser extends Browser_js_1.Browser {
    protocol = 'cdp';
    static async _create(connection, contextIds, acceptInsecureCerts, defaultViewport, downloadBehavior, process, closeCallback, targetFilterCallback, isPageTargetCallback, waitForInitiallyDiscoveredTargets = true, networkEnabled = true, handleDevToolsAsPage = false) {
        const browser = new CdpBrowser(connection, contextIds, defaultViewport, process, closeCallback, targetFilterCallback, isPageTargetCallback, waitForInitiallyDiscoveredTargets, networkEnabled, handleDevToolsAsPage);
        if (acceptInsecureCerts) {
            await connection.send('Security.setIgnoreCertificateErrors', {
                ignore: true,
            });
        }
        await browser._attach(downloadBehavior);
        return browser;
    }
    #defaultViewport;
    #process;
    #connection;
    #closeCallback;
    #targetFilterCallback;
    #isPageTargetCallback;
    #defaultContext;
    #contexts = new Map();
    #networkEnabled = true;
    #targetManager;
    #handleDevToolsAsPage = false;
    constructor(connection, contextIds, defaultViewport, process, closeCallback, targetFilterCallback, isPageTargetCallback, waitForInitiallyDiscoveredTargets = true, networkEnabled = true, handleDevToolsAsPage = false) {
        super();
        this.#networkEnabled = networkEnabled;
        this.#defaultViewport = defaultViewport;
        this.#process = process;
        this.#connection = connection;
        this.#closeCallback = closeCallback || (() => { });
        this.#targetFilterCallback =
            targetFilterCallback ||
                (() => {
                    return true;
                });
        this.#handleDevToolsAsPage = handleDevToolsAsPage;
        this.#setIsPageTargetCallback(isPageTargetCallback);
        this.#targetManager = new TargetManager_js_1.TargetManager(connection, this.#createTarget, this.#targetFilterCallback, waitForInitiallyDiscoveredTargets);
        this.#defaultContext = new BrowserContext_js_1.CdpBrowserContext(this.#connection, this);
        for (const contextId of contextIds) {
            this.#contexts.set(contextId, new BrowserContext_js_1.CdpBrowserContext(this.#connection, this, contextId));
        }
    }
    #emitDisconnected = () => {
        this.emit("disconnected" /* BrowserEvent.Disconnected */, undefined);
    };
    async _attach(downloadBehavior) {
        this.#connection.on(CDPSession_js_1.CDPSessionEvent.Disconnected, this.#emitDisconnected);
        if (downloadBehavior) {
            await this.#defaultContext.setDownloadBehavior(downloadBehavior);
        }
        this.#targetManager.on("targetAvailable" /* TargetManagerEvent.TargetAvailable */, this.#onAttachedToTarget);
        this.#targetManager.on("targetGone" /* TargetManagerEvent.TargetGone */, this.#onDetachedFromTarget);
        this.#targetManager.on("targetChanged" /* TargetManagerEvent.TargetChanged */, this.#onTargetChanged);
        this.#targetManager.on("targetDiscovered" /* TargetManagerEvent.TargetDiscovered */, this.#onTargetDiscovered);
        await this.#targetManager.initialize();
    }
    _detach() {
        this.#connection.off(CDPSession_js_1.CDPSessionEvent.Disconnected, this.#emitDisconnected);
        this.#targetManager.off("targetAvailable" /* TargetManagerEvent.TargetAvailable */, this.#onAttachedToTarget);
        this.#targetManager.off("targetGone" /* TargetManagerEvent.TargetGone */, this.#onDetachedFromTarget);
        this.#targetManager.off("targetChanged" /* TargetManagerEvent.TargetChanged */, this.#onTargetChanged);
        this.#targetManager.off("targetDiscovered" /* TargetManagerEvent.TargetDiscovered */, this.#onTargetDiscovered);
    }
    process() {
        return this.#process ?? null;
    }
    _targetManager() {
        return this.#targetManager;
    }
    #setIsPageTargetCallback(isPageTargetCallback) {
        this.#isPageTargetCallback =
            isPageTargetCallback ||
                ((target) => {
                    return (target.type() === 'page' ||
                        target.type() === 'background_page' ||
                        target.type() === 'webview' ||
                        (this.#handleDevToolsAsPage &&
                            target.type() === 'other' &&
                            isDevToolsPageTarget(target.url())));
                });
    }
    _getIsPageTargetCallback() {
        return this.#isPageTargetCallback;
    }
    async createBrowserContext(options = {}) {
        const { proxyServer, proxyBypassList, downloadBehavior } = options;
        const { browserContextId } = await this.#connection.send('Target.createBrowserContext', {
            proxyServer,
            proxyBypassList: proxyBypassList && proxyBypassList.join(','),
        });
        const context = new BrowserContext_js_1.CdpBrowserContext(this.#connection, this, browserContextId);
        if (downloadBehavior) {
            await context.setDownloadBehavior(downloadBehavior);
        }
        this.#contexts.set(browserContextId, context);
        return context;
    }
    browserContexts() {
        return [this.#defaultContext, ...Array.from(this.#contexts.values())];
    }
    defaultBrowserContext() {
        return this.#defaultContext;
    }
    async _disposeContext(contextId) {
        if (!contextId) {
            return;
        }
        await this.#connection.send('Target.disposeBrowserContext', {
            browserContextId: contextId,
        });
        this.#contexts.delete(contextId);
    }
    #createTarget = (targetInfo, session) => {
        const { browserContextId } = targetInfo;
        const context = browserContextId && this.#contexts.has(browserContextId)
            ? this.#contexts.get(browserContextId)
            : this.#defaultContext;
        if (!context) {
            throw new Error('Missing browser context');
        }
        const createSession = (isAutoAttachEmulated) => {
            return this.#connection._createSession(targetInfo, isAutoAttachEmulated);
        };
        const otherTarget = new Target_js_1.OtherTarget(targetInfo, session, context, this.#targetManager, createSession);
        if (targetInfo.url && isDevToolsPageTarget(targetInfo.url)) {
            return new Target_js_1.DevToolsTarget(targetInfo, session, context, this.#targetManager, createSession, this.#defaultViewport ?? null);
        }
        if (this.#isPageTargetCallback(otherTarget)) {
            return new Target_js_1.PageTarget(targetInfo, session, context, this.#targetManager, createSession, this.#defaultViewport ?? null);
        }
        if (targetInfo.type === 'service_worker' ||
            targetInfo.type === 'shared_worker') {
            return new Target_js_1.WorkerTarget(targetInfo, session, context, this.#targetManager, createSession);
        }
        return otherTarget;
    };
    #onAttachedToTarget = async (target) => {
        if (target._isTargetExposed() &&
            (await target._initializedDeferred.valueOrThrow()) ===
                Target_js_1.InitializationStatus.SUCCESS) {
            this.emit("targetcreated" /* BrowserEvent.TargetCreated */, target);
            target.browserContext().emit("targetcreated" /* BrowserContextEvent.TargetCreated */, target);
        }
    };
    #onDetachedFromTarget = async (target) => {
        target._initializedDeferred.resolve(Target_js_1.InitializationStatus.ABORTED);
        target._isClosedDeferred.resolve();
        if (target._isTargetExposed() &&
            (await target._initializedDeferred.valueOrThrow()) ===
                Target_js_1.InitializationStatus.SUCCESS) {
            this.emit("targetdestroyed" /* BrowserEvent.TargetDestroyed */, target);
            target.browserContext().emit("targetdestroyed" /* BrowserContextEvent.TargetDestroyed */, target);
        }
    };
    #onTargetChanged = ({ target }) => {
        this.emit("targetchanged" /* BrowserEvent.TargetChanged */, target);
        target.browserContext().emit("targetchanged" /* BrowserContextEvent.TargetChanged */, target);
    };
    #onTargetDiscovered = (targetInfo) => {
        this.emit("targetdiscovered" /* BrowserEvent.TargetDiscovered */, targetInfo);
    };
    wsEndpoint() {
        return this.#connection.url();
    }
    async newPage(options) {
        return await this.#defaultContext.newPage(options);
    }
    async _createPageInContext(contextId, options) {
        const hasTargets = this.targets().filter(t => {
            return t.browserContext().id === contextId;
        }).length > 0;
        const windowBounds = options?.type === 'window' ? options.windowBounds : undefined;
        const { targetId } = await this.#connection.send('Target.createTarget', {
            url: 'about:blank',
            browserContextId: contextId || undefined,
            left: windowBounds?.left,
            top: windowBounds?.top,
            width: windowBounds?.width,
            height: windowBounds?.height,
            windowState: windowBounds?.windowState,
            // Works around crbug.com/454825274.
            newWindow: hasTargets && options?.type === 'window' ? true : undefined,
            background: options?.background,
        });
        const target = (await this.waitForTarget(t => {
            return t._targetId === targetId;
        }));
        if (!target) {
            throw new Error(`Missing target for page (id = ${targetId})`);
        }
        const initialized = (await target._initializedDeferred.valueOrThrow()) ===
            Target_js_1.InitializationStatus.SUCCESS;
        if (!initialized) {
            throw new Error(`Failed to create target for page (id = ${targetId})`);
        }
        const page = await target.page();
        if (!page) {
            throw new Error(`Failed to create a page for context (id = ${contextId})`);
        }
        return page;
    }
    async _createDevToolsPage(pageTargetId) {
        const openDevToolsResponse = await this.#connection.send('Target.openDevTools', {
            targetId: pageTargetId,
        });
        const target = (await this.waitForTarget(t => {
            return t._targetId === openDevToolsResponse.targetId;
        }));
        if (!target) {
            throw new Error(`Missing target for DevTools page (id = ${pageTargetId})`);
        }
        const initialized = (await target._initializedDeferred.valueOrThrow()) ===
            Target_js_1.InitializationStatus.SUCCESS;
        if (!initialized) {
            throw new Error(`Failed to create target for DevTools page (id = ${pageTargetId})`);
        }
        const page = await target.page();
        if (!page) {
            throw new Error(`Failed to create a DevTools Page for target (id = ${pageTargetId})`);
        }
        return page;
    }
    async installExtension(path) {
        const { id } = await this.#connection.send('Extensions.loadUnpacked', { path });
        return id;
    }
    uninstallExtension(id) {
        return this.#connection.send('Extensions.uninstall', { id });
    }
    async screens() {
        const { screenInfos } = await this.#connection.send('Emulation.getScreenInfos');
        return screenInfos;
    }
    async addScreen(params) {
        const { screenInfo } = await this.#connection.send('Emulation.addScreen', params);
        return screenInfo;
    }
    async removeScreen(screenId) {
        return await this.#connection.send('Emulation.removeScreen', { screenId });
    }
    async getWindowBounds(windowId) {
        const { bounds } = await this.#connection.send('Browser.getWindowBounds', {
            windowId: Number(windowId),
        });
        return bounds;
    }
    async setWindowBounds(windowId, windowBounds) {
        await this.#connection.send('Browser.setWindowBounds', {
            windowId: Number(windowId),
            bounds: windowBounds,
        });
    }
    targets() {
        return Array.from(this.#targetManager.getAvailableTargets().values()).filter(target => {
            return (target._isTargetExposed() &&
                target._initializedDeferred.value() === Target_js_1.InitializationStatus.SUCCESS);
        });
    }
    target() {
        const browserTarget = this.targets().find(target => {
            return target.type() === 'browser';
        });
        if (!browserTarget) {
            throw new Error('Browser target is not found');
        }
        return browserTarget;
    }
    async version() {
        const version = await this.#getVersion();
        return version.product;
    }
    async userAgent() {
        const version = await this.#getVersion();
        return version.userAgent;
    }
    async close() {
        await this.#closeCallback.call(null);
        await this.disconnect();
    }
    disconnect() {
        this.#targetManager.dispose();
        this.#connection.dispose();
        this._detach();
        return Promise.resolve();
    }
    get connected() {
        return !this.#connection._closed;
    }
    #getVersion() {
        return this.#connection.send('Browser.getVersion');
    }
    get debugInfo() {
        return {
            pendingProtocolErrors: this.#connection.getPendingProtocolErrors(),
        };
    }
    isNetworkEnabled() {
        return this.#networkEnabled;
    }
}
exports.CdpBrowser = CdpBrowser;
//# sourceMappingURL=Browser.js.map