"use strict";
/**
 * @license
 * Copyright 2019 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
Object.defineProperty(exports, "__esModule", { value: true });
exports.OtherTarget = exports.WorkerTarget = exports.DevToolsTarget = exports.PageTarget = exports.CdpTarget = exports.InitializationStatus = void 0;
const Target_js_1 = require("../api/Target.js");
const util_js_1 = require("../common/util.js");
const Deferred_js_1 = require("../util/Deferred.js");
const Page_js_1 = require("./Page.js");
const WebWorker_js_1 = require("./WebWorker.js");
/**
 * @internal
 */
var InitializationStatus;
(function (InitializationStatus) {
    InitializationStatus["SUCCESS"] = "success";
    InitializationStatus["ABORTED"] = "aborted";
})(InitializationStatus || (exports.InitializationStatus = InitializationStatus = {}));
/**
 * @internal
 */
class CdpTarget extends Target_js_1.Target {
    #browserContext;
    #session;
    #targetInfo;
    #targetManager;
    #sessionFactory;
    #childTargets = new Set();
    _initializedDeferred = Deferred_js_1.Deferred.create();
    _isClosedDeferred = Deferred_js_1.Deferred.create();
    _targetId;
    /**
     * To initialize the target for use, call initialize.
     *
     * @internal
     */
    constructor(targetInfo, session, browserContext, targetManager, sessionFactory) {
        super();
        this.#session = session;
        this.#targetManager = targetManager;
        this.#targetInfo = targetInfo;
        this.#browserContext = browserContext;
        this._targetId = targetInfo.targetId;
        this.#sessionFactory = sessionFactory;
        if (this.#session) {
            this.#session.setTarget(this);
        }
    }
    async asPage() {
        const session = this._session();
        if (!session) {
            return await this.createCDPSession().then(client => {
                return Page_js_1.CdpPage._create(client, this, null);
            });
        }
        return await Page_js_1.CdpPage._create(session, this, null);
    }
    _subtype() {
        return this.#targetInfo.subtype;
    }
    _session() {
        return this.#session;
    }
    _addChildTarget(target) {
        this.#childTargets.add(target);
    }
    _removeChildTarget(target) {
        this.#childTargets.delete(target);
    }
    _childTargets() {
        return this.#childTargets;
    }
    _sessionFactory() {
        if (!this.#sessionFactory) {
            throw new Error('sessionFactory is not initialized');
        }
        return this.#sessionFactory;
    }
    createCDPSession() {
        if (!this.#sessionFactory) {
            throw new Error('sessionFactory is not initialized');
        }
        return this.#sessionFactory(false).then(session => {
            session.setTarget(this);
            return session;
        });
    }
    url() {
        return this.#targetInfo.url;
    }
    type() {
        const type = this.#targetInfo.type;
        switch (type) {
            case 'page':
                return Target_js_1.TargetType.PAGE;
            case 'background_page':
                return Target_js_1.TargetType.BACKGROUND_PAGE;
            case 'service_worker':
                return Target_js_1.TargetType.SERVICE_WORKER;
            case 'shared_worker':
                return Target_js_1.TargetType.SHARED_WORKER;
            case 'browser':
                return Target_js_1.TargetType.BROWSER;
            case 'webview':
                return Target_js_1.TargetType.WEBVIEW;
            case 'tab':
                return Target_js_1.TargetType.TAB;
            default:
                return Target_js_1.TargetType.OTHER;
        }
    }
    _targetManager() {
        if (!this.#targetManager) {
            throw new Error('targetManager is not initialized');
        }
        return this.#targetManager;
    }
    _getTargetInfo() {
        return this.#targetInfo;
    }
    browser() {
        if (!this.#browserContext) {
            throw new Error('browserContext is not initialized');
        }
        return this.#browserContext.browser();
    }
    browserContext() {
        if (!this.#browserContext) {
            throw new Error('browserContext is not initialized');
        }
        return this.#browserContext;
    }
    opener() {
        const { openerId } = this.#targetInfo;
        if (!openerId) {
            return;
        }
        return this.browser()
            .targets()
            .find(target => {
            return target._targetId === openerId;
        });
    }
    _targetInfoChanged(targetInfo) {
        this.#targetInfo = targetInfo;
        this._checkIfInitialized();
    }
    _initialize() {
        this._initializedDeferred.resolve(InitializationStatus.SUCCESS);
    }
    _isTargetExposed() {
        return this.type() !== Target_js_1.TargetType.TAB && !this._subtype();
    }
    _checkIfInitialized() {
        if (!this._initializedDeferred.resolved()) {
            this._initializedDeferred.resolve(InitializationStatus.SUCCESS);
        }
    }
}
exports.CdpTarget = CdpTarget;
/**
 * @internal
 */
class PageTarget extends CdpTarget {
    #defaultViewport;
    pagePromise;
    constructor(targetInfo, session, browserContext, targetManager, sessionFactory, defaultViewport) {
        super(targetInfo, session, browserContext, targetManager, sessionFactory);
        this.#defaultViewport = defaultViewport ?? undefined;
    }
    _initialize() {
        this._initializedDeferred
            .valueOrThrow()
            .then(async (result) => {
            if (result === InitializationStatus.ABORTED) {
                return;
            }
            const opener = this.opener();
            if (!(opener instanceof PageTarget)) {
                return;
            }
            if (!opener || !opener.pagePromise || this.type() !== 'page') {
                return true;
            }
            const openerPage = await opener.pagePromise;
            if (!openerPage.listenerCount("popup" /* PageEvent.Popup */)) {
                return true;
            }
            const popupPage = await this.page();
            openerPage.emit("popup" /* PageEvent.Popup */, popupPage);
            return true;
        })
            .catch(util_js_1.debugError);
        this._checkIfInitialized();
    }
    async page() {
        if (!this.pagePromise) {
            const session = this._session();
            this.pagePromise = (session
                ? Promise.resolve(session)
                : this._sessionFactory()(/* isAutoAttachEmulated=*/ false)).then(client => {
                return Page_js_1.CdpPage._create(client, this, this.#defaultViewport ?? null);
            });
        }
        return (await this.pagePromise) ?? null;
    }
    _checkIfInitialized() {
        if (this._initializedDeferred.resolved()) {
            return;
        }
        if (this._getTargetInfo().url !== '') {
            this._initializedDeferred.resolve(InitializationStatus.SUCCESS);
        }
    }
}
exports.PageTarget = PageTarget;
/**
 * @internal
 */
class DevToolsTarget extends PageTarget {
}
exports.DevToolsTarget = DevToolsTarget;
/**
 * @internal
 */
class WorkerTarget extends CdpTarget {
    #workerPromise;
    async worker() {
        if (!this.#workerPromise) {
            const session = this._session();
            // TODO(einbinder): Make workers send their console logs.
            this.#workerPromise = (session
                ? Promise.resolve(session)
                : this._sessionFactory()(/* isAutoAttachEmulated=*/ false)).then(client => {
                return new WebWorker_js_1.CdpWebWorker(client, this._getTargetInfo().url, this._targetId, this.type(), () => { } /* consoleAPICalled */, () => { } /* exceptionThrown */, undefined /* networkManager */);
            });
        }
        return await this.#workerPromise;
    }
}
exports.WorkerTarget = WorkerTarget;
/**
 * @internal
 */
class OtherTarget extends CdpTarget {
}
exports.OtherTarget = OtherTarget;
//# sourceMappingURL=Target.js.map