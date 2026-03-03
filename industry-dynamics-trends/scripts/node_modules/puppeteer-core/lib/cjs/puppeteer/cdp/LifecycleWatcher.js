"use strict";
/**
 * @license
 * Copyright 2019 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
Object.defineProperty(exports, "__esModule", { value: true });
exports.LifecycleWatcher = void 0;
const Frame_js_1 = require("../api/Frame.js");
const EventEmitter_js_1 = require("../common/EventEmitter.js");
const NetworkManagerEvents_js_1 = require("../common/NetworkManagerEvents.js");
const assert_js_1 = require("../util/assert.js");
const Deferred_js_1 = require("../util/Deferred.js");
const disposable_js_1 = require("../util/disposable.js");
const FrameManagerEvents_js_1 = require("./FrameManagerEvents.js");
const puppeteerToProtocolLifecycle = new Map([
    ['load', 'load'],
    ['domcontentloaded', 'DOMContentLoaded'],
    ['networkidle0', 'networkIdle'],
    ['networkidle2', 'networkAlmostIdle'],
]);
/**
 * @internal
 */
class LifecycleWatcher {
    #expectedLifecycle;
    #frame;
    #timeout;
    #navigationRequest = null;
    #subscriptions = new disposable_js_1.DisposableStack();
    #initialLoaderId;
    #terminationDeferred;
    #sameDocumentNavigationDeferred = Deferred_js_1.Deferred.create();
    #lifecycleDeferred = Deferred_js_1.Deferred.create();
    #newDocumentNavigationDeferred = Deferred_js_1.Deferred.create();
    #error = new Error('LifecycleWatcher terminated');
    #hasSameDocumentNavigation;
    #swapped;
    #navigationResponseReceived;
    constructor(networkManager, frame, waitUntil, timeout, signal) {
        if (Array.isArray(waitUntil)) {
            waitUntil = waitUntil.slice();
        }
        else if (typeof waitUntil === 'string') {
            waitUntil = [waitUntil];
        }
        this.#initialLoaderId = frame._loaderId;
        this.#expectedLifecycle = waitUntil.map(value => {
            const protocolEvent = puppeteerToProtocolLifecycle.get(value);
            (0, assert_js_1.assert)(protocolEvent, 'Unknown value for options.waitUntil: ' + value);
            return protocolEvent;
        });
        signal?.addEventListener('abort', () => {
            if (signal.reason instanceof Error) {
                signal.reason.cause = this.#error;
            }
            this.#terminationDeferred.reject(signal.reason);
        });
        this.#frame = frame;
        this.#timeout = timeout;
        const frameManagerEmitter = this.#subscriptions.use(new EventEmitter_js_1.EventEmitter(frame._frameManager));
        frameManagerEmitter.on(FrameManagerEvents_js_1.FrameManagerEvent.LifecycleEvent, this.#checkLifecycleComplete.bind(this));
        const frameEmitter = this.#subscriptions.use(new EventEmitter_js_1.EventEmitter(frame));
        frameEmitter.on(Frame_js_1.FrameEvent.FrameNavigatedWithinDocument, this.#navigatedWithinDocument.bind(this));
        frameEmitter.on(Frame_js_1.FrameEvent.FrameNavigated, this.#navigated.bind(this));
        frameEmitter.on(Frame_js_1.FrameEvent.FrameSwapped, this.#frameSwapped.bind(this));
        frameEmitter.on(Frame_js_1.FrameEvent.FrameSwappedByActivation, this.#frameSwapped.bind(this));
        frameEmitter.on(Frame_js_1.FrameEvent.FrameDetached, this.#onFrameDetached.bind(this));
        const networkManagerEmitter = this.#subscriptions.use(new EventEmitter_js_1.EventEmitter(networkManager));
        networkManagerEmitter.on(NetworkManagerEvents_js_1.NetworkManagerEvent.Request, this.#onRequest.bind(this));
        networkManagerEmitter.on(NetworkManagerEvents_js_1.NetworkManagerEvent.Response, this.#onResponse.bind(this));
        networkManagerEmitter.on(NetworkManagerEvents_js_1.NetworkManagerEvent.RequestFailed, this.#onRequestFailed.bind(this));
        this.#terminationDeferred = Deferred_js_1.Deferred.create({
            timeout: this.#timeout,
            message: `Navigation timeout of ${this.#timeout} ms exceeded`,
        });
        this.#checkLifecycleComplete();
    }
    #onRequest(request) {
        if (request.frame() !== this.#frame || !request.isNavigationRequest()) {
            return;
        }
        this.#navigationRequest = request;
        // Resolve previous navigation response in case there are multiple
        // navigation requests reported by the backend. This generally should not
        // happen by it looks like it's possible.
        this.#navigationResponseReceived?.resolve();
        this.#navigationResponseReceived = Deferred_js_1.Deferred.create();
        if (request.response() !== null) {
            this.#navigationResponseReceived?.resolve();
        }
    }
    #onRequestFailed(request) {
        if (this.#navigationRequest?.id !== request.id) {
            return;
        }
        this.#navigationResponseReceived?.resolve();
    }
    #onResponse(response) {
        if (this.#navigationRequest?.id !== response.request().id) {
            return;
        }
        this.#navigationResponseReceived?.resolve();
    }
    #onFrameDetached(frame) {
        if (this.#frame === frame) {
            this.#error.message = 'Navigating frame was detached';
            this.#terminationDeferred.resolve(this.#error);
            return;
        }
        this.#checkLifecycleComplete();
    }
    async navigationResponse() {
        // Continue with a possibly null response.
        await this.#navigationResponseReceived?.valueOrThrow();
        return this.#navigationRequest ? this.#navigationRequest.response() : null;
    }
    sameDocumentNavigationPromise() {
        return this.#sameDocumentNavigationDeferred.valueOrThrow();
    }
    newDocumentNavigationPromise() {
        return this.#newDocumentNavigationDeferred.valueOrThrow();
    }
    lifecyclePromise() {
        return this.#lifecycleDeferred.valueOrThrow();
    }
    terminationPromise() {
        return this.#terminationDeferred.valueOrThrow();
    }
    #navigatedWithinDocument() {
        this.#hasSameDocumentNavigation = true;
        this.#checkLifecycleComplete();
    }
    #navigated(navigationType) {
        if (navigationType === 'BackForwardCacheRestore') {
            return this.#frameSwapped();
        }
        this.#checkLifecycleComplete();
    }
    #frameSwapped() {
        this.#swapped = true;
        this.#checkLifecycleComplete();
    }
    #checkLifecycleComplete() {
        // We expect navigation to commit.
        if (!checkLifecycle(this.#frame, this.#expectedLifecycle)) {
            return;
        }
        this.#lifecycleDeferred.resolve();
        if (this.#hasSameDocumentNavigation) {
            this.#sameDocumentNavigationDeferred.resolve(undefined);
        }
        if (this.#swapped || this.#frame._loaderId !== this.#initialLoaderId) {
            this.#newDocumentNavigationDeferred.resolve(undefined);
        }
        function checkLifecycle(frame, expectedLifecycle) {
            for (const event of expectedLifecycle) {
                if (!frame._lifecycleEvents.has(event)) {
                    return false;
                }
            }
            for (const child of frame.childFrames()) {
                if (child._hasStartedLoading &&
                    !checkLifecycle(child, expectedLifecycle)) {
                    return false;
                }
            }
            return true;
        }
    }
    dispose() {
        this.#subscriptions.dispose();
        this.#error.cause = new Error('LifecycleWatcher disposed');
        this.#terminationDeferred.resolve(this.#error);
    }
}
exports.LifecycleWatcher = LifecycleWatcher;
//# sourceMappingURL=LifecycleWatcher.js.map