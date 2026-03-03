"use strict";
/**
 * @license
 * Copyright 2019 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
Object.defineProperty(exports, "__esModule", { value: true });
exports.IsolatedWorld = void 0;
const rxjs_js_1 = require("../../third_party/rxjs/rxjs.js");
const Realm_js_1 = require("../api/Realm.js");
const EventEmitter_js_1 = require("../common/EventEmitter.js");
const util_js_1 = require("../common/util.js");
const disposable_js_1 = require("../util/disposable.js");
const ElementHandle_js_1 = require("./ElementHandle.js");
const JSHandle_js_1 = require("./JSHandle.js");
/**
 * @internal
 */
class IsolatedWorld extends Realm_js_1.Realm {
    #context;
    #emitter = new EventEmitter_js_1.EventEmitter();
    #frameOrWorker;
    constructor(frameOrWorker, timeoutSettings) {
        super(timeoutSettings);
        this.#frameOrWorker = frameOrWorker;
    }
    get environment() {
        return this.#frameOrWorker;
    }
    get client() {
        return this.#frameOrWorker.client;
    }
    get emitter() {
        return this.#emitter;
    }
    setContext(context) {
        this.#context?.[disposable_js_1.disposeSymbol]();
        context.once('disposed', this.#onContextDisposed.bind(this));
        context.on('consoleapicalled', this.#onContextConsoleApiCalled.bind(this));
        context.on('bindingcalled', this.#onContextBindingCalled.bind(this));
        this.#context = context;
        this.#emitter.emit('context', context);
        void this.taskManager.rerunAll();
    }
    #onContextDisposed() {
        this.#context = undefined;
        if ('clearDocumentHandle' in this.#frameOrWorker) {
            this.#frameOrWorker.clearDocumentHandle();
        }
    }
    #onContextConsoleApiCalled(event) {
        this.#emitter.emit('consoleapicalled', event);
    }
    #onContextBindingCalled(event) {
        this.#emitter.emit('bindingcalled', event);
    }
    hasContext() {
        return !!this.#context;
    }
    get context() {
        return this.#context;
    }
    #executionContext() {
        if (this.disposed) {
            throw new Error(`Execution context is not available in detached frame or worker "${this.environment.url()}" (are you trying to evaluate?)`);
        }
        return this.#context;
    }
    /**
     * Waits for the next context to be set on the isolated world.
     */
    async #waitForExecutionContext() {
        const error = new Error('Execution context was destroyed');
        const result = await (0, rxjs_js_1.firstValueFrom)((0, util_js_1.fromEmitterEvent)(this.#emitter, 'context').pipe((0, rxjs_js_1.raceWith)((0, util_js_1.fromEmitterEvent)(this.#emitter, 'disposed').pipe((0, rxjs_js_1.map)(() => {
            // The message has to match the CDP message expected by the WaitTask class.
            throw error;
        })), (0, util_js_1.timeout)(this.timeoutSettings.timeout()))));
        return result;
    }
    async evaluateHandle(pageFunction, ...args) {
        pageFunction = (0, util_js_1.withSourcePuppeteerURLIfNone)(this.evaluateHandle.name, pageFunction);
        // This code needs to schedule evaluateHandle call synchronously (at
        // least when the context is there) so we cannot unconditionally
        // await.
        let context = this.#executionContext();
        if (!context) {
            context = await this.#waitForExecutionContext();
        }
        return await context.evaluateHandle(pageFunction, ...args);
    }
    async evaluate(pageFunction, ...args) {
        pageFunction = (0, util_js_1.withSourcePuppeteerURLIfNone)(this.evaluate.name, pageFunction);
        // This code needs to schedule evaluate call synchronously (at
        // least when the context is there) so we cannot unconditionally
        // await.
        let context = this.#executionContext();
        if (!context) {
            context = await this.#waitForExecutionContext();
        }
        return await context.evaluate(pageFunction, ...args);
    }
    async adoptBackendNode(backendNodeId) {
        // This code needs to schedule resolveNode call synchronously (at
        // least when the context is there) so we cannot unconditionally
        // await.
        let context = this.#executionContext();
        if (!context) {
            context = await this.#waitForExecutionContext();
        }
        const { object } = await this.client.send('DOM.resolveNode', {
            backendNodeId: backendNodeId,
            executionContextId: context.id,
        });
        return this.createCdpHandle(object);
    }
    async adoptHandle(handle) {
        if (handle.realm === this) {
            // If the context has already adopted this handle, clone it so downstream
            // disposal doesn't become an issue.
            return (await handle.evaluateHandle(value => {
                return value;
            }));
        }
        const nodeInfo = await this.client.send('DOM.describeNode', {
            objectId: handle.id,
        });
        return (await this.adoptBackendNode(nodeInfo.node.backendNodeId));
    }
    async transferHandle(handle) {
        if (handle.realm === this) {
            return handle;
        }
        // Implies it's a primitive value, probably.
        if (handle.remoteObject().objectId === undefined) {
            return handle;
        }
        const info = await this.client.send('DOM.describeNode', {
            objectId: handle.remoteObject().objectId,
        });
        const newHandle = (await this.adoptBackendNode(info.node.backendNodeId));
        await handle.dispose();
        return newHandle;
    }
    /**
     * @internal
     */
    createCdpHandle(remoteObject) {
        if (remoteObject.subtype === 'node') {
            return new ElementHandle_js_1.CdpElementHandle(this, remoteObject);
        }
        return new JSHandle_js_1.CdpJSHandle(this, remoteObject);
    }
    [disposable_js_1.disposeSymbol]() {
        this.#context?.[disposable_js_1.disposeSymbol]();
        this.#emitter.emit('disposed', undefined);
        super[disposable_js_1.disposeSymbol]();
        this.#emitter.removeAllListeners();
    }
}
exports.IsolatedWorld = IsolatedWorld;
//# sourceMappingURL=IsolatedWorld.js.map