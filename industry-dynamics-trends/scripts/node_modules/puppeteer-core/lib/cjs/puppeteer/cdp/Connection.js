"use strict";
/**
 * @license
 * Copyright 2017 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
Object.defineProperty(exports, "__esModule", { value: true });
exports.Connection = void 0;
exports.isTargetClosedError = isTargetClosedError;
const CDPSession_js_1 = require("../api/CDPSession.js");
const CallbackRegistry_js_1 = require("../common/CallbackRegistry.js");
const Debug_js_1 = require("../common/Debug.js");
const Errors_js_1 = require("../common/Errors.js");
const EventEmitter_js_1 = require("../common/EventEmitter.js");
const ErrorLike_js_1 = require("../util/ErrorLike.js");
const incremental_id_generator_js_1 = require("../util/incremental-id-generator.js");
const CdpSession_js_1 = require("./CdpSession.js");
const debugProtocolSend = (0, Debug_js_1.debug)('puppeteer:protocol:SEND ►');
const debugProtocolReceive = (0, Debug_js_1.debug)('puppeteer:protocol:RECV ◀');
/**
 * @public
 */
class Connection extends EventEmitter_js_1.EventEmitter {
    #url;
    #transport;
    #delay;
    #timeout;
    #sessions = new Map();
    #closed = false;
    #manuallyAttached = new Set();
    #callbacks;
    #rawErrors = false;
    #idGenerator;
    constructor(url, transport, delay = 0, timeout, rawErrors = false, idGenerator = (0, incremental_id_generator_js_1.createIncrementalIdGenerator)()) {
        super();
        this.#rawErrors = rawErrors;
        this.#idGenerator = idGenerator;
        this.#callbacks = new CallbackRegistry_js_1.CallbackRegistry(idGenerator);
        this.#url = url;
        this.#delay = delay;
        this.#timeout = timeout ?? 180_000;
        this.#transport = transport;
        this.#transport.onmessage = this.onMessage.bind(this);
        this.#transport.onclose = this.#onClose.bind(this);
    }
    static fromSession(session) {
        return session.connection();
    }
    /**
     * @internal
     */
    get delay() {
        return this.#delay;
    }
    get timeout() {
        return this.#timeout;
    }
    /**
     * @internal
     */
    get _closed() {
        return this.#closed;
    }
    /**
     * @internal
     */
    get _idGenerator() {
        return this.#idGenerator;
    }
    /**
     * @internal
     */
    get _sessions() {
        return this.#sessions;
    }
    /**
     * @internal
     */
    _session(sessionId) {
        return this.#sessions.get(sessionId) || null;
    }
    /**
     * @param sessionId - The session id
     * @returns The current CDP session if it exists
     */
    session(sessionId) {
        return this._session(sessionId);
    }
    url() {
        return this.#url;
    }
    send(method, params, options) {
        // There is only ever 1 param arg passed, but the Protocol defines it as an
        // array of 0 or 1 items See this comment:
        // https://github.com/ChromeDevTools/devtools-protocol/pull/113#issuecomment-412603285
        // which explains why the protocol defines the params this way for better
        // type-inference.
        // So now we check if there are any params or not and deal with them accordingly.
        return this._rawSend(this.#callbacks, method, params, undefined, options);
    }
    /**
     * @internal
     */
    _rawSend(callbacks, method, params, sessionId, options) {
        if (this.#closed) {
            return Promise.reject(new Errors_js_1.ConnectionClosedError('Connection closed.'));
        }
        return callbacks.create(method, options?.timeout ?? this.#timeout, id => {
            const stringifiedMessage = JSON.stringify({
                method,
                params,
                id,
                sessionId,
            });
            debugProtocolSend(stringifiedMessage);
            this.#transport.send(stringifiedMessage);
        });
    }
    /**
     * @internal
     */
    async closeBrowser() {
        await this.send('Browser.close');
    }
    /**
     * @internal
     */
    async onMessage(message) {
        if (this.#delay) {
            await new Promise(r => {
                return setTimeout(r, this.#delay);
            });
        }
        debugProtocolReceive(message);
        const object = JSON.parse(message);
        if (object.method === 'Target.attachedToTarget') {
            const sessionId = object.params.sessionId;
            const session = new CdpSession_js_1.CdpCDPSession(this, object.params.targetInfo.type, sessionId, object.sessionId, this.#rawErrors);
            this.#sessions.set(sessionId, session);
            this.emit(CDPSession_js_1.CDPSessionEvent.SessionAttached, session);
            const parentSession = this.#sessions.get(object.sessionId);
            if (parentSession) {
                parentSession.emit(CDPSession_js_1.CDPSessionEvent.SessionAttached, session);
            }
        }
        else if (object.method === 'Target.detachedFromTarget') {
            const session = this.#sessions.get(object.params.sessionId);
            if (session) {
                session.onClosed();
                this.#sessions.delete(object.params.sessionId);
                this.emit(CDPSession_js_1.CDPSessionEvent.SessionDetached, session);
                const parentSession = this.#sessions.get(object.sessionId);
                if (parentSession) {
                    parentSession.emit(CDPSession_js_1.CDPSessionEvent.SessionDetached, session);
                }
            }
        }
        if (object.sessionId) {
            const session = this.#sessions.get(object.sessionId);
            if (session) {
                session.onMessage(object);
            }
        }
        else if (object.id) {
            if (object.error) {
                if (this.#rawErrors) {
                    this.#callbacks.rejectRaw(object.id, object.error);
                }
                else {
                    this.#callbacks.reject(object.id, (0, ErrorLike_js_1.createProtocolErrorMessage)(object), object.error.message);
                }
            }
            else {
                this.#callbacks.resolve(object.id, object.result);
            }
        }
        else {
            this.emit(object.method, object.params);
        }
    }
    #onClose() {
        if (this.#closed) {
            return;
        }
        this.#closed = true;
        this.#transport.onmessage = undefined;
        this.#transport.onclose = undefined;
        this.#callbacks.clear();
        for (const session of this.#sessions.values()) {
            session.onClosed();
        }
        this.#sessions.clear();
        this.emit(CDPSession_js_1.CDPSessionEvent.Disconnected, undefined);
    }
    dispose() {
        this.#onClose();
        this.#transport.close();
    }
    /**
     * @internal
     */
    isAutoAttached(targetId) {
        return !this.#manuallyAttached.has(targetId);
    }
    /**
     * @internal
     */
    async _createSession(targetInfo, isAutoAttachEmulated = true) {
        if (!isAutoAttachEmulated) {
            this.#manuallyAttached.add(targetInfo.targetId);
        }
        const { sessionId } = await this.send('Target.attachToTarget', {
            targetId: targetInfo.targetId,
            flatten: true,
        });
        this.#manuallyAttached.delete(targetInfo.targetId);
        const session = this.#sessions.get(sessionId);
        if (!session) {
            throw new Error('CDPSession creation failed.');
        }
        return session;
    }
    /**
     * @param targetInfo - The target info
     * @returns The CDP session that is created
     */
    async createSession(targetInfo) {
        return await this._createSession(targetInfo, false);
    }
    /**
     * @internal
     */
    getPendingProtocolErrors() {
        const result = [];
        result.push(...this.#callbacks.getPendingProtocolErrors());
        for (const session of this.#sessions.values()) {
            result.push(...session.getPendingProtocolErrors());
        }
        return result;
    }
}
exports.Connection = Connection;
/**
 * @internal
 */
function isTargetClosedError(error) {
    return error instanceof Errors_js_1.TargetCloseError;
}
//# sourceMappingURL=Connection.js.map