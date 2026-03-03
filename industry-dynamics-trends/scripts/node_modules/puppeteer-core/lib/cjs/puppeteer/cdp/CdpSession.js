"use strict";
/**
 * @license
 * Copyright 2017 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
Object.defineProperty(exports, "__esModule", { value: true });
exports.CdpCDPSession = void 0;
const CDPSession_js_1 = require("../api/CDPSession.js");
const CallbackRegistry_js_1 = require("../common/CallbackRegistry.js");
const Errors_js_1 = require("../common/Errors.js");
const assert_js_1 = require("../util/assert.js");
const ErrorLike_js_1 = require("../util/ErrorLike.js");
/**
 * @internal
 */
class CdpCDPSession extends CDPSession_js_1.CDPSession {
    #sessionId;
    #targetType;
    #callbacks;
    #connection;
    #parentSessionId;
    #target;
    #rawErrors = false;
    #detached = false;
    /**
     * @internal
     */
    constructor(connection, targetType, sessionId, parentSessionId, rawErrors) {
        super();
        this.#connection = connection;
        this.#targetType = targetType;
        this.#callbacks = new CallbackRegistry_js_1.CallbackRegistry(connection._idGenerator);
        this.#sessionId = sessionId;
        this.#parentSessionId = parentSessionId;
        this.#rawErrors = rawErrors;
    }
    /**
     * Sets the {@link CdpTarget} associated with the session instance.
     *
     * @internal
     */
    setTarget(target) {
        this.#target = target;
    }
    /**
     * Gets the {@link CdpTarget} associated with the session instance.
     *
     * @internal
     */
    target() {
        (0, assert_js_1.assert)(this.#target, 'Target must exist');
        return this.#target;
    }
    connection() {
        return this.#connection;
    }
    get detached() {
        return this.#connection._closed || this.#detached;
    }
    parentSession() {
        if (!this.#parentSessionId) {
            // In some cases, e.g., DevTools pages there is no parent session. In this
            // case, we treat the current session as the parent session.
            return this;
        }
        const parent = this.#connection?.session(this.#parentSessionId);
        return parent ?? undefined;
    }
    send(method, params, options) {
        if (this.detached) {
            return Promise.reject(new Errors_js_1.TargetCloseError(`Protocol error (${method}): Session closed. Most likely the ${this.#targetType} has been closed.`));
        }
        return this.#connection._rawSend(this.#callbacks, method, params, this.#sessionId, options);
    }
    /**
     * @internal
     */
    onMessage(object) {
        if (object.id) {
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
            (0, assert_js_1.assert)(!object.id);
            this.emit(object.method, object.params);
        }
    }
    /**
     * Detaches the cdpSession from the target. Once detached, the cdpSession object
     * won't emit any events and can't be used to send messages.
     */
    async detach() {
        if (this.detached) {
            throw new Error(`Session already detached. Most likely the ${this.#targetType} has been closed.`);
        }
        await this.#connection.send('Target.detachFromTarget', {
            sessionId: this.#sessionId,
        });
        this.#detached = true;
    }
    /**
     * @internal
     */
    onClosed() {
        this.#callbacks.clear();
        this.#detached = true;
        this.emit(CDPSession_js_1.CDPSessionEvent.Disconnected, undefined);
    }
    /**
     * Returns the session's id.
     */
    id() {
        return this.#sessionId;
    }
    /**
     * @internal
     */
    getPendingProtocolErrors() {
        return this.#callbacks.getPendingProtocolErrors();
    }
}
exports.CdpCDPSession = CdpCDPSession;
//# sourceMappingURL=CdpSession.js.map