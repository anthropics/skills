"use strict";
/**
 * @license
 * Copyright 2025 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
Object.defineProperty(exports, "__esModule", { value: true });
exports.BidiDeviceRequestPrompt = exports.BidiDeviceRequestPromptManager = void 0;
const DeviceRequestPrompt_js_1 = require("../api/DeviceRequestPrompt.js");
const Errors_js_1 = require("../common/Errors.js");
const Deferred_js_1 = require("../util/Deferred.js");
/**
 * @internal
 */
class BidiDeviceRequestPromptManager {
    #session;
    #contextId;
    #enabled = false;
    constructor(contextId, session) {
        this.#session = session;
        this.#contextId = contextId;
    }
    async #enableIfNeeded() {
        if (!this.#enabled) {
            this.#enabled = true;
            await this.#session.subscribe(['bluetooth.requestDevicePromptUpdated'], [this.#contextId]);
        }
    }
    async waitForDevicePrompt(timeout, signal) {
        const deferred = Deferred_js_1.Deferred.create({
            message: `Waiting for \`DeviceRequestPrompt\` failed: ${timeout}ms exceeded`,
            timeout,
        });
        const onRequestDevicePromptUpdated = (params) => {
            if (params.context === this.#contextId) {
                deferred.resolve(new BidiDeviceRequestPrompt(this.#contextId, params.prompt, this.#session, params.devices));
                this.#session.off('bluetooth.requestDevicePromptUpdated', onRequestDevicePromptUpdated);
            }
        };
        this.#session.on('bluetooth.requestDevicePromptUpdated', onRequestDevicePromptUpdated);
        if (signal) {
            signal.addEventListener('abort', () => {
                deferred.reject(signal.reason);
            }, { once: true });
        }
        await this.#enableIfNeeded();
        return await deferred.valueOrThrow();
    }
}
exports.BidiDeviceRequestPromptManager = BidiDeviceRequestPromptManager;
/**
 * @internal
 */
class BidiDeviceRequestPrompt extends DeviceRequestPrompt_js_1.DeviceRequestPrompt {
    #session;
    #promptId;
    #contextId;
    constructor(contextId, promptId, session, devices) {
        super();
        this.#session = session;
        this.#promptId = promptId;
        this.#contextId = contextId;
        this.devices.push(...devices.map(d => {
            return {
                id: d.id,
                name: d.name ?? 'UNKNOWN',
            };
        }));
    }
    async cancel() {
        await this.#session.send('bluetooth.handleRequestDevicePrompt', {
            context: this.#contextId,
            prompt: this.#promptId,
            accept: false,
        });
    }
    async select(device) {
        await this.#session.send('bluetooth.handleRequestDevicePrompt', {
            context: this.#contextId,
            prompt: this.#promptId,
            accept: true,
            device: device.id,
        });
    }
    waitForDevice() {
        throw new Errors_js_1.UnsupportedOperation();
    }
}
exports.BidiDeviceRequestPrompt = BidiDeviceRequestPrompt;
//# sourceMappingURL=DeviceRequestPrompt.js.map