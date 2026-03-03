"use strict";
/**
 * Copyright 2021 Google LLC.
 * Copyright (c) Microsoft Corporation.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
Object.defineProperty(exports, "__esModule", { value: true });
exports.BidiServer = void 0;
const EventEmitter_js_1 = require("../utils/EventEmitter.js");
const log_js_1 = require("../utils/log.js");
const ProcessingQueue_js_1 = require("../utils/ProcessingQueue.js");
const CommandProcessor_js_1 = require("./CommandProcessor.js");
const BluetoothProcessor_js_1 = require("./modules/bluetooth/BluetoothProcessor.js");
const ContextConfigStorage_js_1 = require("./modules/browser/ContextConfigStorage.js");
const UserContextStorage_js_1 = require("./modules/browser/UserContextStorage.js");
const CdpTargetManager_js_1 = require("./modules/cdp/CdpTargetManager.js");
const BrowsingContextStorage_js_1 = require("./modules/context/BrowsingContextStorage.js");
const NetworkStorage_js_1 = require("./modules/network/NetworkStorage.js");
const PreloadScriptStorage_js_1 = require("./modules/script/PreloadScriptStorage.js");
const RealmStorage_js_1 = require("./modules/script/RealmStorage.js");
const EventManager_js_1 = require("./modules/session/EventManager.js");
const SpeculationProcessor_js_1 = require("./modules/speculation/SpeculationProcessor.js");
class BidiServer extends EventEmitter_js_1.EventEmitter {
    #messageQueue;
    #transport;
    #commandProcessor;
    #eventManager;
    #browsingContextStorage = new BrowsingContextStorage_js_1.BrowsingContextStorage();
    #realmStorage = new RealmStorage_js_1.RealmStorage();
    #preloadScriptStorage = new PreloadScriptStorage_js_1.PreloadScriptStorage();
    #bluetoothProcessor;
    #speculationProcessor;
    #logger;
    #handleIncomingMessage = (message) => {
        void this.#commandProcessor.processCommand(message).catch((error) => {
            this.#logger?.(log_js_1.LogType.debugError, error);
        });
    };
    #processOutgoingMessage = async (messageEntry) => {
        const message = messageEntry.message;
        if (messageEntry.googChannel !== null) {
            message['goog:channel'] = messageEntry.googChannel;
        }
        await this.#transport.sendMessage(message);
    };
    constructor(bidiTransport, cdpConnection, browserCdpClient, selfTargetId, defaultUserContextId, defaultUserAgent, parser, logger) {
        super();
        this.#logger = logger;
        this.#messageQueue = new ProcessingQueue_js_1.ProcessingQueue(this.#processOutgoingMessage, this.#logger);
        this.#transport = bidiTransport;
        this.#transport.setOnMessage(this.#handleIncomingMessage);
        const contextConfigStorage = new ContextConfigStorage_js_1.ContextConfigStorage();
        const userContextStorage = new UserContextStorage_js_1.UserContextStorage(browserCdpClient);
        this.#eventManager = new EventManager_js_1.EventManager(this.#browsingContextStorage, userContextStorage);
        const networkStorage = new NetworkStorage_js_1.NetworkStorage(this.#eventManager, this.#browsingContextStorage, browserCdpClient, logger);
        this.#bluetoothProcessor = new BluetoothProcessor_js_1.BluetoothProcessor(this.#eventManager, this.#browsingContextStorage);
        this.#speculationProcessor = new SpeculationProcessor_js_1.SpeculationProcessor(this.#eventManager, this.#logger);
        this.#commandProcessor = new CommandProcessor_js_1.CommandProcessor(cdpConnection, browserCdpClient, this.#eventManager, this.#browsingContextStorage, this.#realmStorage, this.#preloadScriptStorage, networkStorage, contextConfigStorage, this.#bluetoothProcessor, userContextStorage, parser, async (options) => {
            // This is required to ignore certificate errors when service worker is fetched.
            await browserCdpClient.sendCommand('Security.setIgnoreCertificateErrors', {
                ignore: options.acceptInsecureCerts ?? false,
            });
            contextConfigStorage.updateGlobalConfig({
                acceptInsecureCerts: options.acceptInsecureCerts ?? false,
                userPromptHandler: options.unhandledPromptBehavior,
                prerenderingDisabled: options?.['goog:prerenderingDisabled'] ?? false,
                disableNetworkDurableMessages: options?.['goog:disableNetworkDurableMessages'],
            });
            new CdpTargetManager_js_1.CdpTargetManager(cdpConnection, browserCdpClient, selfTargetId, this.#eventManager, this.#browsingContextStorage, this.#realmStorage, networkStorage, contextConfigStorage, this.#bluetoothProcessor, this.#speculationProcessor, this.#preloadScriptStorage, defaultUserContextId, defaultUserAgent, logger);
            // Needed to get events about new targets.
            await browserCdpClient.sendCommand('Target.setDiscoverTargets', {
                discover: true,
            });
            // Needed to automatically attach to new targets.
            await browserCdpClient.sendCommand('Target.setAutoAttach', {
                autoAttach: true,
                waitForDebuggerOnStart: true,
                flatten: true,
                // Browser session should attach to tab instead of the page, so that
                // prerendering is not blocked.
                filter: [
                    {
                        type: 'page',
                        exclude: true,
                    },
                    {},
                ],
            });
            await this.#topLevelContextsLoaded();
        }, this.#logger);
        this.#eventManager.on("event" /* EventManagerEvents.Event */, ({ message, event }) => {
            this.emitOutgoingMessage(message, event);
        });
        this.#commandProcessor.on("response" /* CommandProcessorEvents.Response */, ({ message, event }) => {
            this.emitOutgoingMessage(message, event);
        });
    }
    /**
     * Creates and starts BiDi Mapper instance.
     */
    static async createAndStart(bidiTransport, cdpConnection, browserCdpClient, selfTargetId, parser, logger) {
        const [defaultUserContextId, version] = await Promise.all([
            this.#getDefaultUserContextId(browserCdpClient),
            // Fetch the default User Agent to be used in `CdpTarget`. This allows to avoid
            // round trips to the browser for every target override.
            browserCdpClient.sendCommand('Browser.getVersion'),
            // Required for `Browser.downloadWillBegin` events.
            browserCdpClient.sendCommand('Browser.setDownloadBehavior', {
                behavior: 'default',
                eventsEnabled: true,
            }),
        ]);
        const server = new BidiServer(bidiTransport, cdpConnection, browserCdpClient, selfTargetId, defaultUserContextId, version.userAgent, parser, logger);
        return server;
    }
    static async #getDefaultUserContextId(browserCdpClient) {
        // In chromium before `145.0.7578.0`, the default context is not exposed in
        // `Target.getBrowserContexts`, but can be observed via `Target.getTargets`.
        // If so, try to determine the default browser context by checking which one
        // is mentioned in `Target.getTargets` and not in
        // `Target.getBrowserContexts`.
        // TODO(after 2026-02-24): rely only on `defaultBrowserContextId` from
        // `Target.getBrowserContexts` after Chromium 145 reaches stable.
        const [{ defaultBrowserContextId, browserContextIds }, { targetInfos }] = await Promise.all([
            browserCdpClient.sendCommand('Target.getBrowserContexts'),
            browserCdpClient.sendCommand('Target.getTargets'),
        ]);
        if (defaultBrowserContextId) {
            return defaultBrowserContextId;
        }
        for (const info of targetInfos) {
            if (info.browserContextId &&
                !browserContextIds.includes(info.browserContextId)) {
                // The target belongs to a browser context that is not mentioned in
                // `Target.getBrowserContexts`. This is the default browser context.
                return info.browserContextId;
            }
        }
        // The browser context is unknown.
        return 'default';
    }
    /**
     * Sends BiDi message.
     */
    emitOutgoingMessage(messageEntry, event) {
        this.#messageQueue.add(messageEntry, event);
    }
    close() {
        this.#transport.close();
    }
    async #topLevelContextsLoaded() {
        await Promise.all(this.#browsingContextStorage
            .getTopLevelContexts()
            .map((c) => c.lifecycleLoaded()));
    }
}
exports.BidiServer = BidiServer;
//# sourceMappingURL=BidiServer.js.map