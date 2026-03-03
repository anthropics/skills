"use strict";
/**
 * Copyright 2025 Google LLC.
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
exports.SpeculationProcessor = void 0;
const log_js_1 = require("../../../utils/log.js");
class SpeculationProcessor {
    #eventManager;
    #logger;
    constructor(eventManager, logger) {
        this.#eventManager = eventManager;
        this.#logger = logger;
    }
    onCdpTargetCreated(cdpTarget) {
        cdpTarget.cdpClient.on('Preload.prefetchStatusUpdated', (event) => {
            let prefetchStatus;
            switch (event.status) {
                case 'Running':
                    prefetchStatus = "pending" /* Speculation.PreloadingStatus.Pending */;
                    break;
                case 'Ready':
                    prefetchStatus = "ready" /* Speculation.PreloadingStatus.Ready */;
                    break;
                case 'Success':
                    prefetchStatus = "success" /* Speculation.PreloadingStatus.Success */;
                    break;
                case 'Failure':
                    prefetchStatus = "failure" /* Speculation.PreloadingStatus.Failure */;
                    break;
                default:
                    // If status is not recognized, skip the event
                    this.#logger?.(log_js_1.LogType.debugWarn, `Unknown prefetch status: ${event.status}`);
                    return;
            }
            this.#eventManager.registerEvent({
                type: 'event',
                method: 'speculation.prefetchStatusUpdated',
                params: {
                    context: event.initiatingFrameId,
                    url: event.prefetchUrl,
                    status: prefetchStatus,
                },
            }, cdpTarget.id);
        });
    }
}
exports.SpeculationProcessor = SpeculationProcessor;
//# sourceMappingURL=SpeculationProcessor.js.map