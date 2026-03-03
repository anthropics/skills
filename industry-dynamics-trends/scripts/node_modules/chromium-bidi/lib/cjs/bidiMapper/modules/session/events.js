"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.isCdpEvent = isCdpEvent;
exports.assertSupportedEvent = assertSupportedEvent;
/**
 * Copyright 2023 Google LLC.
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
const protocol_js_1 = require("../../../protocol/protocol.js");
/**
 * Returns true if the given event is a CDP event.
 * @see https://chromedevtools.github.io/devtools-protocol/
 */
function isCdpEvent(name) {
    return (name.split('.').at(0)?.startsWith(protocol_js_1.ChromiumBidi.BiDiModule.Cdp) ?? false);
}
/**
 * Asserts that the given event is known to BiDi or BiDi+, or throws otherwise.
 */
function assertSupportedEvent(name) {
    if (!protocol_js_1.ChromiumBidi.EVENT_NAMES.has(name) && !isCdpEvent(name)) {
        throw new protocol_js_1.InvalidArgumentException(`Unknown event: ${name}`);
    }
}
//# sourceMappingURL=events.js.map