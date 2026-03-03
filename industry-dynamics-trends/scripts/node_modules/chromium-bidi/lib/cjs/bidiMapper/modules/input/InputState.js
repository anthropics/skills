"use strict";
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
Object.defineProperty(exports, "__esModule", { value: true });
exports.InputState = void 0;
const protocol_js_1 = require("../../../protocol/protocol.js");
const Mutex_js_1 = require("../../../utils/Mutex.js");
const InputSource_js_1 = require("./InputSource.js");
class InputState {
    cancelList = [];
    #sources = new Map();
    #mutex = new Mutex_js_1.Mutex();
    getOrCreate(id, type, subtype) {
        let source = this.#sources.get(id);
        if (!source) {
            switch (type) {
                case "none" /* SourceType.None */:
                    source = new InputSource_js_1.NoneSource();
                    break;
                case "key" /* SourceType.Key */:
                    source = new InputSource_js_1.KeySource();
                    break;
                case "pointer" /* SourceType.Pointer */: {
                    let pointerId = subtype === "mouse" /* Input.PointerType.Mouse */ ? 0 : 2;
                    const pointerIds = new Set();
                    for (const [, source] of this.#sources) {
                        if (source.type === "pointer" /* SourceType.Pointer */) {
                            pointerIds.add(source.pointerId);
                        }
                    }
                    while (pointerIds.has(pointerId)) {
                        ++pointerId;
                    }
                    source = new InputSource_js_1.PointerSource(pointerId, subtype);
                    break;
                }
                case "wheel" /* SourceType.Wheel */:
                    source = new InputSource_js_1.WheelSource();
                    break;
                default:
                    throw new protocol_js_1.InvalidArgumentException(`Expected "${"none" /* SourceType.None */}", "${"key" /* SourceType.Key */}", "${"pointer" /* SourceType.Pointer */}", or "${"wheel" /* SourceType.Wheel */}". Found unknown source type ${type}.`);
            }
            this.#sources.set(id, source);
            return source;
        }
        if (source.type !== type) {
            throw new protocol_js_1.InvalidArgumentException(`Input source type of ${id} is ${source.type}, but received ${type}.`);
        }
        return source;
    }
    get(id) {
        const source = this.#sources.get(id);
        if (!source) {
            throw new protocol_js_1.UnknownErrorException(`Internal error.`);
        }
        return source;
    }
    getGlobalKeyState() {
        const state = new InputSource_js_1.KeySource();
        for (const [, source] of this.#sources) {
            if (source.type !== "key" /* SourceType.Key */) {
                continue;
            }
            for (const pressed of source.pressed) {
                state.pressed.add(pressed);
            }
            state.alt ||= source.alt;
            state.ctrl ||= source.ctrl;
            state.meta ||= source.meta;
            state.shift ||= source.shift;
        }
        return state;
    }
    get queue() {
        return this.#mutex;
    }
}
exports.InputState = InputState;
//# sourceMappingURL=InputState.js.map