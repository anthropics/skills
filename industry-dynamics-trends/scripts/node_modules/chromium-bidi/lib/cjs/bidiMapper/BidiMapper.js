"use strict";
/**
 * Copyright 2022 Google LLC.
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
exports.OutgoingMessage = exports.EventEmitter = exports.BidiServer = void 0;
/**
 * @fileoverview The entry point to the BiDi Mapper namespace.
 * Other modules should only access exports defined in this file.
 * XXX: Add ESlint rule for this (https://github.com/import-js/eslint-plugin-import/blob/main/docs/rules/no-restricted-paths.md)
 */
var BidiServer_js_1 = require("./BidiServer.js");
Object.defineProperty(exports, "BidiServer", { enumerable: true, get: function () { return BidiServer_js_1.BidiServer; } });
var EventEmitter_js_1 = require("../utils/EventEmitter.js");
Object.defineProperty(exports, "EventEmitter", { enumerable: true, get: function () { return EventEmitter_js_1.EventEmitter; } });
var OutgoingMessage_js_1 = require("./OutgoingMessage.js");
Object.defineProperty(exports, "OutgoingMessage", { enumerable: true, get: function () { return OutgoingMessage_js_1.OutgoingMessage; } });
//# sourceMappingURL=BidiMapper.js.map