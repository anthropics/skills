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
exports.InputStateManager = void 0;
const assert_js_1 = require("../../../utils/assert.js");
const InputState_js_1 = require("./InputState.js");
// We use a weak map here as specified here:
// https://www.w3.org/TR/webdriver/#dfn-browsing-context-input-state-map
class InputStateManager extends WeakMap {
    get(context) {
        (0, assert_js_1.assert)(context.isTopLevelContext());
        if (!this.has(context)) {
            this.set(context, new InputState_js_1.InputState());
        }
        return super.get(context);
    }
}
exports.InputStateManager = InputStateManager;
//# sourceMappingURL=InputStateManager.js.map