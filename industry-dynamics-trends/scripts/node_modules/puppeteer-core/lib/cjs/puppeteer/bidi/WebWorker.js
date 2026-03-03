"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.BidiWebWorker = void 0;
/**
 * @license
 * Copyright 2024 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
const WebWorker_js_1 = require("../api/WebWorker.js");
const Errors_js_1 = require("../common/Errors.js");
const Realm_js_1 = require("./Realm.js");
/**
 * @internal
 */
class BidiWebWorker extends WebWorker_js_1.WebWorker {
    static from(frame, realm) {
        const worker = new BidiWebWorker(frame, realm);
        return worker;
    }
    #frame;
    #realm;
    constructor(frame, realm) {
        super(realm.origin);
        this.#frame = frame;
        this.#realm = Realm_js_1.BidiWorkerRealm.from(realm, this);
    }
    get frame() {
        return this.#frame;
    }
    mainRealm() {
        return this.#realm;
    }
    get client() {
        throw new Errors_js_1.UnsupportedOperation();
    }
}
exports.BidiWebWorker = BidiWebWorker;
//# sourceMappingURL=WebWorker.js.map