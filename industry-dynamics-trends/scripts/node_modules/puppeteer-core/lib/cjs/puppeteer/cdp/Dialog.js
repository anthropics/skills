"use strict";
/**
 * @license
 * Copyright 2017 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
Object.defineProperty(exports, "__esModule", { value: true });
exports.CdpDialog = void 0;
const Dialog_js_1 = require("../api/Dialog.js");
/**
 * @internal
 */
class CdpDialog extends Dialog_js_1.Dialog {
    #client;
    constructor(client, type, message, defaultValue = '') {
        super(type, message, defaultValue);
        this.#client = client;
    }
    async handle(options) {
        await this.#client.send('Page.handleJavaScriptDialog', {
            accept: options.accept,
            promptText: options.text,
        });
    }
}
exports.CdpDialog = CdpDialog;
//# sourceMappingURL=Dialog.js.map