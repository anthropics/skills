"use strict";
/**
 * @license
 * Copyright 2023 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
exports.rm = rm;
exports.rmSync = rmSync;
const node_fs_1 = __importDefault(require("node:fs"));
const rmOptions = {
    force: true,
    recursive: true,
    maxRetries: 5,
};
/**
 * @internal
 */
async function rm(path) {
    await node_fs_1.default.promises.rm(path, rmOptions);
}
/**
 * @internal
 */
function rmSync(path) {
    node_fs_1.default.rmSync(path, rmOptions);
}
//# sourceMappingURL=fs.js.map