"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
exports.https = void 0;
const https_1 = __importDefault(require("https"));
const http_1 = require("./http");
/**
 * Returns a Readable stream from an "https:" URI.
 */
const https = (url, opts) => {
    return (0, http_1.http)(url, { ...opts, http: https_1.default });
};
exports.https = https;
//# sourceMappingURL=https.js.map