"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.debugLog = exports.QTS_DEBUG = void 0;
exports.QTS_DEBUG = false || Boolean(typeof process === "object" && process.env.QTS_DEBUG);
exports.debugLog = exports.QTS_DEBUG ? console.log.bind(console) : () => { };
//# sourceMappingURL=debug.js.map