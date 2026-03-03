"use strict";;
Object.defineProperty(exports, "__esModule", { value: true });
var tslib_1 = require("tslib");
var babel_core_1 = tslib_1.__importDefault(require("./babel-core"));
var flow_1 = tslib_1.__importDefault(require("./flow"));
function default_1(fork) {
    fork.use(babel_core_1.default);
    fork.use(flow_1.default);
}
exports.default = default_1;
module.exports = exports["default"];
