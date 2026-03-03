"use strict";;
Object.defineProperty(exports, "__esModule", { value: true });
var tslib_1 = require("tslib");
var es7_1 = tslib_1.__importDefault(require("./es7"));
var types_1 = tslib_1.__importDefault(require("../lib/types"));
function default_1(fork) {
    fork.use(es7_1.default);
    var types = fork.use(types_1.default);
    var def = types.Type.def;
    def("ImportExpression")
        .bases("Expression")
        .build("source")
        .field("source", def("Expression"));
}
exports.default = default_1;
module.exports = exports["default"];
