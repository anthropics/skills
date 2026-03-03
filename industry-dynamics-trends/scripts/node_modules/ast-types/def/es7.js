"use strict";;
Object.defineProperty(exports, "__esModule", { value: true });
var tslib_1 = require("tslib");
var es6_1 = tslib_1.__importDefault(require("./es6"));
var types_1 = tslib_1.__importDefault(require("../lib/types"));
var shared_1 = tslib_1.__importDefault(require("../lib/shared"));
function default_1(fork) {
    fork.use(es6_1.default);
    var types = fork.use(types_1.default);
    var def = types.Type.def;
    var or = types.Type.or;
    var defaults = fork.use(shared_1.default).defaults;
    def("Function")
        .field("async", Boolean, defaults["false"]);
    def("SpreadProperty")
        .bases("Node")
        .build("argument")
        .field("argument", def("Expression"));
    def("ObjectExpression")
        .field("properties", [or(def("Property"), def("SpreadProperty"), def("SpreadElement"))]);
    def("SpreadPropertyPattern")
        .bases("Pattern")
        .build("argument")
        .field("argument", def("Pattern"));
    def("ObjectPattern")
        .field("properties", [or(def("Property"), def("PropertyPattern"), def("SpreadPropertyPattern"))]);
    def("AwaitExpression")
        .bases("Expression")
        .build("argument", "all")
        .field("argument", or(def("Expression"), null))
        .field("all", Boolean, defaults["false"]);
}
exports.default = default_1;
module.exports = exports["default"];
