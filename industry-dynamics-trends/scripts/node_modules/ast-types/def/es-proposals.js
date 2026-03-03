"use strict";;
Object.defineProperty(exports, "__esModule", { value: true });
var tslib_1 = require("tslib");
var types_1 = tslib_1.__importDefault(require("../lib/types"));
var shared_1 = tslib_1.__importDefault(require("../lib/shared"));
var core_1 = tslib_1.__importDefault(require("./core"));
function default_1(fork) {
    fork.use(core_1.default);
    var types = fork.use(types_1.default);
    var Type = types.Type;
    var def = types.Type.def;
    var or = Type.or;
    var shared = fork.use(shared_1.default);
    var defaults = shared.defaults;
    // https://github.com/tc39/proposal-optional-chaining
    // `a?.b` as per https://github.com/estree/estree/issues/146
    def("OptionalMemberExpression")
        .bases("MemberExpression")
        .build("object", "property", "computed", "optional")
        .field("optional", Boolean, defaults["true"]);
    // a?.b()
    def("OptionalCallExpression")
        .bases("CallExpression")
        .build("callee", "arguments", "optional")
        .field("optional", Boolean, defaults["true"]);
    // https://github.com/tc39/proposal-nullish-coalescing
    // `a ?? b` as per https://github.com/babel/babylon/pull/761/files
    var LogicalOperator = or("||", "&&", "??");
    def("LogicalExpression")
        .field("operator", LogicalOperator);
}
exports.default = default_1;
module.exports = exports["default"];
