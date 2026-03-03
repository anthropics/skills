"use strict";;
Object.defineProperty(exports, "__esModule", { value: true });
var tslib_1 = require("tslib");
var types_1 = tslib_1.__importDefault(require("./types"));
function default_1(fork) {
    var types = fork.use(types_1.default);
    var Type = types.Type;
    var builtin = types.builtInTypes;
    var isNumber = builtin.number;
    // An example of constructing a new type with arbitrary constraints from
    // an existing type.
    function geq(than) {
        return Type.from(function (value) { return isNumber.check(value) && value >= than; }, isNumber + " >= " + than);
    }
    ;
    // Default value-returning functions that may optionally be passed as a
    // third argument to Def.prototype.field.
    var defaults = {
        // Functions were used because (among other reasons) that's the most
        // elegant way to allow for the emptyArray one always to give a new
        // array instance.
        "null": function () { return null; },
        "emptyArray": function () { return []; },
        "false": function () { return false; },
        "true": function () { return true; },
        "undefined": function () { },
        "use strict": function () { return "use strict"; }
    };
    var naiveIsPrimitive = Type.or(builtin.string, builtin.number, builtin.boolean, builtin.null, builtin.undefined);
    var isPrimitive = Type.from(function (value) {
        if (value === null)
            return true;
        var type = typeof value;
        if (type === "object" ||
            type === "function") {
            return false;
        }
        return true;
    }, naiveIsPrimitive.toString());
    return {
        geq: geq,
        defaults: defaults,
        isPrimitive: isPrimitive,
    };
}
exports.default = default_1;
module.exports = exports["default"];
