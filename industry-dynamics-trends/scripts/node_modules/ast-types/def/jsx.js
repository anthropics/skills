"use strict";;
Object.defineProperty(exports, "__esModule", { value: true });
var tslib_1 = require("tslib");
var es7_1 = tslib_1.__importDefault(require("./es7"));
var types_1 = tslib_1.__importDefault(require("../lib/types"));
var shared_1 = tslib_1.__importDefault(require("../lib/shared"));
function default_1(fork) {
    fork.use(es7_1.default);
    var types = fork.use(types_1.default);
    var def = types.Type.def;
    var or = types.Type.or;
    var defaults = fork.use(shared_1.default).defaults;
    def("JSXAttribute")
        .bases("Node")
        .build("name", "value")
        .field("name", or(def("JSXIdentifier"), def("JSXNamespacedName")))
        .field("value", or(def("Literal"), // attr="value"
    def("JSXExpressionContainer"), // attr={value}
    null // attr= or just attr
    ), defaults["null"]);
    def("JSXIdentifier")
        .bases("Identifier")
        .build("name")
        .field("name", String);
    def("JSXNamespacedName")
        .bases("Node")
        .build("namespace", "name")
        .field("namespace", def("JSXIdentifier"))
        .field("name", def("JSXIdentifier"));
    def("JSXMemberExpression")
        .bases("MemberExpression")
        .build("object", "property")
        .field("object", or(def("JSXIdentifier"), def("JSXMemberExpression")))
        .field("property", def("JSXIdentifier"))
        .field("computed", Boolean, defaults.false);
    var JSXElementName = or(def("JSXIdentifier"), def("JSXNamespacedName"), def("JSXMemberExpression"));
    def("JSXSpreadAttribute")
        .bases("Node")
        .build("argument")
        .field("argument", def("Expression"));
    var JSXAttributes = [or(def("JSXAttribute"), def("JSXSpreadAttribute"))];
    def("JSXExpressionContainer")
        .bases("Expression")
        .build("expression")
        .field("expression", def("Expression"));
    def("JSXElement")
        .bases("Expression")
        .build("openingElement", "closingElement", "children")
        .field("openingElement", def("JSXOpeningElement"))
        .field("closingElement", or(def("JSXClosingElement"), null), defaults["null"])
        .field("children", [or(def("JSXElement"), def("JSXExpressionContainer"), def("JSXFragment"), def("JSXText"), def("Literal") // TODO Esprima should return JSXText instead.
        )], defaults.emptyArray)
        .field("name", JSXElementName, function () {
        // Little-known fact: the `this` object inside a default function
        // is none other than the partially-built object itself, and any
        // fields initialized directly from builder function arguments
        // (like openingElement, closingElement, and children) are
        // guaranteed to be available.
        return this.openingElement.name;
    }, true) // hidden from traversal
        .field("selfClosing", Boolean, function () {
        return this.openingElement.selfClosing;
    }, true) // hidden from traversal
        .field("attributes", JSXAttributes, function () {
        return this.openingElement.attributes;
    }, true); // hidden from traversal
    def("JSXOpeningElement")
        .bases("Node") // TODO Does this make sense? Can't really be an JSXElement.
        .build("name", "attributes", "selfClosing")
        .field("name", JSXElementName)
        .field("attributes", JSXAttributes, defaults.emptyArray)
        .field("selfClosing", Boolean, defaults["false"]);
    def("JSXClosingElement")
        .bases("Node") // TODO Same concern.
        .build("name")
        .field("name", JSXElementName);
    def("JSXFragment")
        .bases("Expression")
        .build("openingElement", "closingElement", "children")
        .field("openingElement", def("JSXOpeningFragment"))
        .field("closingElement", def("JSXClosingFragment"))
        .field("children", [or(def("JSXElement"), def("JSXExpressionContainer"), def("JSXFragment"), def("JSXText"), def("Literal") // TODO Esprima should return JSXText instead.
        )], defaults.emptyArray);
    def("JSXOpeningFragment")
        .bases("Node") // TODO Same concern.
        .build();
    def("JSXClosingFragment")
        .bases("Node") // TODO Same concern.
        .build();
    def("JSXText")
        .bases("Literal")
        .build("value")
        .field("value", String);
    def("JSXEmptyExpression").bases("Expression").build();
    // This PR has caused many people issues, but supporting it seems like a
    // good idea anyway: https://github.com/babel/babel/pull/4988
    def("JSXSpreadChild")
        .bases("Expression")
        .build("expression")
        .field("expression", def("Expression"));
}
exports.default = default_1;
module.exports = exports["default"];
