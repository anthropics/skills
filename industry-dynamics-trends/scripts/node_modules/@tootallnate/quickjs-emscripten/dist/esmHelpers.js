"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.unwrapJavascript = exports.unwrapTypescript = void 0;
/** Typescript thinks import('...js/.d.ts') needs mod.default.default */
function fakeUnwrapDefault(mod) {
    // console.log("fakeUnwrapDefault", mod)
    return mod.default;
}
/** Typescript thinks import('...ts') doesn't need mod.default.default, but does */
function actualUnwrapDefault(mod) {
    // console.log("actualUnwrapDefault", mod)
    const maybeUnwrap = mod.default;
    return maybeUnwrap ?? mod;
}
// I'm not sure if this behavior is needed in all runtimes,
// or just for mocha + ts-node.
exports.unwrapTypescript = actualUnwrapDefault;
exports.unwrapJavascript = fakeUnwrapDefault;
//# sourceMappingURL=esmHelpers.js.map