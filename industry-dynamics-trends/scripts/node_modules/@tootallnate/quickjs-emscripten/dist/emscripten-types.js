"use strict";
// This is a subset of the Emscripten type definitions from @types/emscripten
// Project: http://kripken.github.io/emscripten-site/index.html
// Definitions by: Kensuke Matsuzaki <https://github.com/zakki>
//                 Periklis Tsirakidis <https://github.com/periklis>
// Definitions: https://github.com/DefinitelyTyped/DefinitelyTyped
//
// quickjs-emscripten doesn't use the full EmscriptenModule type from @types/emscripten because:
//
// - the upstream types define many properties that don't exist on our module due
//   to our build settings
// - some upstream types reference web-only ambient types like WebGL stuff, which
//   we don't use.
Object.defineProperty(exports, "__esModule", { value: true });
//# sourceMappingURL=emscripten-types.js.map