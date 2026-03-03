/**
 * @deprecated The `node:constants` module is deprecated. When requiring access to constants
 * relevant to specific Node.js builtin modules, developers should instead refer
 * to the `constants` property exposed by the relevant module. For instance,
 * `require('node:fs').constants` and `require('node:os').constants`.
 */
declare module "node:constants" {
    const constants:
        & typeof import("node:os").constants.dlopen
        & typeof import("node:os").constants.errno
        & typeof import("node:os").constants.priority
        & typeof import("node:os").constants.signals
        & typeof import("node:fs").constants
        & typeof import("node:crypto").constants;
    export = constants;
}
declare module "constants" {
    import constants = require("node:constants");
    export = constants;
}
