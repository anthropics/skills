"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.isFail = exports.isSuccess = void 0;
function isSuccess(successOrFail) {
    return "error" in successOrFail === false;
}
exports.isSuccess = isSuccess;
function isFail(successOrFail) {
    return "error" in successOrFail === true;
}
exports.isFail = isFail;
//# sourceMappingURL=vm-interface.js.map