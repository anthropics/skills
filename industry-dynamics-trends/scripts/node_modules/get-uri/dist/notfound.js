"use strict";
/**
 * Error subclass to use when the source does not exist at the specified endpoint.
 *
 * @param {String} message optional "message" property to set
 * @api protected
 */
Object.defineProperty(exports, "__esModule", { value: true });
class NotFoundError extends Error {
    constructor(message) {
        super(message || 'File does not exist at the specified endpoint');
        this.code = 'ENOTFOUND';
    }
}
exports.default = NotFoundError;
//# sourceMappingURL=notfound.js.map