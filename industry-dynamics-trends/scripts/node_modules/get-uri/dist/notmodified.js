"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
/**
 * Error subclass to use when the source has not been modified.
 *
 * @param {String} message optional "message" property to set
 * @api protected
 */
class NotModifiedError extends Error {
    constructor(message) {
        super(message ||
            'Source has not been modified since the provied "cache", re-use previous results');
        this.code = 'ENOTMODIFIED';
    }
}
exports.default = NotModifiedError;
//# sourceMappingURL=notmodified.js.map