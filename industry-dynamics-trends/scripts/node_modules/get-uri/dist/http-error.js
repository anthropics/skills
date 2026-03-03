"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
const http_1 = require("http");
/**
 * Error subclass to use when an HTTP application error has occurred.
 */
class HTTPError extends Error {
    constructor(statusCode, message = http_1.STATUS_CODES[statusCode]) {
        super(message);
        this.statusCode = statusCode;
        this.code = `E${String(message).toUpperCase().replace(/\s+/g, '')}`;
    }
}
exports.default = HTTPError;
//# sourceMappingURL=http-error.js.map