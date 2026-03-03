/**
 * Error subclass to use when the source has not been modified.
 *
 * @param {String} message optional "message" property to set
 * @api protected
 */
export default class NotModifiedError extends Error {
    code: string;
    constructor(message?: string);
}
