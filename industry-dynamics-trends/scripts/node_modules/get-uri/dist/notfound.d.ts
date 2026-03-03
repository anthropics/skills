/**
 * Error subclass to use when the source does not exist at the specified endpoint.
 *
 * @param {String} message optional "message" property to set
 * @api protected
 */
export default class NotFoundError extends Error {
    code: string;
    constructor(message?: string);
}
