/**
 * Error subclass to use when an HTTP application error has occurred.
 */
export default class HTTPError extends Error {
    code: string;
    statusCode: number;
    constructor(statusCode: number, message?: string | undefined);
}
