import { Socket } from "net";
import { ConnectionOptions as TLSConnectionOptions, TLSSocket } from "tls";
import { StringEncoding } from "./StringEncoding";
interface Task {
    /** Handles a response for a task. */
    readonly responseHandler: ResponseHandler;
    /** Resolves or rejects a task. */
    readonly resolver: TaskResolver;
    /** Call stack when task was run. */
    readonly stack: string;
}
export interface TaskResolver {
    resolve(args: any): void;
    reject(err: Error): void;
}
export interface FTPResponse {
    /** FTP response code */
    readonly code: number;
    /** Whole response including response code */
    readonly message: string;
}
export type ResponseHandler = (response: Error | FTPResponse, task: TaskResolver) => void;
/**
 * Describes an FTP server error response including the FTP response code.
 */
export declare class FTPError extends Error {
    /** FTP response code */
    readonly code: number;
    constructor(res: FTPResponse);
}
/**
 * FTPContext holds the control and data sockets of an FTP connection and provides a
 * simplified way to interact with an FTP server, handle responses, errors and timeouts.
 *
 * It doesn't implement or use any FTP commands. It's only a foundation to make writing an FTP
 * client as easy as possible. You won't usually instantiate this, but use `Client`.
 */
export declare class FTPContext {
    readonly timeout: number;
    /** Debug-level logging of all socket communication. */
    verbose: boolean;
    /** IP version to prefer (4: IPv4, 6: IPv6, undefined: automatic). */
    ipFamily: number | undefined;
    /** Options for TLS connections. */
    tlsOptions: TLSConnectionOptions;
    /** Current task to be resolved or rejected. */
    protected _task: Task | undefined;
    /** A multiline response might be received as multiple chunks. */
    protected _partialResponse: string;
    /** The reason why a context has been closed. */
    protected _closingError: NodeJS.ErrnoException | undefined;
    /** Encoding supported by Node applied to commands, responses and directory listing data. */
    protected _encoding: StringEncoding;
    /** FTP control connection */
    protected _socket: Socket | TLSSocket;
    /** FTP data connection */
    protected _dataSocket: Socket | TLSSocket | undefined;
    /**
     * Instantiate an FTP context.
     *
     * @param timeout - Timeout in milliseconds to apply to control and data connections. Use 0 for no timeout.
     * @param encoding - Encoding to use for control connection. UTF-8 by default. Use "latin1" for older servers.
     */
    constructor(timeout?: number, encoding?: StringEncoding);
    /**
     * Close the context.
     */
    close(): void;
    /**
     * Close the context with an error.
     */
    closeWithError(err: Error): void;
    /**
     * Returns true if this context has been closed or hasn't been connected yet. You can reopen it with `access`.
     */
    get closed(): boolean;
    /**
     * Reset this contex and all of its state.
     */
    reset(): void;
    /**
     * Get the FTP control socket.
     */
    get socket(): Socket | TLSSocket;
    /**
     * Set the socket for the control connection. This will only close the current control socket
     * if the new one is not an upgrade to the current one.
     */
    set socket(socket: Socket | TLSSocket);
    /**
     * Get the current FTP data connection if present.
     */
    get dataSocket(): Socket | TLSSocket | undefined;
    /**
     * Set the socket for the data connection. This will automatically close the former data socket.
     */
    set dataSocket(socket: Socket | TLSSocket | undefined);
    /**
     * Get the currently used encoding.
     */
    get encoding(): StringEncoding;
    /**
     * Set the encoding used for the control socket.
     *
     * See https://nodejs.org/api/buffer.html#buffer_buffers_and_character_encodings for what encodings
     * are supported by Node.
     */
    set encoding(encoding: StringEncoding);
    /**
     * Send an FTP command without waiting for or handling the result.
     */
    send(command: string): void;
    /**
     * Send an FTP command and handle the first response. Use this if you have a simple
     * request-response situation.
     */
    request(command: string): Promise<FTPResponse>;
    /**
     * Send an FTP command and handle any response until you resolve/reject. Use this if you expect multiple responses
     * to a request. This returns a Promise that will hold whatever the response handler passed on when resolving/rejecting its task.
     */
    handle(command: string | undefined, responseHandler: ResponseHandler): Promise<any>;
    /**
     * Log message if set to be verbose.
     */
    log(message: string): void;
    /**
     * Return true if the control socket is using TLS. This does not mean that a session
     * has already been negotiated.
     */
    get hasTLS(): boolean;
    /**
     * Removes reference to current task and handler. This won't resolve or reject the task.
     * @protected
     */
    protected _stopTrackingTask(): void;
    /**
     * Handle incoming data on the control socket. The chunk is going to be of type `string`
     * because we let `socket` handle encoding with `setEncoding`.
     * @protected
     */
    protected _onControlSocketData(chunk: string): void;
    /**
     * Send the current handler a response. This is usually a control socket response
     * or a socket event, like an error or timeout.
     * @protected
     */
    protected _passToHandler(response: Error | FTPResponse): void;
    /**
     * Setup all error handlers for a socket.
     * @protected
     */
    protected _setupDefaultErrorHandlers(socket: Socket, identifier: string): void;
    /**
     * Close the control socket. Sends QUIT, then FIN, and ignores any response or error.
     */
    protected _closeControlSocket(): void;
    /**
     * Close a socket, ignores any error.
     * @protected
     */
    protected _closeSocket(socket: Socket | undefined): void;
    /**
     * Remove all default listeners for socket.
     * @protected
     */
    protected _removeSocketListeners(socket: Socket): void;
    /**
     * Provide a new socket instance.
     *
     * Internal use only, replaced for unit tests.
     */
    _newSocket(): Socket;
}
export {};
