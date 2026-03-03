import { Readable, Writable } from "stream";
import { ConnectionOptions as TLSConnectionOptions } from "tls";
import { FileInfo } from "./FileInfo";
import { FTPContext, FTPResponse } from "./FtpContext";
import { ProgressHandler, ProgressTracker } from "./ProgressTracker";
import { UploadCommand } from "./transfer";
export interface AccessOptions {
    /** Host the client should connect to. Optional, default is "localhost". */
    readonly host?: string;
    /** Port the client should connect to. Optional, default is 21. */
    readonly port?: number;
    /** Username to use for login. Optional, default is "anonymous". */
    readonly user?: string;
    /** Password to use for login. Optional, default is "guest". */
    readonly password?: string;
    /** Use FTPS over TLS. Optional, default is false. True is preferred explicit TLS, "implicit" supports legacy, non-standardized implicit TLS. */
    readonly secure?: boolean | "implicit";
    /** TLS options as in [tls.connect(options)](https://nodejs.org/api/tls.html#tls_tls_connect_options_callback), optional. */
    readonly secureOptions?: TLSConnectionOptions;
}
/** Prepares a data connection for transfer. */
export type TransferStrategy = (ftp: FTPContext) => Promise<FTPResponse>;
/** Parses raw directoy listing data. */
export type RawListParser = (rawList: string) => FileInfo[];
export interface UploadOptions {
    /** Offset in the local file to start uploading from. */
    localStart?: number;
    /** Final byte position to include in upload from the local file. */
    localEndInclusive?: number;
}
export interface ClientOptions {
    allowSeparateTransferHost: boolean;
}
/**
 * High-level API to interact with an FTP server.
 */
export declare class Client {
    prepareTransfer: TransferStrategy;
    parseList: RawListParser;
    availableListCommands: string[];
    /** Low-level API to interact with FTP server. */
    readonly ftp: FTPContext;
    /** Tracks progress of data transfers. */
    protected _progressTracker: ProgressTracker;
    /**
     * Instantiate an FTP client.
     *
     * @param timeout  Timeout in milliseconds, use 0 for no timeout. Optional, default is 30 seconds.
     */
    constructor(timeout?: number, options?: ClientOptions);
    /**
     * Close the client and all open socket connections.
     *
     * Close the client and all open socket connections. The client can’t be used anymore after calling this method,
     * you have to either reconnect with `access` or `connect` or instantiate a new instance to continue any work.
     * A client is also closed automatically if any timeout or connection error occurs.
     */
    close(): void;
    /**
     * Returns true if the client is closed and can't be used anymore.
     */
    get closed(): boolean;
    /**
     * Connect (or reconnect) to an FTP server.
     *
     * This is an instance method and thus can be called multiple times during the lifecycle of a `Client`
     * instance. Whenever you do, the client is reset with a new control connection. This also implies that
     * you can reopen a `Client` instance that has been closed due to an error when reconnecting with this
     * method. In fact, reconnecting is the only way to continue using a closed `Client`.
     *
     * @param host  Host the client should connect to. Optional, default is "localhost".
     * @param port  Port the client should connect to. Optional, default is 21.
     */
    connect(host?: string, port?: number): Promise<FTPResponse>;
    /**
     * As `connect` but using implicit TLS. Implicit TLS is not an FTP standard and has been replaced by
     * explicit TLS. There are still FTP servers that support only implicit TLS, though.
     */
    connectImplicitTLS(host?: string, port?: number, tlsOptions?: TLSConnectionOptions): Promise<FTPResponse>;
    /**
     * Handles the first reponse by an FTP server after the socket connection has been established.
     */
    private _handleConnectResponse;
    /**
     * Send an FTP command and handle the first response.
     */
    send(command: string, ignoreErrorCodesDEPRECATED?: boolean): Promise<FTPResponse>;
    /**
     * Send an FTP command and ignore an FTP error response. Any other kind of error or timeout will still reject the Promise.
     *
     * @param command
     */
    sendIgnoringError(command: string): Promise<FTPResponse>;
    /**
     * Upgrade the current socket connection to TLS.
     *
     * @param options  TLS options as in `tls.connect(options)`, optional.
     * @param command  Set the authentication command. Optional, default is "AUTH TLS".
     */
    useTLS(options?: TLSConnectionOptions, command?: string): Promise<FTPResponse>;
    /**
     * Login a user with a password.
     *
     * @param user  Username to use for login. Optional, default is "anonymous".
     * @param password  Password to use for login. Optional, default is "guest".
     */
    login(user?: string, password?: string): Promise<FTPResponse>;
    /**
     * Set the usual default settings.
     *
     * Settings used:
     * * Binary mode (TYPE I)
     * * File structure (STRU F)
     * * Additional settings for FTPS (PBSZ 0, PROT P)
     */
    useDefaultSettings(): Promise<void>;
    /**
     * Convenience method that calls `connect`, `useTLS`, `login` and `useDefaultSettings`.
     *
     * This is an instance method and thus can be called multiple times during the lifecycle of a `Client`
     * instance. Whenever you do, the client is reset with a new control connection. This also implies that
     * you can reopen a `Client` instance that has been closed due to an error when reconnecting with this
     * method. In fact, reconnecting is the only way to continue using a closed `Client`.
     */
    access(options?: AccessOptions): Promise<FTPResponse>;
    /**
     * Get the current working directory.
     */
    pwd(): Promise<string>;
    /**
     * Get a description of supported features.
     *
     * This sends the FEAT command and parses the result into a Map where keys correspond to available commands
     * and values hold further information. Be aware that your FTP servers might not support this
     * command in which case this method will not throw an exception but just return an empty Map.
     */
    features(): Promise<Map<string, string>>;
    /**
     * Set the working directory.
     */
    cd(path: string): Promise<FTPResponse>;
    /**
     * Switch to the parent directory of the working directory.
     */
    cdup(): Promise<FTPResponse>;
    /**
     * Get the last modified time of a file. This is not supported by every FTP server, in which case
     * calling this method will throw an exception.
     */
    lastMod(path: string): Promise<Date>;
    /**
     * Get the size of a file.
     */
    size(path: string): Promise<number>;
    /**
     * Rename a file.
     *
     * Depending on the FTP server this might also be used to move a file from one
     * directory to another by providing full paths.
     */
    rename(srcPath: string, destPath: string): Promise<FTPResponse>;
    /**
     * Remove a file from the current working directory.
     *
     * You can ignore FTP error return codes which won't throw an exception if e.g.
     * the file doesn't exist.
     */
    remove(path: string, ignoreErrorCodes?: boolean): Promise<FTPResponse>;
    /**
     * Report transfer progress for any upload or download to a given handler.
     *
     * This will also reset the overall transfer counter that can be used for multiple transfers. You can
     * also call the function without a handler to stop reporting to an earlier one.
     *
     * @param handler  Handler function to call on transfer progress.
     */
    trackProgress(handler?: ProgressHandler): void;
    /**
     * Upload data from a readable stream or a local file to a remote file.
     *
     * @param source  Readable stream or path to a local file.
     * @param toRemotePath  Path to a remote file to write to.
     */
    uploadFrom(source: Readable | string, toRemotePath: string, options?: UploadOptions): Promise<FTPResponse>;
    /**
     * Upload data from a readable stream or a local file by appending it to an existing file. If the file doesn't
     * exist the FTP server should create it.
     *
     * @param source  Readable stream or path to a local file.
     * @param toRemotePath  Path to a remote file to write to.
     */
    appendFrom(source: Readable | string, toRemotePath: string, options?: UploadOptions): Promise<FTPResponse>;
    /**
     * @protected
     */
    protected _uploadWithCommand(source: Readable | string, remotePath: string, command: UploadCommand, options: UploadOptions): Promise<FTPResponse>;
    /**
     * @protected
     */
    protected _uploadLocalFile(localPath: string, remotePath: string, command: UploadCommand, options: UploadOptions): Promise<FTPResponse>;
    /**
     * @protected
     */
    protected _uploadFromStream(source: Readable, remotePath: string, command: UploadCommand): Promise<FTPResponse>;
    /**
     * Download a remote file and pipe its data to a writable stream or to a local file.
     *
     * You can optionally define at which position of the remote file you'd like to start
     * downloading. If the destination you provide is a file, the offset will be applied
     * to it as well. For example: To resume a failed download, you'd request the size of
     * the local, partially downloaded file and use that as the offset. Assuming the size
     * is 23, you'd download the rest using `downloadTo("local.txt", "remote.txt", 23)`.
     *
     * @param destination  Stream or path for a local file to write to.
     * @param fromRemotePath  Path of the remote file to read from.
     * @param startAt  Position within the remote file to start downloading at. If the destination is a file, this offset is also applied to it.
     */
    downloadTo(destination: Writable | string, fromRemotePath: string, startAt?: number): Promise<FTPResponse>;
    /**
     * @protected
     */
    protected _downloadToFile(localPath: string, remotePath: string, startAt: number): Promise<FTPResponse>;
    /**
     * @protected
     */
    protected _downloadToStream(destination: Writable, remotePath: string, startAt: number): Promise<FTPResponse>;
    /**
     * List files and directories in the current working directory, or from `path` if specified.
     *
     * @param [path]  Path to remote file or directory.
     */
    list(path?: string): Promise<FileInfo[]>;
    /**
     * @protected
     */
    protected _requestListWithCommand(command: string): Promise<FileInfo[]>;
    /**
     * Remove a directory and all of its content.
     *
     * @param remoteDirPath  The path of the remote directory to delete.
     * @example client.removeDir("foo") // Remove directory 'foo' using a relative path.
     * @example client.removeDir("foo/bar") // Remove directory 'bar' using a relative path.
     * @example client.removeDir("/foo/bar") // Remove directory 'bar' using an absolute path.
     * @example client.removeDir("/") // Remove everything.
     */
    removeDir(remoteDirPath: string): Promise<void>;
    /**
     * Remove all files and directories in the working directory without removing
     * the working directory itself.
     */
    clearWorkingDir(): Promise<void>;
    /**
     * Upload the contents of a local directory to the remote working directory.
     *
     * This will overwrite existing files with the same names and reuse existing directories.
     * Unrelated files and directories will remain untouched. You can optionally provide a `remoteDirPath`
     * to put the contents inside a directory which will be created if necessary including all
     * intermediate directories. If you did provide a remoteDirPath the working directory will stay
     * the same as before calling this method.
     *
     * @param localDirPath  Local path, e.g. "foo/bar" or "../test"
     * @param [remoteDirPath]  Remote path of a directory to upload to. Working directory if undefined.
     */
    uploadFromDir(localDirPath: string, remoteDirPath?: string): Promise<void>;
    /**
     * @protected
     */
    protected _uploadToWorkingDir(localDirPath: string): Promise<void>;
    /**
     * Download all files and directories of the working directory to a local directory.
     *
     * @param localDirPath  The local directory to download to.
     * @param remoteDirPath  Remote directory to download. Current working directory if not specified.
     */
    downloadToDir(localDirPath: string, remoteDirPath?: string): Promise<void>;
    /**
     * @protected
     */
    protected _downloadFromWorkingDir(localDirPath: string): Promise<void>;
    /**
     * Make sure a given remote path exists, creating all directories as necessary.
     * This function also changes the current working directory to the given path.
     */
    ensureDir(remoteDirPath: string): Promise<void>;
    /**
     * Try to create a directory and enter it. This will not raise an exception if the directory
     * couldn't be created if for example it already exists.
     * @protected
     */
    protected _openDir(dirName: string): Promise<void>;
    /**
     * Remove an empty directory, will fail if not empty.
     */
    removeEmptyDir(path: string): Promise<FTPResponse>;
    /**
     * FTP servers can't handle filenames that have leading whitespace. This method transforms
     * a given path to fix that issue for most cases.
     */
    protectWhitespace(path: string): Promise<string>;
    protected _exitAtCurrentDirectory<T>(func: () => Promise<T>): Promise<T>;
    /**
     * Try all available transfer strategies and pick the first one that works. Update `client` to
     * use the working strategy for all successive transfer requests.
     *
     * @returns a function that will try the provided strategies.
     */
    protected _enterFirstCompatibleMode(strategies: TransferStrategy[]): TransferStrategy;
    /**
     * DEPRECATED, use `uploadFrom`.
     * @deprecated
     */
    upload(source: Readable | string, toRemotePath: string, options?: UploadOptions): Promise<FTPResponse>;
    /**
     * DEPRECATED, use `appendFrom`.
     * @deprecated
     */
    append(source: Readable | string, toRemotePath: string, options?: UploadOptions): Promise<FTPResponse>;
    /**
     * DEPRECATED, use `downloadTo`.
     * @deprecated
     */
    download(destination: Writable | string, fromRemotePath: string, startAt?: number): Promise<FTPResponse>;
    /**
     * DEPRECATED, use `uploadFromDir`.
     * @deprecated
     */
    uploadDir(localDirPath: string, remoteDirPath?: string): Promise<void>;
    /**
     * DEPRECATED, use `downloadToDir`.
     * @deprecated
     */
    downloadDir(localDirPath: string): Promise<void>;
}
