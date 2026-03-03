"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.Client = void 0;
const fs_1 = require("fs");
const path_1 = require("path");
const tls_1 = require("tls");
const util_1 = require("util");
const FtpContext_1 = require("./FtpContext");
const parseList_1 = require("./parseList");
const ProgressTracker_1 = require("./ProgressTracker");
const StringWriter_1 = require("./StringWriter");
const parseListMLSD_1 = require("./parseListMLSD");
const netUtils_1 = require("./netUtils");
const transfer_1 = require("./transfer");
const parseControlResponse_1 = require("./parseControlResponse");
// Use promisify to keep the library compatible with Node 8.
const fsReadDir = (0, util_1.promisify)(fs_1.readdir);
const fsMkDir = (0, util_1.promisify)(fs_1.mkdir);
const fsStat = (0, util_1.promisify)(fs_1.stat);
const fsOpen = (0, util_1.promisify)(fs_1.open);
const fsClose = (0, util_1.promisify)(fs_1.close);
const fsUnlink = (0, util_1.promisify)(fs_1.unlink);
const defaultClientOptions = {
    allowSeparateTransferHost: true
};
const LIST_COMMANDS_DEFAULT = () => ["LIST -a", "LIST"];
const LIST_COMMANDS_MLSD = () => ["MLSD", "LIST -a", "LIST"];
/**
 * High-level API to interact with an FTP server.
 */
class Client {
    /**
     * Instantiate an FTP client.
     *
     * @param timeout  Timeout in milliseconds, use 0 for no timeout. Optional, default is 30 seconds.
     */
    constructor(timeout = 30000, options = defaultClientOptions) {
        this.availableListCommands = LIST_COMMANDS_DEFAULT();
        this.ftp = new FtpContext_1.FTPContext(timeout);
        this.prepareTransfer = this._enterFirstCompatibleMode([
            transfer_1.enterPassiveModeIPv6,
            options.allowSeparateTransferHost ? transfer_1.enterPassiveModeIPv4 : transfer_1.enterPassiveModeIPv4_forceControlHostIP
        ]);
        this.parseList = parseList_1.parseList;
        this._progressTracker = new ProgressTracker_1.ProgressTracker();
    }
    /**
     * Close the client and all open socket connections.
     *
     * Close the client and all open socket connections. The client can’t be used anymore after calling this method,
     * you have to either reconnect with `access` or `connect` or instantiate a new instance to continue any work.
     * A client is also closed automatically if any timeout or connection error occurs.
     */
    close() {
        this.ftp.close();
        this._progressTracker.stop();
    }
    /**
     * Returns true if the client is closed and can't be used anymore.
     */
    get closed() {
        return this.ftp.closed;
    }
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
    connect(host = "localhost", port = 21) {
        this.ftp.reset();
        this.ftp.socket.connect({
            host,
            port,
            family: this.ftp.ipFamily
        }, () => this.ftp.log(`Connected to ${(0, netUtils_1.describeAddress)(this.ftp.socket)} (${(0, netUtils_1.describeTLS)(this.ftp.socket)})`));
        return this._handleConnectResponse();
    }
    /**
     * As `connect` but using implicit TLS. Implicit TLS is not an FTP standard and has been replaced by
     * explicit TLS. There are still FTP servers that support only implicit TLS, though.
     */
    connectImplicitTLS(host = "localhost", port = 21, tlsOptions = {}) {
        this.ftp.reset();
        this.ftp.socket = (0, tls_1.connect)(port, host, tlsOptions, () => this.ftp.log(`Connected to ${(0, netUtils_1.describeAddress)(this.ftp.socket)} (${(0, netUtils_1.describeTLS)(this.ftp.socket)})`));
        this.ftp.tlsOptions = tlsOptions;
        return this._handleConnectResponse();
    }
    /**
     * Handles the first reponse by an FTP server after the socket connection has been established.
     */
    _handleConnectResponse() {
        return this.ftp.handle(undefined, (res, task) => {
            if (res instanceof Error) {
                // The connection has been destroyed by the FTPContext at this point.
                task.reject(res);
            }
            else if ((0, parseControlResponse_1.positiveCompletion)(res.code)) {
                task.resolve(res);
            }
            // Reject all other codes, including 120 "Service ready in nnn minutes".
            else {
                // Don't stay connected but don't replace the socket yet by using reset()
                // so the user can inspect properties of this instance.
                task.reject(new FtpContext_1.FTPError(res));
            }
        });
    }
    /**
     * Send an FTP command and handle the first response.
     */
    send(command, ignoreErrorCodesDEPRECATED = false) {
        if (ignoreErrorCodesDEPRECATED) { // Deprecated starting from 3.9.0
            this.ftp.log("Deprecated call using send(command, flag) with boolean flag to ignore errors. Use sendIgnoringError(command).");
            return this.sendIgnoringError(command);
        }
        return this.ftp.request(command);
    }
    /**
     * Send an FTP command and ignore an FTP error response. Any other kind of error or timeout will still reject the Promise.
     *
     * @param command
     */
    sendIgnoringError(command) {
        return this.ftp.handle(command, (res, task) => {
            if (res instanceof FtpContext_1.FTPError) {
                task.resolve({ code: res.code, message: res.message });
            }
            else if (res instanceof Error) {
                task.reject(res);
            }
            else {
                task.resolve(res);
            }
        });
    }
    /**
     * Upgrade the current socket connection to TLS.
     *
     * @param options  TLS options as in `tls.connect(options)`, optional.
     * @param command  Set the authentication command. Optional, default is "AUTH TLS".
     */
    async useTLS(options = {}, command = "AUTH TLS") {
        const ret = await this.send(command);
        this.ftp.socket = await (0, netUtils_1.upgradeSocket)(this.ftp.socket, options);
        this.ftp.tlsOptions = options; // Keep the TLS options for later data connections that should use the same options.
        this.ftp.log(`Control socket is using: ${(0, netUtils_1.describeTLS)(this.ftp.socket)}`);
        return ret;
    }
    /**
     * Login a user with a password.
     *
     * @param user  Username to use for login. Optional, default is "anonymous".
     * @param password  Password to use for login. Optional, default is "guest".
     */
    login(user = "anonymous", password = "guest") {
        this.ftp.log(`Login security: ${(0, netUtils_1.describeTLS)(this.ftp.socket)}`);
        return this.ftp.handle("USER " + user, (res, task) => {
            if (res instanceof Error) {
                task.reject(res);
            }
            else if ((0, parseControlResponse_1.positiveCompletion)(res.code)) { // User logged in proceed OR Command superfluous
                task.resolve(res);
            }
            else if (res.code === 331) { // User name okay, need password
                this.ftp.send("PASS " + password);
            }
            else { // Also report error on 332 (Need account)
                task.reject(new FtpContext_1.FTPError(res));
            }
        });
    }
    /**
     * Set the usual default settings.
     *
     * Settings used:
     * * Binary mode (TYPE I)
     * * File structure (STRU F)
     * * Additional settings for FTPS (PBSZ 0, PROT P)
     */
    async useDefaultSettings() {
        const features = await this.features();
        // Use MLSD directory listing if possible. See https://tools.ietf.org/html/rfc3659#section-7.8:
        // "The presence of the MLST feature indicates that both MLST and MLSD are supported."
        const supportsMLSD = features.has("MLST");
        this.availableListCommands = supportsMLSD ? LIST_COMMANDS_MLSD() : LIST_COMMANDS_DEFAULT();
        await this.send("TYPE I"); // Binary mode
        await this.sendIgnoringError("STRU F"); // Use file structure
        await this.sendIgnoringError("OPTS UTF8 ON"); // Some servers expect UTF-8 to be enabled explicitly and setting before login might not have worked.
        if (supportsMLSD) {
            await this.sendIgnoringError("OPTS MLST type;size;modify;unique;unix.mode;unix.owner;unix.group;unix.ownername;unix.groupname;"); // Make sure MLSD listings include all we can parse
        }
        if (this.ftp.hasTLS) {
            await this.sendIgnoringError("PBSZ 0"); // Set to 0 for TLS
            await this.sendIgnoringError("PROT P"); // Protect channel (also for data connections)
        }
    }
    /**
     * Convenience method that calls `connect`, `useTLS`, `login` and `useDefaultSettings`.
     *
     * This is an instance method and thus can be called multiple times during the lifecycle of a `Client`
     * instance. Whenever you do, the client is reset with a new control connection. This also implies that
     * you can reopen a `Client` instance that has been closed due to an error when reconnecting with this
     * method. In fact, reconnecting is the only way to continue using a closed `Client`.
     */
    async access(options = {}) {
        var _a, _b;
        const useExplicitTLS = options.secure === true;
        const useImplicitTLS = options.secure === "implicit";
        let welcome;
        if (useImplicitTLS) {
            welcome = await this.connectImplicitTLS(options.host, options.port, options.secureOptions);
        }
        else {
            welcome = await this.connect(options.host, options.port);
        }
        if (useExplicitTLS) {
            // Fixes https://github.com/patrickjuchli/basic-ftp/issues/166 by making sure
            // host is set for any future data connection as well.
            const secureOptions = (_a = options.secureOptions) !== null && _a !== void 0 ? _a : {};
            secureOptions.host = (_b = secureOptions.host) !== null && _b !== void 0 ? _b : options.host;
            await this.useTLS(secureOptions);
        }
        // Set UTF-8 on before login in case there are non-ascii characters in user or password.
        // Note that this might not work before login depending on server.
        await this.sendIgnoringError("OPTS UTF8 ON");
        await this.login(options.user, options.password);
        await this.useDefaultSettings();
        return welcome;
    }
    /**
     * Get the current working directory.
     */
    async pwd() {
        const res = await this.send("PWD");
        // The directory is part of the return message, for example:
        // 257 "/this/that" is current directory.
        const parsed = res.message.match(/"(.+)"/);
        if (parsed === null || parsed[1] === undefined) {
            throw new Error(`Can't parse response to command 'PWD': ${res.message}`);
        }
        return parsed[1];
    }
    /**
     * Get a description of supported features.
     *
     * This sends the FEAT command and parses the result into a Map where keys correspond to available commands
     * and values hold further information. Be aware that your FTP servers might not support this
     * command in which case this method will not throw an exception but just return an empty Map.
     */
    async features() {
        const res = await this.sendIgnoringError("FEAT");
        const features = new Map();
        // Not supporting any special features will be reported with a single line.
        if (res.code < 400 && (0, parseControlResponse_1.isMultiline)(res.message)) {
            // The first and last line wrap the multiline response, ignore them.
            res.message.split("\n").slice(1, -1).forEach(line => {
                // A typical lines looks like: " REST STREAM" or " MDTM".
                // Servers might not use an indentation though.
                const entry = line.trim().split(" ");
                features.set(entry[0], entry[1] || "");
            });
        }
        return features;
    }
    /**
     * Set the working directory.
     */
    async cd(path) {
        const validPath = await this.protectWhitespace(path);
        return this.send("CWD " + validPath);
    }
    /**
     * Switch to the parent directory of the working directory.
     */
    async cdup() {
        return this.send("CDUP");
    }
    /**
     * Get the last modified time of a file. This is not supported by every FTP server, in which case
     * calling this method will throw an exception.
     */
    async lastMod(path) {
        const validPath = await this.protectWhitespace(path);
        const res = await this.send(`MDTM ${validPath}`);
        const date = res.message.slice(4);
        return (0, parseListMLSD_1.parseMLSxDate)(date);
    }
    /**
     * Get the size of a file.
     */
    async size(path) {
        const validPath = await this.protectWhitespace(path);
        const command = `SIZE ${validPath}`;
        const res = await this.send(command);
        // The size is part of the response message, for example: "213 555555". It's
        // possible that there is a commmentary appended like "213 5555, some commentary".
        const size = parseInt(res.message.slice(4), 10);
        if (Number.isNaN(size)) {
            throw new Error(`Can't parse response to command '${command}' as a numerical value: ${res.message}`);
        }
        return size;
    }
    /**
     * Rename a file.
     *
     * Depending on the FTP server this might also be used to move a file from one
     * directory to another by providing full paths.
     */
    async rename(srcPath, destPath) {
        const validSrc = await this.protectWhitespace(srcPath);
        const validDest = await this.protectWhitespace(destPath);
        await this.send("RNFR " + validSrc);
        return this.send("RNTO " + validDest);
    }
    /**
     * Remove a file from the current working directory.
     *
     * You can ignore FTP error return codes which won't throw an exception if e.g.
     * the file doesn't exist.
     */
    async remove(path, ignoreErrorCodes = false) {
        const validPath = await this.protectWhitespace(path);
        if (ignoreErrorCodes) {
            return this.sendIgnoringError(`DELE ${validPath}`);
        }
        return this.send(`DELE ${validPath}`);
    }
    /**
     * Report transfer progress for any upload or download to a given handler.
     *
     * This will also reset the overall transfer counter that can be used for multiple transfers. You can
     * also call the function without a handler to stop reporting to an earlier one.
     *
     * @param handler  Handler function to call on transfer progress.
     */
    trackProgress(handler) {
        this._progressTracker.bytesOverall = 0;
        this._progressTracker.reportTo(handler);
    }
    /**
     * Upload data from a readable stream or a local file to a remote file.
     *
     * @param source  Readable stream or path to a local file.
     * @param toRemotePath  Path to a remote file to write to.
     */
    async uploadFrom(source, toRemotePath, options = {}) {
        return this._uploadWithCommand(source, toRemotePath, "STOR", options);
    }
    /**
     * Upload data from a readable stream or a local file by appending it to an existing file. If the file doesn't
     * exist the FTP server should create it.
     *
     * @param source  Readable stream or path to a local file.
     * @param toRemotePath  Path to a remote file to write to.
     */
    async appendFrom(source, toRemotePath, options = {}) {
        return this._uploadWithCommand(source, toRemotePath, "APPE", options);
    }
    /**
     * @protected
     */
    async _uploadWithCommand(source, remotePath, command, options) {
        if (typeof source === "string") {
            return this._uploadLocalFile(source, remotePath, command, options);
        }
        return this._uploadFromStream(source, remotePath, command);
    }
    /**
     * @protected
     */
    async _uploadLocalFile(localPath, remotePath, command, options) {
        const fd = await fsOpen(localPath, "r");
        const source = (0, fs_1.createReadStream)("", {
            fd,
            start: options.localStart,
            end: options.localEndInclusive,
            autoClose: false
        });
        try {
            return await this._uploadFromStream(source, remotePath, command);
        }
        finally {
            await ignoreError(() => fsClose(fd));
        }
    }
    /**
     * @protected
     */
    async _uploadFromStream(source, remotePath, command) {
        const onError = (err) => this.ftp.closeWithError(err);
        source.once("error", onError);
        try {
            const validPath = await this.protectWhitespace(remotePath);
            await this.prepareTransfer(this.ftp);
            // Keep the keyword `await` or the `finally` clause below runs too early
            // and removes the event listener for the source stream too early.
            return await (0, transfer_1.uploadFrom)(source, {
                ftp: this.ftp,
                tracker: this._progressTracker,
                command,
                remotePath: validPath,
                type: "upload"
            });
        }
        finally {
            source.removeListener("error", onError);
        }
    }
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
    async downloadTo(destination, fromRemotePath, startAt = 0) {
        if (typeof destination === "string") {
            return this._downloadToFile(destination, fromRemotePath, startAt);
        }
        return this._downloadToStream(destination, fromRemotePath, startAt);
    }
    /**
     * @protected
     */
    async _downloadToFile(localPath, remotePath, startAt) {
        const appendingToLocalFile = startAt > 0;
        const fileSystemFlags = appendingToLocalFile ? "r+" : "w";
        const fd = await fsOpen(localPath, fileSystemFlags);
        const destination = (0, fs_1.createWriteStream)("", {
            fd,
            start: startAt,
            autoClose: false
        });
        try {
            return await this._downloadToStream(destination, remotePath, startAt);
        }
        catch (err) {
            const localFileStats = await ignoreError(() => fsStat(localPath));
            const hasDownloadedData = localFileStats && localFileStats.size > 0;
            const shouldRemoveLocalFile = !appendingToLocalFile && !hasDownloadedData;
            if (shouldRemoveLocalFile) {
                await ignoreError(() => fsUnlink(localPath));
            }
            throw err;
        }
        finally {
            await ignoreError(() => fsClose(fd));
        }
    }
    /**
     * @protected
     */
    async _downloadToStream(destination, remotePath, startAt) {
        const onError = (err) => this.ftp.closeWithError(err);
        destination.once("error", onError);
        try {
            const validPath = await this.protectWhitespace(remotePath);
            await this.prepareTransfer(this.ftp);
            // Keep the keyword `await` or the `finally` clause below runs too early
            // and removes the event listener for the source stream too early.
            return await (0, transfer_1.downloadTo)(destination, {
                ftp: this.ftp,
                tracker: this._progressTracker,
                command: startAt > 0 ? `REST ${startAt}` : `RETR ${validPath}`,
                remotePath: validPath,
                type: "download"
            });
        }
        finally {
            destination.removeListener("error", onError);
            destination.end();
        }
    }
    /**
     * List files and directories in the current working directory, or from `path` if specified.
     *
     * @param [path]  Path to remote file or directory.
     */
    async list(path = "") {
        const validPath = await this.protectWhitespace(path);
        let lastError;
        for (const candidate of this.availableListCommands) {
            const command = validPath === "" ? candidate : `${candidate} ${validPath}`;
            await this.prepareTransfer(this.ftp);
            try {
                const parsedList = await this._requestListWithCommand(command);
                // Use successful candidate for all subsequent requests.
                this.availableListCommands = [candidate];
                return parsedList;
            }
            catch (err) {
                const shouldTryNext = err instanceof FtpContext_1.FTPError;
                if (!shouldTryNext) {
                    throw err;
                }
                lastError = err;
            }
        }
        throw lastError;
    }
    /**
     * @protected
     */
    async _requestListWithCommand(command) {
        const buffer = new StringWriter_1.StringWriter();
        await (0, transfer_1.downloadTo)(buffer, {
            ftp: this.ftp,
            tracker: this._progressTracker,
            command,
            remotePath: "",
            type: "list"
        });
        const text = buffer.getText(this.ftp.encoding);
        this.ftp.log(text);
        return this.parseList(text);
    }
    /**
     * Remove a directory and all of its content.
     *
     * @param remoteDirPath  The path of the remote directory to delete.
     * @example client.removeDir("foo") // Remove directory 'foo' using a relative path.
     * @example client.removeDir("foo/bar") // Remove directory 'bar' using a relative path.
     * @example client.removeDir("/foo/bar") // Remove directory 'bar' using an absolute path.
     * @example client.removeDir("/") // Remove everything.
     */
    async removeDir(remoteDirPath) {
        return this._exitAtCurrentDirectory(async () => {
            await this.cd(remoteDirPath);
            // Get the absolute path of the target because remoteDirPath might be a relative path, even `../` is possible.
            const absoluteDirPath = await this.pwd();
            await this.clearWorkingDir();
            const dirIsRoot = absoluteDirPath === "/";
            if (!dirIsRoot) {
                await this.cdup();
                await this.removeEmptyDir(absoluteDirPath);
            }
        });
    }
    /**
     * Remove all files and directories in the working directory without removing
     * the working directory itself.
     */
    async clearWorkingDir() {
        for (const file of await this.list()) {
            if (file.isDirectory) {
                await this.cd(file.name);
                await this.clearWorkingDir();
                await this.cdup();
                await this.removeEmptyDir(file.name);
            }
            else {
                await this.remove(file.name);
            }
        }
    }
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
    async uploadFromDir(localDirPath, remoteDirPath) {
        return this._exitAtCurrentDirectory(async () => {
            if (remoteDirPath) {
                await this.ensureDir(remoteDirPath);
            }
            return await this._uploadToWorkingDir(localDirPath);
        });
    }
    /**
     * @protected
     */
    async _uploadToWorkingDir(localDirPath) {
        const files = await fsReadDir(localDirPath);
        for (const file of files) {
            const fullPath = (0, path_1.join)(localDirPath, file);
            const stats = await fsStat(fullPath);
            if (stats.isFile()) {
                await this.uploadFrom(fullPath, file);
            }
            else if (stats.isDirectory()) {
                await this._openDir(file);
                await this._uploadToWorkingDir(fullPath);
                await this.cdup();
            }
        }
    }
    /**
     * Download all files and directories of the working directory to a local directory.
     *
     * @param localDirPath  The local directory to download to.
     * @param remoteDirPath  Remote directory to download. Current working directory if not specified.
     */
    async downloadToDir(localDirPath, remoteDirPath) {
        return this._exitAtCurrentDirectory(async () => {
            if (remoteDirPath) {
                await this.cd(remoteDirPath);
            }
            return await this._downloadFromWorkingDir(localDirPath);
        });
    }
    /**
     * @protected
     */
    async _downloadFromWorkingDir(localDirPath) {
        await ensureLocalDirectory(localDirPath);
        for (const file of await this.list()) {
            const hasInvalidName = !file.name || (0, path_1.basename)(file.name) !== file.name;
            if (hasInvalidName) {
                const safeName = JSON.stringify(file.name);
                this.ftp.log(`Invalid filename from server listing, will skip file. (${safeName})`);
                continue;
            }
            const localPath = (0, path_1.join)(localDirPath, file.name);
            if (file.isDirectory) {
                await this.cd(file.name);
                await this._downloadFromWorkingDir(localPath);
                await this.cdup();
            }
            else if (file.isFile) {
                await this.downloadTo(localPath, file.name);
            }
        }
    }
    /**
     * Make sure a given remote path exists, creating all directories as necessary.
     * This function also changes the current working directory to the given path.
     */
    async ensureDir(remoteDirPath) {
        // If the remoteDirPath was absolute go to root directory.
        if (remoteDirPath.startsWith("/")) {
            await this.cd("/");
        }
        const names = remoteDirPath.split("/").filter(name => name !== "");
        for (const name of names) {
            await this._openDir(name);
        }
    }
    /**
     * Try to create a directory and enter it. This will not raise an exception if the directory
     * couldn't be created if for example it already exists.
     * @protected
     */
    async _openDir(dirName) {
        await this.sendIgnoringError("MKD " + dirName);
        await this.cd(dirName);
    }
    /**
     * Remove an empty directory, will fail if not empty.
     */
    async removeEmptyDir(path) {
        const validPath = await this.protectWhitespace(path);
        return this.send(`RMD ${validPath}`);
    }
    /**
     * FTP servers can't handle filenames that have leading whitespace. This method transforms
     * a given path to fix that issue for most cases.
     */
    async protectWhitespace(path) {
        if (!path.startsWith(" ")) {
            return path;
        }
        // Handle leading whitespace by prepending the absolute path:
        // " test.txt" while being in the root directory becomes "/ test.txt".
        const pwd = await this.pwd();
        const absolutePathPrefix = pwd.endsWith("/") ? pwd : pwd + "/";
        return absolutePathPrefix + path;
    }
    async _exitAtCurrentDirectory(func) {
        const userDir = await this.pwd();
        try {
            return await func();
        }
        finally {
            if (!this.closed) {
                await ignoreError(() => this.cd(userDir));
            }
        }
    }
    /**
     * Try all available transfer strategies and pick the first one that works. Update `client` to
     * use the working strategy for all successive transfer requests.
     *
     * @returns a function that will try the provided strategies.
     */
    _enterFirstCompatibleMode(strategies) {
        return async (ftp) => {
            ftp.log("Trying to find optimal transfer strategy...");
            let lastError = undefined;
            for (const strategy of strategies) {
                try {
                    const res = await strategy(ftp);
                    ftp.log("Optimal transfer strategy found.");
                    this.prepareTransfer = strategy;
                    return res;
                }
                catch (err) {
                    // Try the next candidate no matter the exact error. It's possible that a server
                    // answered incorrectly to a strategy, for example a PASV answer to an EPSV.
                    lastError = err;
                }
            }
            throw new Error(`None of the available transfer strategies work. Last error response was '${lastError}'.`);
        };
    }
    /**
     * DEPRECATED, use `uploadFrom`.
     * @deprecated
     */
    async upload(source, toRemotePath, options = {}) {
        this.ftp.log("Warning: upload() has been deprecated, use uploadFrom().");
        return this.uploadFrom(source, toRemotePath, options);
    }
    /**
     * DEPRECATED, use `appendFrom`.
     * @deprecated
     */
    async append(source, toRemotePath, options = {}) {
        this.ftp.log("Warning: append() has been deprecated, use appendFrom().");
        return this.appendFrom(source, toRemotePath, options);
    }
    /**
     * DEPRECATED, use `downloadTo`.
     * @deprecated
     */
    async download(destination, fromRemotePath, startAt = 0) {
        this.ftp.log("Warning: download() has been deprecated, use downloadTo().");
        return this.downloadTo(destination, fromRemotePath, startAt);
    }
    /**
     * DEPRECATED, use `uploadFromDir`.
     * @deprecated
     */
    async uploadDir(localDirPath, remoteDirPath) {
        this.ftp.log("Warning: uploadDir() has been deprecated, use uploadFromDir().");
        return this.uploadFromDir(localDirPath, remoteDirPath);
    }
    /**
     * DEPRECATED, use `downloadToDir`.
     * @deprecated
     */
    async downloadDir(localDirPath) {
        this.ftp.log("Warning: downloadDir() has been deprecated, use downloadToDir().");
        return this.downloadToDir(localDirPath);
    }
}
exports.Client = Client;
async function ensureLocalDirectory(path) {
    try {
        await fsStat(path);
    }
    catch (_a) {
        await fsMkDir(path, { recursive: true });
    }
}
async function ignoreError(func) {
    try {
        return await func();
    }
    catch (_a) {
        // Ignore
        return undefined;
    }
}
