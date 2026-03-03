"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.enterPassiveModeIPv6 = enterPassiveModeIPv6;
exports.parseEpsvResponse = parseEpsvResponse;
exports.enterPassiveModeIPv4 = enterPassiveModeIPv4;
exports.enterPassiveModeIPv4_forceControlHostIP = enterPassiveModeIPv4_forceControlHostIP;
exports.parsePasvResponse = parsePasvResponse;
exports.connectForPassiveTransfer = connectForPassiveTransfer;
exports.uploadFrom = uploadFrom;
exports.downloadTo = downloadTo;
const netUtils_1 = require("./netUtils");
const stream_1 = require("stream");
const tls_1 = require("tls");
const parseControlResponse_1 = require("./parseControlResponse");
/**
 * Prepare a data socket using passive mode over IPv6.
 */
async function enterPassiveModeIPv6(ftp) {
    const res = await ftp.request("EPSV");
    const port = parseEpsvResponse(res.message);
    if (!port) {
        throw new Error("Can't parse EPSV response: " + res.message);
    }
    const controlHost = ftp.socket.remoteAddress;
    if (controlHost === undefined) {
        throw new Error("Control socket is disconnected, can't get remote address.");
    }
    await connectForPassiveTransfer(controlHost, port, ftp);
    return res;
}
/**
 * Parse an EPSV response. Returns only the port as in EPSV the host of the control connection is used.
 */
function parseEpsvResponse(message) {
    // Get port from EPSV response, e.g. "229 Entering Extended Passive Mode (|||6446|)"
    // Some FTP Servers such as the one on IBM i (OS/400) use ! instead of | in their EPSV response.
    const groups = message.match(/[|!]{3}(.+)[|!]/);
    if (groups === null || groups[1] === undefined) {
        throw new Error(`Can't parse response to 'EPSV': ${message}`);
    }
    const port = parseInt(groups[1], 10);
    if (Number.isNaN(port)) {
        throw new Error(`Can't parse response to 'EPSV', port is not a number: ${message}`);
    }
    return port;
}
/**
 * Prepare a data socket using passive mode over IPv4.
 */
async function enterPassiveModeIPv4(ftp) {
    const res = await ftp.request("PASV");
    const target = parsePasvResponse(res.message);
    if (!target) {
        throw new Error("Can't parse PASV response: " + res.message);
    }
    // If the host in the PASV response has a local address while the control connection hasn't,
    // we assume a NAT issue and use the IP of the control connection as the target for the data connection.
    // We can't always perform this replacement because it's possible (although unlikely) that the FTP server
    // indeed uses a different host for data connections.
    const controlHost = ftp.socket.remoteAddress;
    if ((0, netUtils_1.ipIsPrivateV4Address)(target.host) && controlHost && !(0, netUtils_1.ipIsPrivateV4Address)(controlHost)) {
        target.host = controlHost;
    }
    await connectForPassiveTransfer(target.host, target.port, ftp);
    return res;
}
/**
 * Prepare a data socket using passive mode over IPv4. Ignore the IP provided by the PASV response,
 * and use the control host IP. This is the same behaviour as with the more modern variant EPSV. Use
 * this to fix issues around NAT or provide more security by preventing FTP bounce attacks.
 */
async function enterPassiveModeIPv4_forceControlHostIP(ftp) {
    const res = await ftp.request("PASV");
    const target = parsePasvResponse(res.message);
    if (!target) {
        throw new Error("Can't parse PASV response: " + res.message);
    }
    const controlHost = ftp.socket.remoteAddress;
    if (controlHost === undefined) {
        throw new Error("Control socket is disconnected, can't get remote address.");
    }
    await connectForPassiveTransfer(controlHost, target.port, ftp);
    return res;
}
/**
 * Parse a PASV response.
 */
function parsePasvResponse(message) {
    // Get host and port from PASV response, e.g. "227 Entering Passive Mode (192,168,1,100,10,229)"
    const groups = message.match(/([-\d]+,[-\d]+,[-\d]+,[-\d]+),([-\d]+),([-\d]+)/);
    if (groups === null || groups.length !== 4) {
        throw new Error(`Can't parse response to 'PASV': ${message}`);
    }
    return {
        host: groups[1].replace(/,/g, "."),
        port: (parseInt(groups[2], 10) & 255) * 256 + (parseInt(groups[3], 10) & 255)
    };
}
function connectForPassiveTransfer(host, port, ftp) {
    return new Promise((resolve, reject) => {
        let socket = ftp._newSocket();
        const handleConnErr = function (err) {
            err.message = "Can't open data connection in passive mode: " + err.message;
            reject(err);
        };
        const handleTimeout = function () {
            socket.destroy();
            reject(new Error(`Timeout when trying to open data connection to ${host}:${port}`));
        };
        socket.setTimeout(ftp.timeout);
        socket.on("error", handleConnErr);
        socket.on("timeout", handleTimeout);
        socket.connect({ port, host, family: ftp.ipFamily }, () => {
            if (ftp.socket instanceof tls_1.TLSSocket) {
                socket = (0, tls_1.connect)(Object.assign({}, ftp.tlsOptions, {
                    socket,
                    // Reuse the TLS session negotiated earlier when the control connection
                    // was upgraded. Servers expect this because it provides additional
                    // security: If a completely new session would be negotiated, a hacker
                    // could guess the port and connect to the new data connection before we do
                    // by just starting his/her own TLS session.
                    session: ftp.socket.getSession()
                }));
                // It's the responsibility of the transfer task to wait until the
                // TLS socket issued the event 'secureConnect'. We can't do this
                // here because some servers will start upgrading after the
                // specific transfer request has been made. List and download don't
                // have to wait for this event because the server sends whenever it
                // is ready. But for upload this has to be taken into account,
                // see the details in the upload() function below.
            }
            // Let the FTPContext listen to errors from now on, remove local handler.
            socket.removeListener("error", handleConnErr);
            socket.removeListener("timeout", handleTimeout);
            ftp.dataSocket = socket;
            resolve();
        });
    });
}
/**
 * Helps resolving/rejecting transfers.
 *
 * This is used internally for all FTP transfers. For example when downloading, the server might confirm
 * with "226 Transfer complete" when in fact the download on the data connection has not finished
 * yet. With all transfers we make sure that a) the result arrived and b) has been confirmed by
 * e.g. the control connection. We just don't know in which order this will happen.
 */
class TransferResolver {
    /**
     * Instantiate a TransferResolver
     */
    constructor(ftp, progress) {
        this.ftp = ftp;
        this.progress = progress;
        this.response = undefined;
        this.dataTransferDone = false;
    }
    /**
     * Mark the beginning of a transfer.
     *
     * @param name - Name of the transfer, usually the filename.
     * @param type - Type of transfer, usually "upload" or "download".
     */
    onDataStart(name, type) {
        // Let the data socket be in charge of tracking timeouts during transfer.
        // The control socket sits idle during this time anyway and might provoke
        // a timeout unnecessarily. The control connection will take care
        // of timeouts again once data transfer is complete or failed.
        if (this.ftp.dataSocket === undefined) {
            throw new Error("Data transfer should start but there is no data connection.");
        }
        this.ftp.socket.setTimeout(0);
        this.ftp.dataSocket.setTimeout(this.ftp.timeout);
        this.progress.start(this.ftp.dataSocket, name, type);
    }
    /**
     * The data connection has finished the transfer.
     */
    onDataDone(task) {
        this.progress.updateAndStop();
        // Hand-over timeout tracking back to the control connection. It's possible that
        // we don't receive the response over the control connection that the transfer is
        // done. In this case, we want to correctly associate the resulting timeout with
        // the control connection.
        this.ftp.socket.setTimeout(this.ftp.timeout);
        if (this.ftp.dataSocket) {
            this.ftp.dataSocket.setTimeout(0);
        }
        this.dataTransferDone = true;
        this.tryResolve(task);
    }
    /**
     * The control connection reports the transfer as finished.
     */
    onControlDone(task, response) {
        this.response = response;
        this.tryResolve(task);
    }
    /**
     * An error has been reported and the task should be rejected.
     */
    onError(task, err) {
        this.progress.updateAndStop();
        this.ftp.socket.setTimeout(this.ftp.timeout);
        this.ftp.dataSocket = undefined;
        task.reject(err);
    }
    /**
     * Control connection sent an unexpected request requiring a response from our part. We
     * can't provide that (because unknown) and have to close the contrext with an error because
     * the FTP server is now caught up in a state we can't resolve.
     */
    onUnexpectedRequest(response) {
        const err = new Error(`Unexpected FTP response is requesting an answer: ${response.message}`);
        this.ftp.closeWithError(err);
    }
    tryResolve(task) {
        // To resolve, we need both control and data connection to report that the transfer is done.
        const canResolve = this.dataTransferDone && this.response !== undefined;
        if (canResolve) {
            this.ftp.dataSocket = undefined;
            task.resolve(this.response);
        }
    }
}
function uploadFrom(source, config) {
    const resolver = new TransferResolver(config.ftp, config.tracker);
    const fullCommand = `${config.command} ${config.remotePath}`;
    return config.ftp.handle(fullCommand, (res, task) => {
        if (res instanceof Error) {
            resolver.onError(task, res);
        }
        else if (res.code === 150 || res.code === 125) { // Ready to upload
            const dataSocket = config.ftp.dataSocket;
            if (!dataSocket) {
                resolver.onError(task, new Error("Upload should begin but no data connection is available."));
                return;
            }
            // If we are using TLS, we have to wait until the dataSocket issued
            // 'secureConnect'. If this hasn't happened yet, getCipher() returns undefined.
            const canUpload = "getCipher" in dataSocket ? dataSocket.getCipher() !== undefined : true;
            onConditionOrEvent(canUpload, dataSocket, "secureConnect", () => {
                config.ftp.log(`Uploading to ${(0, netUtils_1.describeAddress)(dataSocket)} (${(0, netUtils_1.describeTLS)(dataSocket)})`);
                resolver.onDataStart(config.remotePath, config.type);
                (0, stream_1.pipeline)(source, dataSocket, err => {
                    if (err) {
                        resolver.onError(task, err);
                    }
                    else {
                        resolver.onDataDone(task);
                    }
                });
            });
        }
        else if ((0, parseControlResponse_1.positiveCompletion)(res.code)) { // Transfer complete
            resolver.onControlDone(task, res);
        }
        else if ((0, parseControlResponse_1.positiveIntermediate)(res.code)) {
            resolver.onUnexpectedRequest(res);
        }
        // Ignore all other positive preliminary response codes (< 200)
    });
}
function downloadTo(destination, config) {
    if (!config.ftp.dataSocket) {
        throw new Error("Download will be initiated but no data connection is available.");
    }
    const resolver = new TransferResolver(config.ftp, config.tracker);
    return config.ftp.handle(config.command, (res, task) => {
        if (res instanceof Error) {
            resolver.onError(task, res);
        }
        else if (res.code === 150 || res.code === 125) { // Ready to download
            const dataSocket = config.ftp.dataSocket;
            if (!dataSocket) {
                resolver.onError(task, new Error("Download should begin but no data connection is available."));
                return;
            }
            config.ftp.log(`Downloading from ${(0, netUtils_1.describeAddress)(dataSocket)} (${(0, netUtils_1.describeTLS)(dataSocket)})`);
            resolver.onDataStart(config.remotePath, config.type);
            (0, stream_1.pipeline)(dataSocket, destination, err => {
                if (err) {
                    resolver.onError(task, err);
                }
                else {
                    resolver.onDataDone(task);
                }
            });
        }
        else if (res.code === 350) { // Restarting at startAt.
            config.ftp.send("RETR " + config.remotePath);
        }
        else if ((0, parseControlResponse_1.positiveCompletion)(res.code)) { // Transfer complete
            resolver.onControlDone(task, res);
        }
        else if ((0, parseControlResponse_1.positiveIntermediate)(res.code)) {
            resolver.onUnexpectedRequest(res);
        }
        // Ignore all other positive preliminary response codes (< 200)
    });
}
/**
 * Calls a function immediately if a condition is met or subscribes to an event and calls
 * it once the event is emitted.
 *
 * @param condition  The condition to test.
 * @param emitter  The emitter to use if the condition is not met.
 * @param eventName  The event to subscribe to if the condition is not met.
 * @param action  The function to call.
 */
function onConditionOrEvent(condition, emitter, eventName, action) {
    if (condition === true) {
        action();
    }
    else {
        emitter.once(eventName, () => action());
    }
}
