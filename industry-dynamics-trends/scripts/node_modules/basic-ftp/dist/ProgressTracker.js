"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.ProgressTracker = void 0;
/**
 * Tracks progress of one socket data transfer at a time.
 */
class ProgressTracker {
    constructor() {
        this.bytesOverall = 0;
        this.intervalMs = 500;
        this.onStop = noop;
        this.onHandle = noop;
    }
    /**
     * Register a new handler for progress info. Use `undefined` to disable reporting.
     */
    reportTo(onHandle = noop) {
        this.onHandle = onHandle;
    }
    /**
     * Start tracking transfer progress of a socket.
     *
     * @param socket  The socket to observe.
     * @param name  A name associated with this progress tracking, e.g. a filename.
     * @param type  The type of the transfer, typically "upload" or "download".
     */
    start(socket, name, type) {
        let lastBytes = 0;
        this.onStop = poll(this.intervalMs, () => {
            const bytes = socket.bytesRead + socket.bytesWritten;
            this.bytesOverall += bytes - lastBytes;
            lastBytes = bytes;
            this.onHandle({
                name,
                type,
                bytes,
                bytesOverall: this.bytesOverall
            });
        });
    }
    /**
     * Stop tracking transfer progress.
     */
    stop() {
        this.onStop(false);
    }
    /**
     * Call the progress handler one more time, then stop tracking.
     */
    updateAndStop() {
        this.onStop(true);
    }
}
exports.ProgressTracker = ProgressTracker;
/**
 * Starts calling a callback function at a regular interval. The first call will go out
 * immediately. The function returns a function to stop the polling.
 */
function poll(intervalMs, updateFunc) {
    const id = setInterval(updateFunc, intervalMs);
    const stopFunc = (stopWithUpdate) => {
        clearInterval(id);
        if (stopWithUpdate) {
            updateFunc();
        }
        // Prevent repeated calls to stop calling handler.
        updateFunc = noop;
    };
    updateFunc();
    return stopFunc;
}
function noop() { }
