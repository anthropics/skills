import { Socket } from "net";
export type ProgressType = "upload" | "download" | "list";
/**
 * Describes progress of file transfer.
 */
export interface ProgressInfo {
    /** A name describing this info, e.g. the filename of the transfer. */
    readonly name: string;
    /** The type of transfer, typically "upload" or "download". */
    readonly type: ProgressType;
    /** Transferred bytes in current transfer. */
    readonly bytes: number;
    /** Transferred bytes since last counter reset. Useful for tracking multiple transfers. */
    readonly bytesOverall: number;
}
export type ProgressHandler = (info: ProgressInfo) => void;
/**
 * Tracks progress of one socket data transfer at a time.
 */
export declare class ProgressTracker {
    bytesOverall: number;
    protected readonly intervalMs = 500;
    protected onStop: (stopWithUpdate: boolean) => void;
    protected onHandle: ProgressHandler;
    /**
     * Register a new handler for progress info. Use `undefined` to disable reporting.
     */
    reportTo(onHandle?: ProgressHandler): void;
    /**
     * Start tracking transfer progress of a socket.
     *
     * @param socket  The socket to observe.
     * @param name  A name associated with this progress tracking, e.g. a filename.
     * @param type  The type of the transfer, typically "upload" or "download".
     */
    start(socket: Socket, name: string, type: ProgressType): void;
    /**
     * Stop tracking transfer progress.
     */
    stop(): void;
    /**
     * Call the progress handler one more time, then stop tracking.
     */
    updateAndStop(): void;
}
