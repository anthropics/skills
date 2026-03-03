import type { QuickJSContext } from "./context";
/**
 * Error thrown if [[QuickJSContext.unwrapResult]] unwraps an error value that isn't an object.
 */
export declare class QuickJSUnwrapError extends Error {
    cause: unknown;
    context?: QuickJSContext | undefined;
    name: string;
    constructor(cause: unknown, context?: QuickJSContext | undefined);
}
export declare class QuickJSWrongOwner extends Error {
    name: string;
}
export declare class QuickJSUseAfterFree extends Error {
    name: string;
}
export declare class QuickJSNotImplemented extends Error {
    name: string;
}
export declare class QuickJSAsyncifyError extends Error {
    name: string;
}
export declare class QuickJSAsyncifySuspended extends Error {
    name: string;
}
export declare class QuickJSMemoryLeakDetected extends Error {
    name: string;
}
