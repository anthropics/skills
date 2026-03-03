"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.QuickJSMemoryLeakDetected = exports.QuickJSAsyncifySuspended = exports.QuickJSAsyncifyError = exports.QuickJSNotImplemented = exports.QuickJSUseAfterFree = exports.QuickJSWrongOwner = exports.QuickJSUnwrapError = void 0;
/**
 * Error thrown if [[QuickJSContext.unwrapResult]] unwraps an error value that isn't an object.
 */
class QuickJSUnwrapError extends Error {
    constructor(cause, context) {
        super(String(cause));
        this.cause = cause;
        this.context = context;
        this.name = "QuickJSUnwrapError";
    }
}
exports.QuickJSUnwrapError = QuickJSUnwrapError;
class QuickJSWrongOwner extends Error {
    constructor() {
        super(...arguments);
        this.name = "QuickJSWrongOwner";
    }
}
exports.QuickJSWrongOwner = QuickJSWrongOwner;
class QuickJSUseAfterFree extends Error {
    constructor() {
        super(...arguments);
        this.name = "QuickJSUseAfterFree";
    }
}
exports.QuickJSUseAfterFree = QuickJSUseAfterFree;
class QuickJSNotImplemented extends Error {
    constructor() {
        super(...arguments);
        this.name = "QuickJSNotImplemented";
    }
}
exports.QuickJSNotImplemented = QuickJSNotImplemented;
class QuickJSAsyncifyError extends Error {
    constructor() {
        super(...arguments);
        this.name = "QuickJSAsyncifyError";
    }
}
exports.QuickJSAsyncifyError = QuickJSAsyncifyError;
class QuickJSAsyncifySuspended extends Error {
    constructor() {
        super(...arguments);
        this.name = "QuickJSAsyncifySuspended";
    }
}
exports.QuickJSAsyncifySuspended = QuickJSAsyncifySuspended;
class QuickJSMemoryLeakDetected extends Error {
    constructor() {
        super(...arguments);
        this.name = "QuickJSMemoryLeakDetected";
    }
}
exports.QuickJSMemoryLeakDetected = QuickJSMemoryLeakDetected;
//# sourceMappingURL=errors.js.map