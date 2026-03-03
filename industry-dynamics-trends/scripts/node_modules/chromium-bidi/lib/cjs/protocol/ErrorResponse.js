"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.UnavailableNetworkDataException = exports.NoSuchNetworkDataException = exports.NoSuchNetworkCollectorException = exports.NoSuchWebExtensionException = exports.InvalidWebExtensionException = exports.UnderspecifiedStoragePartitionException = exports.UnableToSetFileInputException = exports.UnableToSetCookieException = exports.NoSuchStoragePartitionException = exports.UnsupportedOperationException = exports.UnableToCloseBrowserException = exports.UnableToCaptureScreenException = exports.UnknownErrorException = exports.UnknownCommandException = exports.SessionNotCreatedException = exports.NoSuchUserContextException = exports.NoSuchScriptException = exports.NoSuchRequestException = exports.NoSuchNodeException = exports.NoSuchInterceptException = exports.NoSuchHistoryEntryException = exports.NoSuchHandleException = exports.NoSuchFrameException = exports.NoSuchElementException = exports.NoSuchAlertException = exports.MoveTargetOutOfBoundsException = exports.InvalidSessionIdException = exports.InvalidSelectorException = exports.InvalidArgumentException = exports.Exception = void 0;
class Exception extends Error {
    error;
    message;
    stacktrace;
    constructor(error, message, stacktrace) {
        super();
        this.error = error;
        this.message = message;
        this.stacktrace = stacktrace;
    }
    toErrorResponse(commandId) {
        return {
            type: 'error',
            id: commandId,
            error: this.error,
            message: this.message,
            stacktrace: this.stacktrace,
        };
    }
}
exports.Exception = Exception;
class InvalidArgumentException extends Exception {
    constructor(message, stacktrace) {
        super("invalid argument" /* ErrorCode.InvalidArgument */, message, stacktrace);
    }
}
exports.InvalidArgumentException = InvalidArgumentException;
class InvalidSelectorException extends Exception {
    constructor(message, stacktrace) {
        super("invalid selector" /* ErrorCode.InvalidSelector */, message, stacktrace);
    }
}
exports.InvalidSelectorException = InvalidSelectorException;
class InvalidSessionIdException extends Exception {
    constructor(message, stacktrace) {
        super("invalid session id" /* ErrorCode.InvalidSessionId */, message, stacktrace);
    }
}
exports.InvalidSessionIdException = InvalidSessionIdException;
class MoveTargetOutOfBoundsException extends Exception {
    constructor(message, stacktrace) {
        super("move target out of bounds" /* ErrorCode.MoveTargetOutOfBounds */, message, stacktrace);
    }
}
exports.MoveTargetOutOfBoundsException = MoveTargetOutOfBoundsException;
class NoSuchAlertException extends Exception {
    constructor(message, stacktrace) {
        super("no such alert" /* ErrorCode.NoSuchAlert */, message, stacktrace);
    }
}
exports.NoSuchAlertException = NoSuchAlertException;
class NoSuchElementException extends Exception {
    constructor(message, stacktrace) {
        super("no such element" /* ErrorCode.NoSuchElement */, message, stacktrace);
    }
}
exports.NoSuchElementException = NoSuchElementException;
class NoSuchFrameException extends Exception {
    constructor(message, stacktrace) {
        super("no such frame" /* ErrorCode.NoSuchFrame */, message, stacktrace);
    }
}
exports.NoSuchFrameException = NoSuchFrameException;
class NoSuchHandleException extends Exception {
    constructor(message, stacktrace) {
        super("no such handle" /* ErrorCode.NoSuchHandle */, message, stacktrace);
    }
}
exports.NoSuchHandleException = NoSuchHandleException;
class NoSuchHistoryEntryException extends Exception {
    constructor(message, stacktrace) {
        super("no such history entry" /* ErrorCode.NoSuchHistoryEntry */, message, stacktrace);
    }
}
exports.NoSuchHistoryEntryException = NoSuchHistoryEntryException;
class NoSuchInterceptException extends Exception {
    constructor(message, stacktrace) {
        super("no such intercept" /* ErrorCode.NoSuchIntercept */, message, stacktrace);
    }
}
exports.NoSuchInterceptException = NoSuchInterceptException;
class NoSuchNodeException extends Exception {
    constructor(message, stacktrace) {
        super("no such node" /* ErrorCode.NoSuchNode */, message, stacktrace);
    }
}
exports.NoSuchNodeException = NoSuchNodeException;
class NoSuchRequestException extends Exception {
    constructor(message, stacktrace) {
        super("no such request" /* ErrorCode.NoSuchRequest */, message, stacktrace);
    }
}
exports.NoSuchRequestException = NoSuchRequestException;
class NoSuchScriptException extends Exception {
    constructor(message, stacktrace) {
        super("no such script" /* ErrorCode.NoSuchScript */, message, stacktrace);
    }
}
exports.NoSuchScriptException = NoSuchScriptException;
class NoSuchUserContextException extends Exception {
    constructor(message, stacktrace) {
        super("no such user context" /* ErrorCode.NoSuchUserContext */, message, stacktrace);
    }
}
exports.NoSuchUserContextException = NoSuchUserContextException;
class SessionNotCreatedException extends Exception {
    constructor(message, stacktrace) {
        super("session not created" /* ErrorCode.SessionNotCreated */, message, stacktrace);
    }
}
exports.SessionNotCreatedException = SessionNotCreatedException;
class UnknownCommandException extends Exception {
    constructor(message, stacktrace) {
        super("unknown command" /* ErrorCode.UnknownCommand */, message, stacktrace);
    }
}
exports.UnknownCommandException = UnknownCommandException;
class UnknownErrorException extends Exception {
    constructor(message, stacktrace = new Error().stack) {
        super("unknown error" /* ErrorCode.UnknownError */, message, stacktrace);
    }
}
exports.UnknownErrorException = UnknownErrorException;
class UnableToCaptureScreenException extends Exception {
    constructor(message, stacktrace) {
        super("unable to capture screen" /* ErrorCode.UnableToCaptureScreen */, message, stacktrace);
    }
}
exports.UnableToCaptureScreenException = UnableToCaptureScreenException;
class UnableToCloseBrowserException extends Exception {
    constructor(message, stacktrace) {
        super("unable to close browser" /* ErrorCode.UnableToCloseBrowser */, message, stacktrace);
    }
}
exports.UnableToCloseBrowserException = UnableToCloseBrowserException;
class UnsupportedOperationException extends Exception {
    constructor(message, stacktrace) {
        super("unsupported operation" /* ErrorCode.UnsupportedOperation */, message, stacktrace);
    }
}
exports.UnsupportedOperationException = UnsupportedOperationException;
class NoSuchStoragePartitionException extends Exception {
    constructor(message, stacktrace) {
        super("no such storage partition" /* ErrorCode.NoSuchStoragePartition */, message, stacktrace);
    }
}
exports.NoSuchStoragePartitionException = NoSuchStoragePartitionException;
class UnableToSetCookieException extends Exception {
    constructor(message, stacktrace) {
        super("unable to set cookie" /* ErrorCode.UnableToSetCookie */, message, stacktrace);
    }
}
exports.UnableToSetCookieException = UnableToSetCookieException;
class UnableToSetFileInputException extends Exception {
    constructor(message, stacktrace) {
        super("unable to set file input" /* ErrorCode.UnableToSetFileInput */, message, stacktrace);
    }
}
exports.UnableToSetFileInputException = UnableToSetFileInputException;
class UnderspecifiedStoragePartitionException extends Exception {
    constructor(message, stacktrace) {
        super("underspecified storage partition" /* ErrorCode.UnderspecifiedStoragePartition */, message, stacktrace);
    }
}
exports.UnderspecifiedStoragePartitionException = UnderspecifiedStoragePartitionException;
class InvalidWebExtensionException extends Exception {
    constructor(message, stacktrace) {
        super("invalid web extension" /* ErrorCode.InvalidWebExtension */, message, stacktrace);
    }
}
exports.InvalidWebExtensionException = InvalidWebExtensionException;
class NoSuchWebExtensionException extends Exception {
    constructor(message, stacktrace) {
        super("no such web extension" /* ErrorCode.NoSuchWebExtension */, message, stacktrace);
    }
}
exports.NoSuchWebExtensionException = NoSuchWebExtensionException;
class NoSuchNetworkCollectorException extends Exception {
    constructor(message, stacktrace) {
        super("no such network collector" /* ErrorCode.NoSuchNetworkCollector */, message, stacktrace);
    }
}
exports.NoSuchNetworkCollectorException = NoSuchNetworkCollectorException;
class NoSuchNetworkDataException extends Exception {
    constructor(message, stacktrace) {
        super("no such network data" /* ErrorCode.NoSuchNetworkData */, message, stacktrace);
    }
}
exports.NoSuchNetworkDataException = NoSuchNetworkDataException;
class UnavailableNetworkDataException extends Exception {
    constructor(message, stacktrace) {
        super("unavailable network data" /* ErrorCode.UnavailableNetworkData */, message, stacktrace);
    }
}
exports.UnavailableNetworkDataException = UnavailableNetworkDataException;
//# sourceMappingURL=ErrorResponse.js.map