/**
 * @license
 * Copyright 2023 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
import { ProtocolError, TimeoutError } from '../common/Errors.js';
import { PuppeteerURL } from '../common/util.js';
import { BidiDeserializer } from './Deserializer.js';
/**
 * @internal
 */
export function createEvaluationError(details) {
    if (details.exception.type === 'object' && !('value' in details.exception)) {
        // Heuristic detecting a platform object was thrown. WebDriver BiDi serializes
        // platform objects without value. If so, throw a generic error with the actual
        // exception's message, as there is no way to restore the original exception's
        // constructor.
        return new Error(details.text);
    }
    if (details.exception.type !== 'error') {
        return BidiDeserializer.deserialize(details.exception);
    }
    const [name = '', ...parts] = details.text.split(': ');
    const message = parts.join(': ');
    const error = new Error(message);
    error.name = name;
    // The first line is this function which we ignore.
    const stackLines = [];
    if (details.stackTrace && stackLines.length < Error.stackTraceLimit) {
        for (const frame of details.stackTrace.callFrames.reverse()) {
            if (PuppeteerURL.isPuppeteerURL(frame.url) &&
                frame.url !== PuppeteerURL.INTERNAL_URL) {
                const url = PuppeteerURL.parse(frame.url);
                stackLines.unshift(`    at ${frame.functionName || url.functionName} (${url.functionName} at ${url.siteString}, <anonymous>:${frame.lineNumber}:${frame.columnNumber})`);
            }
            else {
                stackLines.push(`    at ${frame.functionName || '<anonymous>'} (${frame.url}:${frame.lineNumber}:${frame.columnNumber})`);
            }
            if (stackLines.length >= Error.stackTraceLimit) {
                break;
            }
        }
    }
    error.stack = [details.text, ...stackLines].join('\n');
    return error;
}
/**
 * @internal
 */
export function rewriteNavigationError(message, ms) {
    return error => {
        if (error instanceof ProtocolError) {
            error.message += ` at ${message}`;
        }
        else if (error instanceof TimeoutError) {
            error.message = `Navigation timeout of ${ms} ms exceeded`;
        }
        throw error;
    };
}
//# sourceMappingURL=util.js.map