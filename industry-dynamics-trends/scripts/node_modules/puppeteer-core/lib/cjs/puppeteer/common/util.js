"use strict";
/**
 * @license
 * Copyright 2017 Google Inc.
 * SPDX-License-Identifier: Apache-2.0
 */
Object.defineProperty(exports, "__esModule", { value: true });
exports.unitToPixels = exports.NETWORK_IDLE_TIME = exports.SOURCE_URL_REGEX = exports.UTILITY_WORLD_NAME = exports.isDate = exports.isRegExp = exports.isPlainObject = exports.isNumber = exports.isString = exports.getSourcePuppeteerURLIfAvailable = exports.withSourcePuppeteerURLIfNone = exports.PuppeteerURL = exports.DEFAULT_VIEWPORT = exports.debugError = void 0;
exports.evaluationString = evaluationString;
exports.getReadableAsTypedArray = getReadableAsTypedArray;
exports.getReadableFromProtocolStream = getReadableFromProtocolStream;
exports.validateDialogType = validateDialogType;
exports.timeout = timeout;
exports.getSourceUrlComment = getSourceUrlComment;
exports.parsePDFOptions = parsePDFOptions;
exports.fromEmitterEvent = fromEmitterEvent;
exports.fromAbortSignal = fromAbortSignal;
exports.filterAsync = filterAsync;
const rxjs_js_1 = require("../../third_party/rxjs/rxjs.js");
const environment_js_1 = require("../environment.js");
const assert_js_1 = require("../util/assert.js");
const encoding_js_1 = require("../util/encoding.js");
const version_js_1 = require("../util/version.js");
const Debug_js_1 = require("./Debug.js");
const Errors_js_1 = require("./Errors.js");
const PDFOptions_js_1 = require("./PDFOptions.js");
/**
 * @internal
 */
exports.debugError = (0, Debug_js_1.debug)('puppeteer:error');
/**
 * @internal
 */
exports.DEFAULT_VIEWPORT = Object.freeze({ width: 800, height: 600 });
/**
 * @internal
 */
const SOURCE_URL = Symbol('Source URL for Puppeteer evaluation scripts');
/**
 * @internal
 */
class PuppeteerURL {
    static INTERNAL_URL = 'pptr:internal';
    static fromCallSite(functionName, site) {
        const url = new PuppeteerURL();
        url.#functionName = functionName;
        url.#siteString = site.toString();
        return url;
    }
    static parse = (url) => {
        url = url.slice('pptr:'.length);
        const [functionName = '', siteString = ''] = url.split(';');
        const puppeteerUrl = new PuppeteerURL();
        puppeteerUrl.#functionName = functionName;
        puppeteerUrl.#siteString = decodeURIComponent(siteString);
        return puppeteerUrl;
    };
    static isPuppeteerURL = (url) => {
        return url.startsWith('pptr:');
    };
    #functionName;
    #siteString;
    get functionName() {
        return this.#functionName;
    }
    get siteString() {
        return this.#siteString;
    }
    toString() {
        return `pptr:${[
            this.#functionName,
            encodeURIComponent(this.#siteString),
        ].join(';')}`;
    }
}
exports.PuppeteerURL = PuppeteerURL;
/**
 * @internal
 */
const withSourcePuppeteerURLIfNone = (functionName, object) => {
    if (Object.prototype.hasOwnProperty.call(object, SOURCE_URL)) {
        return object;
    }
    const original = Error.prepareStackTrace;
    Error.prepareStackTrace = (_, stack) => {
        // First element is the function.
        // Second element is the caller of this function.
        // Third element is the caller of the caller of this function
        // which is precisely what we want.
        return stack[2];
    };
    const site = new Error().stack;
    Error.prepareStackTrace = original;
    return Object.assign(object, {
        [SOURCE_URL]: PuppeteerURL.fromCallSite(functionName, site),
    });
};
exports.withSourcePuppeteerURLIfNone = withSourcePuppeteerURLIfNone;
/**
 * @internal
 */
const getSourcePuppeteerURLIfAvailable = (object) => {
    if (Object.prototype.hasOwnProperty.call(object, SOURCE_URL)) {
        return object[SOURCE_URL];
    }
    return undefined;
};
exports.getSourcePuppeteerURLIfAvailable = getSourcePuppeteerURLIfAvailable;
/**
 * @internal
 */
const isString = (obj) => {
    return typeof obj === 'string' || obj instanceof String;
};
exports.isString = isString;
/**
 * @internal
 */
const isNumber = (obj) => {
    return typeof obj === 'number' || obj instanceof Number;
};
exports.isNumber = isNumber;
/**
 * @internal
 */
const isPlainObject = (obj) => {
    return typeof obj === 'object' && obj?.constructor === Object;
};
exports.isPlainObject = isPlainObject;
/**
 * @internal
 */
const isRegExp = (obj) => {
    return typeof obj === 'object' && obj?.constructor === RegExp;
};
exports.isRegExp = isRegExp;
/**
 * @internal
 */
const isDate = (obj) => {
    return typeof obj === 'object' && obj?.constructor === Date;
};
exports.isDate = isDate;
/**
 * @internal
 */
function evaluationString(
// eslint-disable-next-line @typescript-eslint/no-unsafe-function-type
fun, ...args) {
    if ((0, exports.isString)(fun)) {
        (0, assert_js_1.assert)(args.length === 0, 'Cannot evaluate a string with arguments');
        return fun;
    }
    function serializeArgument(arg) {
        if (Object.is(arg, undefined)) {
            return 'undefined';
        }
        return JSON.stringify(arg);
    }
    return `(${fun})(${args.map(serializeArgument).join(',')})`;
}
/**
 * @internal
 */
async function getReadableAsTypedArray(readable, path) {
    const buffers = [];
    const reader = readable.getReader();
    if (path) {
        const fileHandle = await environment_js_1.environment.value.fs.promises.open(path, 'w+');
        try {
            while (true) {
                const { done, value } = await reader.read();
                if (done) {
                    break;
                }
                buffers.push(value);
                await fileHandle.writeFile(value);
            }
        }
        finally {
            await fileHandle.close();
        }
    }
    else {
        while (true) {
            const { done, value } = await reader.read();
            if (done) {
                break;
            }
            buffers.push(value);
        }
    }
    try {
        const concat = (0, encoding_js_1.mergeUint8Arrays)(buffers);
        if (concat.length === 0) {
            return null;
        }
        return concat;
    }
    catch (error) {
        (0, exports.debugError)(error);
        return null;
    }
}
/**
 * @internal
 */
async function getReadableFromProtocolStream(client, handle) {
    return new ReadableStream({
        async pull(controller) {
            const { data, base64Encoded, eof } = await client.send('IO.read', {
                handle,
            });
            controller.enqueue((0, encoding_js_1.stringToTypedArray)(data, base64Encoded ?? false));
            if (eof) {
                await client.send('IO.close', { handle });
                controller.close();
            }
        },
    });
}
const VALID_DIALOG_TYPES = new Set([
    'alert',
    'confirm',
    'prompt',
    'beforeunload',
]);
/**
 * @internal
 */
function validateDialogType(type) {
    let dialogType = null;
    if (VALID_DIALOG_TYPES.has(type)) {
        dialogType = type;
    }
    (0, assert_js_1.assert)(dialogType, `Unknown javascript dialog type: ${type}`);
    return dialogType;
}
/**
 * @internal
 */
function timeout(ms, cause) {
    return ms === 0
        ? rxjs_js_1.NEVER
        : (0, rxjs_js_1.timer)(ms).pipe((0, rxjs_js_1.map)(() => {
            throw new Errors_js_1.TimeoutError(`Timed out after waiting ${ms}ms`, { cause });
        }));
}
/**
 * @internal
 */
exports.UTILITY_WORLD_NAME = '__puppeteer_utility_world__' + version_js_1.packageVersion;
/**
 * @internal
 */
exports.SOURCE_URL_REGEX = /^[\x20\t]*\/\/[@#] sourceURL=\s{0,10}(\S*?)\s{0,10}$/m;
/**
 * @internal
 */
function getSourceUrlComment(url) {
    return `//# sourceURL=${url}`;
}
/**
 * @internal
 */
exports.NETWORK_IDLE_TIME = 500;
/**
 * @internal
 */
function parsePDFOptions(options = {}, lengthUnit = 'in') {
    const defaults = {
        scale: 1,
        displayHeaderFooter: false,
        headerTemplate: '',
        footerTemplate: '',
        printBackground: false,
        landscape: false,
        pageRanges: '',
        preferCSSPageSize: false,
        omitBackground: false,
        outline: false,
        tagged: true,
        waitForFonts: true,
    };
    let width = 8.5;
    let height = 11;
    if (options.format) {
        const format = PDFOptions_js_1.paperFormats[options.format.toLowerCase()][lengthUnit];
        (0, assert_js_1.assert)(format, 'Unknown paper format: ' + options.format);
        width = format.width;
        height = format.height;
    }
    else {
        width = convertPrintParameterToInches(options.width, lengthUnit) ?? width;
        height =
            convertPrintParameterToInches(options.height, lengthUnit) ?? height;
    }
    const margin = {
        top: convertPrintParameterToInches(options.margin?.top, lengthUnit) || 0,
        left: convertPrintParameterToInches(options.margin?.left, lengthUnit) || 0,
        bottom: convertPrintParameterToInches(options.margin?.bottom, lengthUnit) || 0,
        right: convertPrintParameterToInches(options.margin?.right, lengthUnit) || 0,
    };
    // Quirk https://bugs.chromium.org/p/chromium/issues/detail?id=840455#c44
    if (options.outline) {
        options.tagged = true;
    }
    return {
        ...defaults,
        ...options,
        width,
        height,
        margin,
    };
}
/**
 * @internal
 */
exports.unitToPixels = {
    px: 1,
    in: 96,
    cm: 37.8,
    mm: 3.78,
};
function convertPrintParameterToInches(parameter, lengthUnit = 'in') {
    if (typeof parameter === 'undefined') {
        return undefined;
    }
    let pixels;
    if ((0, exports.isNumber)(parameter)) {
        // Treat numbers as pixel values to be aligned with phantom's paperSize.
        pixels = parameter;
    }
    else if ((0, exports.isString)(parameter)) {
        const text = parameter;
        let unit = text.substring(text.length - 2).toLowerCase();
        let valueText = '';
        if (unit in exports.unitToPixels) {
            valueText = text.substring(0, text.length - 2);
        }
        else {
            // In case of unknown unit try to parse the whole parameter as number of pixels.
            // This is consistent with phantom's paperSize behavior.
            unit = 'px';
            valueText = text;
        }
        const value = Number(valueText);
        (0, assert_js_1.assert)(!isNaN(value), 'Failed to parse parameter value: ' + text);
        pixels = value * exports.unitToPixels[unit];
    }
    else {
        throw new Error('page.pdf() Cannot handle parameter type: ' + typeof parameter);
    }
    return pixels / exports.unitToPixels[lengthUnit];
}
/**
 * @internal
 */
function fromEmitterEvent(emitter, eventName) {
    return new rxjs_js_1.Observable(subscriber => {
        const listener = (event) => {
            subscriber.next(event);
        };
        emitter.on(eventName, listener);
        return () => {
            emitter.off(eventName, listener);
        };
    });
}
/**
 * @internal
 */
function fromAbortSignal(signal, cause) {
    return signal
        ? (0, rxjs_js_1.fromEvent)(signal, 'abort').pipe((0, rxjs_js_1.map)(() => {
            if (signal.reason instanceof Error) {
                signal.reason.cause = cause;
                throw signal.reason;
            }
            throw new Error(signal.reason, { cause });
        }))
        : rxjs_js_1.NEVER;
}
/**
 * @internal
 */
function filterAsync(predicate) {
    return (0, rxjs_js_1.mergeMap)((value) => {
        return (0, rxjs_js_1.from)(Promise.resolve(predicate(value))).pipe((0, rxjs_js_1.filter)(isMatch => {
            return isMatch;
        }), (0, rxjs_js_1.map)(() => {
            return value;
        }));
    });
}
//# sourceMappingURL=util.js.map