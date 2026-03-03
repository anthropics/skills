"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.PipeTransport = void 0;
const EventEmitter_js_1 = require("../common/EventEmitter.js");
const util_js_1 = require("../common/util.js");
const assert_js_1 = require("../util/assert.js");
const disposable_js_1 = require("../util/disposable.js");
/**
 * @internal
 */
class PipeTransport {
    #pipeWrite;
    #subscriptions = new disposable_js_1.DisposableStack();
    #isClosed = false;
    #pendingMessage = [];
    onclose;
    onmessage;
    constructor(pipeWrite, pipeRead) {
        this.#pipeWrite = pipeWrite;
        const pipeReadEmitter = this.#subscriptions.use(
        // NodeJS event emitters don't support `*` so we need to typecast
        // As long as we don't use it we should be OK.
        new EventEmitter_js_1.EventEmitter(pipeRead));
        pipeReadEmitter.on('data', buffer => {
            return this.#dispatch(buffer);
        });
        pipeReadEmitter.on('close', () => {
            if (this.onclose) {
                this.onclose.call(null);
            }
        });
        pipeReadEmitter.on('error', util_js_1.debugError);
        const pipeWriteEmitter = this.#subscriptions.use(
        // NodeJS event emitters don't support `*` so we need to typecast
        // As long as we don't use it we should be OK.
        new EventEmitter_js_1.EventEmitter(pipeWrite));
        pipeWriteEmitter.on('error', util_js_1.debugError);
    }
    send(message) {
        (0, assert_js_1.assert)(!this.#isClosed, '`PipeTransport` is closed.');
        this.#pipeWrite.write(message);
        this.#pipeWrite.write('\0');
    }
    #dispatch(buffer) {
        (0, assert_js_1.assert)(!this.#isClosed, '`PipeTransport` is closed.');
        this.#pendingMessage.push(buffer);
        if (buffer.indexOf('\0') === -1) {
            return;
        }
        const concatBuffer = Buffer.concat(this.#pendingMessage);
        let start = 0;
        let end = concatBuffer.indexOf('\0');
        while (end !== -1) {
            const message = concatBuffer.toString(undefined, start, end);
            setImmediate(() => {
                if (this.onmessage) {
                    this.onmessage.call(null, message);
                }
            });
            start = end + 1;
            end = concatBuffer.indexOf('\0', start);
        }
        if (start >= concatBuffer.length) {
            this.#pendingMessage = [];
        }
        else {
            this.#pendingMessage = [concatBuffer.subarray(start)];
        }
    }
    close() {
        this.#isClosed = true;
        this.#subscriptions.dispose();
    }
}
exports.PipeTransport = PipeTransport;
//# sourceMappingURL=PipeTransport.js.map