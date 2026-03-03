"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.dataUriToBuffer = void 0;
const common_1 = require("./common");
function nodeBuffertoArrayBuffer(nodeBuf) {
    if (nodeBuf.byteLength === nodeBuf.buffer.byteLength) {
        return nodeBuf.buffer; // large strings may get their own memory allocation
    }
    const buffer = new ArrayBuffer(nodeBuf.byteLength);
    const view = new Uint8Array(buffer);
    view.set(nodeBuf);
    return buffer;
}
function base64ToArrayBuffer(base64) {
    return nodeBuffertoArrayBuffer(Buffer.from(base64, 'base64'));
}
function stringToBuffer(str) {
    return nodeBuffertoArrayBuffer(Buffer.from(str, 'ascii'));
}
/**
 * Returns a `Buffer` instance from the given data URI `uri`.
 *
 * @param {String} uri Data URI to turn into a Buffer instance
 */
exports.dataUriToBuffer = (0, common_1.makeDataUriToBuffer)({ stringToBuffer, base64ToArrayBuffer });
//# sourceMappingURL=node.js.map