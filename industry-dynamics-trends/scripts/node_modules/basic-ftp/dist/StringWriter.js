"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.StringWriter = void 0;
const stream_1 = require("stream");
class StringWriter extends stream_1.Writable {
    constructor() {
        super(...arguments);
        this.buf = Buffer.alloc(0);
    }
    _write(chunk, _, callback) {
        if (chunk instanceof Buffer) {
            this.buf = Buffer.concat([this.buf, chunk]);
            callback(null);
        }
        else {
            callback(new Error("StringWriter expects chunks of type 'Buffer'."));
        }
    }
    getText(encoding) {
        return this.buf.toString(encoding);
    }
}
exports.StringWriter = StringWriter;
