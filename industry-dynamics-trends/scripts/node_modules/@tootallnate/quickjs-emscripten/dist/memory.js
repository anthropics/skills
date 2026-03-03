"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.ModuleMemory = void 0;
const lifetime_1 = require("./lifetime");
/**
 * @private
 */
class ModuleMemory {
    constructor(module) {
        this.module = module;
    }
    toPointerArray(handleArray) {
        const typedArray = new Int32Array(handleArray.map((handle) => handle.value));
        const numBytes = typedArray.length * typedArray.BYTES_PER_ELEMENT;
        const ptr = this.module._malloc(numBytes);
        var heapBytes = new Uint8Array(this.module.HEAPU8.buffer, ptr, numBytes);
        heapBytes.set(new Uint8Array(typedArray.buffer));
        return new lifetime_1.Lifetime(ptr, undefined, (ptr) => this.module._free(ptr));
    }
    newMutablePointerArray(length) {
        const zeros = new Int32Array(new Array(length).fill(0));
        const numBytes = zeros.length * zeros.BYTES_PER_ELEMENT;
        const ptr = this.module._malloc(numBytes);
        const typedArray = new Int32Array(this.module.HEAPU8.buffer, ptr, length);
        typedArray.set(zeros);
        return new lifetime_1.Lifetime({ typedArray, ptr }, undefined, (value) => this.module._free(value.ptr));
    }
    newHeapCharPointer(string) {
        const numBytes = this.module.lengthBytesUTF8(string) + 1;
        const ptr = this.module._malloc(numBytes);
        this.module.stringToUTF8(string, ptr, numBytes);
        return new lifetime_1.Lifetime(ptr, undefined, (value) => this.module._free(value));
    }
    consumeHeapCharPointer(ptr) {
        const str = this.module.UTF8ToString(ptr);
        this.module._free(ptr);
        return str;
    }
}
exports.ModuleMemory = ModuleMemory;
//# sourceMappingURL=memory.js.map