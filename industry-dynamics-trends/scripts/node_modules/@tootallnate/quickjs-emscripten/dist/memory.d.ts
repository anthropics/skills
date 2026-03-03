import { EitherModule } from "./emscripten-types";
import { OwnedHeapCharPointer, JSContextPointerPointer, JSValueConstPointerPointer, JSValuePointerPointer } from "./types-ffi";
import { Lifetime } from "./lifetime";
import { QuickJSHandle } from "./types";
/**
 * @private
 */
export declare class ModuleMemory {
    module: EitherModule;
    constructor(module: EitherModule);
    toPointerArray(handleArray: QuickJSHandle[]): Lifetime<JSValueConstPointerPointer>;
    newMutablePointerArray<T extends JSContextPointerPointer | JSValuePointerPointer>(length: number): Lifetime<{
        typedArray: Int32Array;
        ptr: T;
    }>;
    newHeapCharPointer(string: string): Lifetime<OwnedHeapCharPointer>;
    consumeHeapCharPointer(ptr: OwnedHeapCharPointer): string;
}
