/**
 * Used as an optional.
 * `{ value: S } | { error: E }`.
 */
export type SuccessOrFail<S, F> = {
    value: S;
    error?: undefined;
} | {
    error: F;
};
export declare function isSuccess<S, F>(successOrFail: SuccessOrFail<S, F>): successOrFail is {
    value: S;
};
export declare function isFail<S, F>(successOrFail: SuccessOrFail<S, F>): successOrFail is {
    error: F;
};
/**
 * Used as an optional for results of a Vm call.
 * `{ value: VmHandle } | { error: VmHandle }`.
 */
export type VmCallResult<VmHandle> = SuccessOrFail<VmHandle, VmHandle>;
/**
 * A VmFunctionImplementation takes handles as arguments.
 * It should return a handle, or be void.
 *
 * To indicate an exception, a VMs can throw either a handle (transferred
 * directly) or any other Javascript value (only the poperties `name` and
 * `message` will be transferred). Or, the VmFunctionImplementation may return
 * a VmCallResult's `{ error: handle }` error variant.
 *
 * VmFunctionImplementation should not free its arguments or its return value.
 * It should not retain a reference to its return value or thrown error.
 */
export type VmFunctionImplementation<VmHandle> = (this: VmHandle, ...args: VmHandle[]) => VmHandle | VmCallResult<VmHandle> | void;
/**
 * A minimal interface to a Javascript execution environment.
 *
 * Higher-level tools should build over the LowLevelJavascriptVm interface to
 * share as much as possible between executors.
 *
 * From https://www.figma.com/blog/how-we-built-the-figma-plugin-system/
 */
export interface LowLevelJavascriptVm<VmHandle> {
    global: VmHandle;
    undefined: VmHandle;
    typeof(handle: VmHandle): string;
    getNumber(handle: VmHandle): number;
    getString(handle: VmHandle): string;
    newNumber(value: number): VmHandle;
    newString(value: string): VmHandle;
    newObject(prototype?: VmHandle): VmHandle;
    newFunction(name: string, value: VmFunctionImplementation<VmHandle>): VmHandle;
    getProp(handle: VmHandle, key: string | VmHandle): VmHandle;
    setProp(handle: VmHandle, key: string | VmHandle, value: VmHandle): void;
    defineProp(handle: VmHandle, key: string | VmHandle, descriptor: VmPropertyDescriptor<VmHandle>): void;
    callFunction(func: VmHandle, thisVal: VmHandle, ...args: VmHandle[]): VmCallResult<VmHandle>;
    evalCode(code: string, filename?: string): VmCallResult<VmHandle>;
}
/**
 * From https://www.figma.com/blog/how-we-built-the-figma-plugin-system/
 */
export interface VmPropertyDescriptor<VmHandle> {
    value?: VmHandle;
    configurable?: boolean;
    enumerable?: boolean;
    get?: (this: VmHandle) => VmHandle;
    set?: (this: VmHandle, value: VmHandle) => void;
}
