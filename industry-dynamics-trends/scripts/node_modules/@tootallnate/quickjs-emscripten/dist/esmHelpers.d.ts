/** Typescript thinks import('...js/.d.ts') needs mod.default.default */
declare function fakeUnwrapDefault<T>(mod: {
    default: T;
}): T;
/** Typescript thinks import('...ts') doesn't need mod.default.default, but does */
declare function actualUnwrapDefault<T>(mod: T): T;
export declare const unwrapTypescript: typeof actualUnwrapDefault;
export declare const unwrapJavascript: typeof fakeUnwrapDefault;
export {};
