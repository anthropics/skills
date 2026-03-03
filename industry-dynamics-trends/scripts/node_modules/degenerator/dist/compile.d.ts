/// <reference types="node" />
import type { Context } from 'vm';
import type { QuickJSWASMModule } from '@tootallnate/quickjs-emscripten';
import type { DegeneratorNames } from './degenerator';
export interface CompileOptions {
    names?: DegeneratorNames;
    filename?: string;
    sandbox?: Context;
}
export declare function compile<R = unknown, A extends unknown[] = []>(qjs: QuickJSWASMModule, code: string, returnName: string, options?: CompileOptions): (...args: A) => Promise<R>;
//# sourceMappingURL=compile.d.ts.map