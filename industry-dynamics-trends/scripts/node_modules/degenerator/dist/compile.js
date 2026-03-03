"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.compile = void 0;
const util_1 = require("util");
const degenerator_1 = require("./degenerator");
function compile(qjs, code, returnName, options = {}) {
    const compiled = (0, degenerator_1.degenerator)(code, options.names ?? []);
    const vm = qjs.newContext();
    // Add functions to global
    if (options.sandbox) {
        for (const [name, value] of Object.entries(options.sandbox)) {
            if (typeof value !== 'function') {
                throw new Error(`Expected a "function" for sandbox property \`${name}\`, but got "${typeof value}"`);
            }
            const fnHandle = vm.newFunction(name, (...args) => {
                const result = value(...args.map((arg) => quickJSHandleToHost(vm, arg)));
                vm.runtime.executePendingJobs();
                return hostToQuickJSHandle(vm, result);
            });
            fnHandle.consume((handle) => vm.setProp(vm.global, name, handle));
        }
    }
    const fnResult = vm.evalCode(`${compiled};${returnName}`, options.filename);
    const fn = vm.unwrapResult(fnResult);
    const t = vm.typeof(fn);
    if (t !== 'function') {
        throw new Error(`Expected a "function" named \`${returnName}\` to be defined, but got "${t}"`);
    }
    const r = async function (...args) {
        let promiseHandle;
        let resolvedHandle;
        try {
            const result = vm.callFunction(fn, vm.undefined, ...args.map((arg) => hostToQuickJSHandle(vm, arg)));
            promiseHandle = vm.unwrapResult(result);
            const resolvedResultP = vm.resolvePromise(promiseHandle);
            vm.runtime.executePendingJobs();
            const resolvedResult = await resolvedResultP;
            resolvedHandle = vm.unwrapResult(resolvedResult);
            return quickJSHandleToHost(vm, resolvedHandle);
        }
        catch (err) {
            if (err && typeof err === 'object' && 'cause' in err && err.cause) {
                if (typeof err.cause === 'object' &&
                    'stack' in err.cause &&
                    'name' in err.cause &&
                    'message' in err.cause &&
                    typeof err.cause.stack === 'string' &&
                    typeof err.cause.name === 'string' &&
                    typeof err.cause.message === 'string') {
                    // QuickJS Error `stack` does not include the name +
                    // message, so patch those in to behave more like V8
                    err.cause.stack = `${err.cause.name}: ${err.cause.message}\n${err.cause.stack}`;
                }
                throw err.cause;
            }
            throw err;
        }
        finally {
            promiseHandle?.dispose();
            resolvedHandle?.dispose();
        }
    };
    Object.defineProperty(r, 'toString', {
        value: () => compiled,
        enumerable: false,
    });
    return r;
}
exports.compile = compile;
function quickJSHandleToHost(vm, val) {
    return vm.dump(val);
}
function hostToQuickJSHandle(vm, val) {
    if (typeof val === 'undefined') {
        return vm.undefined;
    }
    else if (val === null) {
        return vm.null;
    }
    else if (typeof val === 'string') {
        return vm.newString(val);
    }
    else if (typeof val === 'number') {
        return vm.newNumber(val);
    }
    else if (typeof val === 'bigint') {
        return vm.newBigInt(val);
    }
    else if (typeof val === 'boolean') {
        return val ? vm.true : vm.false;
    }
    else if (util_1.types.isPromise(val)) {
        const promise = vm.newPromise();
        promise.settled.then(vm.runtime.executePendingJobs);
        val.then((r) => {
            promise.resolve(hostToQuickJSHandle(vm, r));
        }, (err) => {
            promise.reject(hostToQuickJSHandle(vm, err));
        });
        return promise.handle;
    }
    else if (util_1.types.isNativeError(val)) {
        return vm.newError(val);
    }
    throw new Error(`Unsupported value: ${val}`);
}
//# sourceMappingURL=compile.js.map