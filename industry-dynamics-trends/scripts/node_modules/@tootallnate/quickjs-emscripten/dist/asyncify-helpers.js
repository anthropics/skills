"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.awaitEachYieldedPromise = exports.maybeAsync = exports.maybeAsyncFn = void 0;
function* awaitYield(value) {
    return (yield value);
}
function awaitYieldOf(generator) {
    return awaitYield(awaitEachYieldedPromise(generator));
}
const AwaitYield = awaitYield;
AwaitYield.of = awaitYieldOf;
/**
 * Create a function that may or may not be async, using a generator
 *
 * Within the generator, call `yield* awaited(maybePromise)` to await a value
 * that may or may not be a promise.
 *
 * If the inner function never yields a promise, it will return synchronously.
 */
function maybeAsyncFn(that, fn) {
    return (...args) => {
        const generator = fn.call(that, AwaitYield, ...args);
        return awaitEachYieldedPromise(generator);
    };
}
exports.maybeAsyncFn = maybeAsyncFn;
class Example {
    constructor() {
        this.maybeAsyncMethod = maybeAsyncFn(this, function* (awaited, a) {
            yield* awaited(new Promise((resolve) => setTimeout(resolve, a)));
            return 5;
        });
    }
}
function maybeAsync(that, startGenerator) {
    const generator = startGenerator.call(that, AwaitYield);
    return awaitEachYieldedPromise(generator);
}
exports.maybeAsync = maybeAsync;
function awaitEachYieldedPromise(gen) {
    function handleNextStep(step) {
        if (step.done) {
            return step.value;
        }
        if (step.value instanceof Promise) {
            return step.value.then((value) => handleNextStep(gen.next(value)), (error) => handleNextStep(gen.throw(error)));
        }
        return handleNextStep(gen.next(step.value));
    }
    return handleNextStep(gen.next());
}
exports.awaitEachYieldedPromise = awaitEachYieldedPromise;
//# sourceMappingURL=asyncify-helpers.js.map