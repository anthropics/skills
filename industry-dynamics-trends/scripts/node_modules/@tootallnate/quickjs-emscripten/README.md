# quickjs-emscripten

Javascript/Typescript bindings for QuickJS, a modern Javascript interpreter,
compiled to WebAssembly.

- Safely evaluate untrusted Javascript (up to ES2020).
- Create and manipulate values inside the QuickJS runtime ([more][values]).
- Expose host functions to the QuickJS runtime ([more][functions]).
- Execute synchronous code that uses asynchronous functions, with [asyncify][asyncify].

[Github] | [NPM] | [API Documentation][api] | [Examples][tests]

```typescript
import { getQuickJS } from "quickjs-emscripten"

async function main() {
  const QuickJS = await getQuickJS()
  const vm = QuickJS.newContext()

  const world = vm.newString("world")
  vm.setProp(vm.global, "NAME", world)
  world.dispose()

  const result = vm.evalCode(`"Hello " + NAME + "!"`)
  if (result.error) {
    console.log("Execution failed:", vm.dump(result.error))
    result.error.dispose()
  } else {
    console.log("Success:", vm.dump(result.value))
    result.value.dispose()
  }

  vm.dispose()
}

main()
```

[github]: https://github.com/justjake/quickjs-emscripten
[npm]: https://www.npmjs.com/package/quickjs-emscripten
[api]: https://github.com/justjake/quickjs-emscripten/blob/main/doc/modules.md
[tests]: https://github.com/justjake/quickjs-emscripten/blob/main/ts/quickjs.test.ts
[values]: #interfacing-with-the-interpreter
[asyncify]: #asyncify
[functions]: #exposing-apis

## Usage

Install from `npm`: `npm install --save quickjs-emscripten` or `yarn add quickjs-emscripten`.

The root entrypoint of this library is the `getQuickJS` function, which returns
a promise that resolves to a [QuickJS singleton](./doc/classes/quickjs.md) when
the QuickJS WASM module is ready.

Once `getQuickJS` has been awaited at least once, you also can use the `getQuickJSSync`
function to directly access the singleton engine in your synchronous code.

### Safely evaluate Javascript code

See [QuickJS.evalCode](https://github.com/justjake/quickjs-emscripten/blob/main/doc/classes/quickjs.md#evalcode)

```typescript
import { getQuickJS, shouldInterruptAfterDeadline } from "quickjs-emscripten"

getQuickJS().then((QuickJS) => {
  const result = QuickJS.evalCode("1 + 1", {
    shouldInterrupt: shouldInterruptAfterDeadline(Date.now() + 1000),
    memoryLimitBytes: 1024 * 1024,
  })
  console.log(result)
})
```

### Interfacing with the interpreter

You can use [QuickJSContext](https://github.com/justjake/quickjs-emscripten/blob/main/doc/classes/QuickJSContext.md)
to build a scripting environment by modifying globals and exposing functions
into the QuickJS interpreter.

Each `QuickJSContext` instance has its own environment -- globals, built-in
classes -- and actions from one context won't leak into other contexts or
runtimes (with one exception, see [Asyncify][asyncify]).

Every context is created inside a
[QuickJSRuntime](https://github.com/justjake/quickjs-emscripten/blob/main/doc/classes/QuickJSRuntime.md).
A runtime represents a Javascript heap, and you can even share values between
contexts in the same runtime.

```typescript
const vm = QuickJS.newContext()
let state = 0

const fnHandle = vm.newFunction("nextId", () => {
  return vm.newNumber(++state)
})

vm.setProp(vm.global, "nextId", fnHandle)
fnHandle.dispose()

const nextId = vm.unwrapResult(vm.evalCode(`nextId(); nextId(); nextId()`))
console.log("vm result:", vm.getNumber(nextId), "native state:", state)

nextId.dispose()
vm.dispose()
```

When you create a context from a top-level API like in the example above,
instead of by calling `runtime.newContext()`, a runtime is automatically created
for the lifetime of the context, and disposed of when you dispose the context.

#### Runtime

The runtime has APIs for CPU and memory limits that apply to all contexts within
the runtime in aggregate. You can also use the runtime to configure EcmaScript
module loading.

```typescript
const runtime = QuickJS.newRuntime()
// "Should be enough for everyone" -- attributed to B. Gates
runtime.setMemoryLimit(1024 * 640)
// Limit stack size
runtime.setMaxStackSize(1024 * 320)
// Interrupt computation after 1024 calls to the interrupt handler
let interruptCycles = 0
runtime.setInterruptHandler(() => ++interruptCycles > 1024)
// Toy module system that always returns the module name
// as the default export
runtime.setModuleLoader((moduleName) => `export default '${moduleName}'`)
const context = runtime.newContext()
const ok = context.evalCode(`
import fooName from './foo.js'
globalThis.result = fooName
`)
context.unwrapResult(ok).dispose()
// logs "foo.js"
console.log(context.getProp(context.global, "result").consume(context.dump))
context.dispose()
runtime.dispose()
```

### Memory Management

Many methods in this library return handles to memory allocated inside the
WebAssembly heap. These types cannot be garbage-collected as usual in
Javascript. Instead, you must manually manage their memory by calling a
`.dispose()` method to free the underlying resources. Once a handle has been
disposed, it cannot be used anymore. Note that in the example above, we call
`.dispose()` on each handle once it is no longer needed.

Calling `QuickJSContext.dispose()` will throw a RuntimeError if you've forgotten to
dispose any handles associated with that VM, so it's good practice to create a
new VM instance for each of your tests, and to call `vm.dispose()` at the end
of every test.

```typescript
const vm = QuickJS.newContext()
const numberHandle = vm.newNumber(42)
// Note: numberHandle not disposed, so it leaks memory.
vm.dispose()
// throws RuntimeError: abort(Assertion failed: list_empty(&rt->gc_obj_list), at: quickjs/quickjs.c,1963,JS_FreeRuntime)
```

Here are some strategies to reduce the toil of calling `.dispose()` on each
handle you create:

#### Scope

A
[`Scope`](https://github.com/justjake/quickjs-emscripten/blob/main/doc/classes/scope.md#class-scope)
instance manages a set of disposables and calls their `.dispose()`
method in the reverse order in which they're added to the scope. Here's the
"Interfacing with the interpreter" example re-written using `Scope`:

```typescript
Scope.withScope((scope) => {
  const vm = scope.manage(QuickJS.newContext())
  let state = 0

  const fnHandle = scope.manage(
    vm.newFunction("nextId", () => {
      return vm.newNumber(++state)
    })
  )

  vm.setProp(vm.global, "nextId", fnHandle)

  const nextId = scope.manage(vm.unwrapResult(vm.evalCode(`nextId(); nextId(); nextId()`)))
  console.log("vm result:", vm.getNumber(nextId), "native state:", state)

  // When the withScope block exits, it calls scope.dispose(), which in turn calls
  // the .dispose() methods of all the disposables managed by the scope.
})
```

You can also create `Scope` instances with `new Scope()` if you want to manage
calling `scope.dispose()` yourself.

#### `Lifetime.consume(fn)`

[`Lifetime.consume`](https://github.com/justjake/quickjs-emscripten/blob/main/doc/classes/lifetime.md#consume)
is sugar for the common pattern of using a handle and then
immediately disposing of it. `Lifetime.consume` takes a `map` function that
produces a result of any type. The `map` fuction is called with the handle,
then the handle is disposed, then the result is returned.

Here's the "Interfacing with interpreter" example re-written using `.consume()`:

```typescript
const vm = QuickJS.newContext()
let state = 0

vm.newFunction("nextId", () => {
  return vm.newNumber(++state)
}).consume((fnHandle) => vm.setProp(vm.global, "nextId", fnHandle))

vm.unwrapResult(vm.evalCode(`nextId(); nextId(); nextId()`)).consume((nextId) =>
  console.log("vm result:", vm.getNumber(nextId), "native state:", state)
)

vm.dispose()
```

Generally working with `Scope` leads to more straight-forward code, but
`Lifetime.consume` can be handy sugar as part of a method call chain.

### Exposing APIs

To add APIs inside the QuickJS environment, you'll need to create objects to
define the shape of your API, and add properties and functions to those objects
to allow code inside QuickJS to call code on the host.

By default, no host functionality is exposed to code running inside QuickJS.

```typescript
const vm = QuickJS.newContext()
// `console.log`
const logHandle = vm.newFunction("log", (...args) => {
  const nativeArgs = args.map(vm.dump)
  console.log("QuickJS:", ...nativeArgs)
})
// Partially implement `console` object
const consoleHandle = vm.newObject()
vm.setProp(consoleHandle, "log", logHandle)
vm.setProp(vm.global, "console", consoleHandle)
consoleHandle.dispose()
logHandle.dispose()

vm.unwrapResult(vm.evalCode(`console.log("Hello from QuickJS!")`)).dispose()
```

#### Promises

To expose an asynchronous function that _returns a promise_ to callers within
QuickJS, your function can return the handle of a `QuickJSDeferredPromise`
created via `context.newPromise()`.

When you resolve a `QuickJSDeferredPromise` -- and generally whenever async
behavior completes for the VM -- pending listeners inside QuickJS may not
execute immediately. Your code needs to explicitly call
`runtime.executePendingJobs()` to resume execution inside QuickJS. This API
gives your code maximum control to _schedule_ when QuickJS will block the host's
event loop by resuming execution.

To work with QuickJS handles that contain a promise inside the environment, you
can convert the QuickJSHandle into a native promise using
`context.resolvePromise()`. Take care with this API to avoid 'deadlocks' where
the host awaits a guest promise, but the guest cannot make progress until the
host calls `runtime.executePendingJobs()`. The simplest way to avoid this kind
of deadlock is to always schedule `executePendingJobs` after any promise is
settled.

```typescript
const vm = QuickJS.newContext()
const fakeFileSystem = new Map([["example.txt", "Example file content"]])

// Function that simulates reading data asynchronously
const readFileHandle = vm.newFunction("readFile", (pathHandle) => {
  const path = vm.getString(pathHandle)
  const promise = vm.newPromise()
  setTimeout(() => {
    const content = fakeFileSystem.get(path)
    promise.resolve(vm.newString(content || ""))
  }, 100)
  // IMPORTANT: Once you resolve an async action inside QuickJS,
  // call runtime.executePendingJobs() to run any code that was
  // waiting on the promise or callback.
  promise.settled.then(vm.runtime.executePendingJobs)
  return promise.handle
})
readFileHandle.consume((handle) => vm.setProp(vm.global, "readFile", handle))

// Evaluate code that uses `readFile`, which returns a promise
const result = vm.evalCode(`(async () => {
  const content = await readFile('example.txt')
  return content.toUpperCase()
})()`)
const promiseHandle = vm.unwrapResult(result)

// Convert the promise handle into a native promise and await it.
// If code like this deadlocks, make sure you are calling
// runtime.executePendingJobs appropriately.
const resolvedResult = await vm.resolvePromise(promiseHandle)
promiseHandle.dispose()
const resolvedHandle = vm.unwrapResult(resolvedResult)
console.log("Result:", vm.getString(resolvedHandle))
resolvedHandle.dispose()
```

#### Asyncify

Sometimes, we want to create a function that's synchronous from the perspective
of QuickJS, but prefer to implement that function _asynchronously_ in your host
code. The most obvious use-case is for EcmaScript module loading. The underlying
QuickJS C library expects the module loader function to return synchronously,
but loading data synchronously in the browser or server is somewhere between "a
bad idea" and "impossible". QuickJS also doesn't expose an API to "pause" the
execution of a runtime, and adding such an API is tricky due to the VM's
implementation.

As a work-around, we provide an alternate build of QuickJS processed by
Emscripten/Binaryen's [ASYNCIFY](https://emscripten.org/docs/porting/asyncify.html)
compiler transform. Here's how Emscripten's documentation describes Asyncify:

> Asyncify lets synchronous C or C++ code interact with asynchronous \[host] JavaScript. This allows things like:
>
> - A synchronous call in C that yields to the event loop, which allows browser events to be handled.
>
> - A synchronous call in C that waits for an asynchronous operation in \[host] JS to complete.
>
> Asyncify automatically transforms ... code into a form that can be paused and
> resumed ..., so that it is asynchronous (hence the name “Asyncify”) even though
> \[it is written] in a normal synchronous way.

This means we can suspend an _entire WebAssembly module_ (which could contain
multiple runtimes and contexts) while our host Javascript loads data
asynchronously, and then resume execution once the data load completes. This is
a very handy superpower, but it comes with a couple of major limitations:

1. _An asyncified WebAssembly module can only suspend to wait for a single
   asynchronous call at a time_. You may call back into a suspended WebAssembly
   module eg. to create a QuickJS value to return a result, but the system will
   crash if this call tries to suspend again. Take a look at Emscripten's documentation
   on [reentrancy](https://emscripten.org/docs/porting/asyncify.html#reentrancy).

2. _Asyncified code is bigger and runs slower_. The asyncified build of
   Quickjs-emscripten library is 1M, 2x larger than the 500K of the default
   version. There may be room for further
   [optimization](https://emscripten.org/docs/porting/asyncify.html#optimizing)
   Of our build in the future.

To use asyncify features, use the following functions:

- [newAsyncRuntime][]: create a runtime inside a new WebAssembly module.
- [newAsyncContext][]: create runtime and context together inside a new
  WebAssembly module.
- [newQuickJSAsyncWASMModule][]: create an empty WebAssembly module.

[newasyncruntime]: https://github.com/justjake/quickjs-emscripten/blob/main/doc/modules.md#newasyncruntime
[newasynccontext]: https://github.com/justjake/quickjs-emscripten/blob/main/doc/modules.md#newasynccontext
[newquickjsasyncwasmmodule]: https://github.com/justjake/quickjs-emscripten/blob/main/doc/modules.md#newquickjsasyncwasmmodule

These functions are asynchronous because they always create a new underlying
WebAssembly module so that each instance can suspend and resume independently,
and instantiating a WebAssembly module is an async operation. This also adds
substantial overhead compared to creating a runtime or context inside an
existing module; if you only need to wait for a single async action at a time,
you can create a single top-level module and create runtimes or contexts inside
of it.

##### Async module loader

Here's an example of valuating a script that loads React asynchronously as an ES
module. In our example, we're loading from the filesystem for reproducibility,
but you can use this technique to load using `fetch`.

```typescript
const module = await newQuickJSAsyncWASMModule()
const runtime = module.newRuntime()
const path = await import("path")
const { promises: fs } = await import("fs")

const importsPath = path.join(__dirname, "../examples/imports") + "/"
// Module loaders can return promises.
// Execution will suspend until the promise resolves.
runtime.setModuleLoader((moduleName) => {
  const modulePath = path.join(importsPath, moduleName)
  if (!modulePath.startsWith(importsPath)) {
    throw new Error("out of bounds")
  }
  console.log("loading", moduleName, "from", modulePath)
  return fs.readFile(modulePath, "utf-8")
})

// evalCodeAsync is required when execution may suspend.
const context = runtime.newContext()
const result = await context.evalCodeAsync(`
import * as React from 'esm.sh/react@17'
import * as ReactDOMServer from 'esm.sh/react-dom@17/server'
const e = React.createElement
globalThis.html = ReactDOMServer.renderToStaticMarkup(
  e('div', null, e('strong', null, 'Hello world!'))
)
`)
context.unwrapResult(result).dispose()
const html = context.getProp(context.global, "html").consume(context.getString)
console.log(html) // <div><strong>Hello world!</strong></div>
```

##### Async on host, sync in QuickJS

Here's an example of turning an async function into a sync function inside the
VM.

```typescript
const context = await newAsyncContext()
const path = await import("path")
const { promises: fs } = await import("fs")

const importsPath = path.join(__dirname, "../examples/imports") + "/"
const readFileHandle = context.newAsyncifiedFunction("readFile", async (pathHandle) => {
  const pathString = path.join(importsPath, context.getString(pathHandle))
  if (!pathString.startsWith(importsPath)) {
    throw new Error("out of bounds")
  }
  const data = await fs.readFile(pathString, "utf-8")
  return context.newString(data)
})
readFileHandle.consume((fn) => context.setProp(context.global, "readFile", fn))

// evalCodeAsync is required when execution may suspend.
const result = await context.evalCodeAsync(`
// Not a promise! Sync! vvvvvvvvvvvvvvvvvvvv 
const data = JSON.parse(readFile('data.json'))
data.map(x => x.toUpperCase()).join(' ')
`)
const upperCaseData = context.unwrapResult(result).consume(context.getString)
console.log(upperCaseData) // 'VERY USEFUL DATA'
```

### Testing your code

This library is complicated to use, so please consider automated testing your
implementation. We highly writing your test suite to run with both the "release"
build variant of quickjs-emscripten, and also the [DEBUG_SYNC] build variant.
The debug sync build variant has extra instrumentation code for detecting memory
leaks.

The class [TestQuickJSWASMModule] exposes the memory leak detection API, although
this API is only accurate when using `DEBUG_SYNC` variant.

```typescript
// Define your test suite in a function, so that you can test against
// different module loaders.
function myTests(moduleLoader: () => Promise<QuickJSWASMModule>) {
  let QuickJS: TestQuickJSWASMModule
  beforeEach(async () => {
    // Get a unique TestQuickJSWASMModule instance for each test.
    const wasmModule = await moduleLoader()
    QuickJS = new TestQuickJSWASMModule(wasmModule)
  })
  afterEach(() => {
    // Assert that the test disposed all handles. The DEBUG_SYNC build
    // variant will show detailed traces for each leak.
    QuickJS.assertNoMemoryAllocated()
  })

  it("works well", () => {
    // TODO: write a test using QuickJS
    const context = QuickJS.newContext()
    context.unwrapResult(context.evalCode("1 + 1")).dispose()
    context.dispose()
  })
}

// Run the test suite against a matrix of module loaders.
describe("Check for memory leaks with QuickJS DEBUG build", () => {
  const moduleLoader = memoizePromiseFactory(() => newQuickJSWASMModule(DEBUG_SYNC))
  myTests(moduleLoader)
})

describe("Realistic test with QuickJS RELEASE build", () => {
  myTests(getQuickJS)
})
```

For more testing examples, please explore the typescript source of [quickjs-emscripten][ts] repository.

[ts]: https://github.com/justjake/quickjs-emscripten/blob/main/ts
[debug_sync]: https://github.com/justjake/quickjs-emscripten/blob/main/doc/modules.md#debug_sync
[testquickjswasmmodule]: https://github.com/justjake/quickjs-emscripten/blob/main/doc/classes/TestQuickJSWASMModule.md

### Debugging

- Switch to a DEBUG build variant of the WebAssembly module to see debug log messages from the C part of this library.
- Set `process.env.QTS_DEBUG` to see debug log messages from the Javascript part of this library.

### More Documentation

[Github] | [NPM] | [API Documentation][api] | [Examples][tests]

## Background

This was inspired by seeing https://github.com/maple3142/duktape-eval
[on Hacker News](https://news.ycombinator.com/item?id=21946565) and Figma's
blogposts about using building a Javascript plugin runtime:

- [How Figma built the Figma plugin system](https://www.figma.com/blog/how-we-built-the-figma-plugin-system/): Describes the LowLevelJavascriptVm interface.
- [An update on plugin security](https://www.figma.com/blog/an-update-on-plugin-security/): Figma switches to QuickJS.

## Status & Roadmap

**Stability**: Because the version number of this project is below `1.0.0`,
\*expect occasional breaking API changes.

**Security**: This project makes every effort to be secure, but has not been
audited. Please use with care in production settings.

**Roadmap**: I work on this project in my free time, for fun. Here's I'm
thinking comes next. Last updated 2022-03-18.

1. Further work on module loading APIs:

   - Create modules via Javascript, instead of source text.
   - Scan source text for imports, for ahead of time or concurrent loading.
     (This is possible with third-party tools, so lower priority.)

2. Higher-level tools for reading QuickJS values:

   - Type guard functions: `context.isArray(handle)`, `context.isPromise(handle)`, etc.
   - Iteration utilities: `context.getIterable(handle)`, `context.iterateObjectEntries(handle)`.
     This better supports user-level code to deserialize complex handle objects.

3. Higher-level tools for creating QuickJS values:

   - Devise a way to avoid needing to mess around with handles when setting up
     the environment.
   - Consider integrating
     [quickjs-emscripten-sync](https://github.com/reearth/quickjs-emscripten-sync)
     for automatic translation.
   - Consider class-based or interface-type-based marshalling.

4. EcmaScript Modules / WebAssembly files / Deno support. This requires me to
   learn a lot of new things, but should be interesting for modern browser usage.

5. SQLite integration.

## Related

- Duktape wrapped in Wasm: https://github.com/maple3142/duktape-eval/blob/main/src/Makefile
- QuickJS wrapped in C++: https://github.com/ftk/quickjspp

## Developing

This library is implemented in two languages: C (compiled to WASM with
Emscripten), and Typescript.

### The C parts

The ./c directory contains C code that wraps the QuickJS C library (in ./quickjs).
Public functions (those starting with `QTS_`) in ./c/interface.c are
automatically exported to native code (via a generated header) and to
Typescript (via a generated FFI class). See ./generate.ts for how this works.

The C code builds as both with `emscripten` (using `emcc`), to produce WASM (or
ASM.js) and with `clang`. Build outputs are checked in, so you can iterate on
the Javascript parts of the library without setting up the Emscripten toolchain.

Intermediate object files from QuickJS end up in ./build/quickjs/.

This project uses `emscripten 3.1.32`.

- On ARM64, you should install `emscripten` on your machine. For example on macOS, `brew install emscripten`.
- If _the correct version of emcc_ is not in your PATH, compilation falls back to using Docker.
  On ARM64, this is 10-50x slower than native compilation, but it's just fine on x64.

Related NPM scripts:

- `yarn update-quickjs` will sync the ./quickjs folder with a
  github repo tracking the upstream QuickJS.
- `yarn make-debug` will rebuild C outputs into ./build/wrapper
- `yarn make-release` will rebuild C outputs in release mode, which is the mode
  that should be checked into the repo.

### The Typescript parts

The ./ts directory contains Typescript types and wraps the generated Emscripten
FFI in a more usable interface.

You'll need `node` and `yarn`. Install dependencies with `yarn install`.

- `yarn build` produces ./dist.
- `yarn test` runs the tests.
- `yarn test --watch` watches for changes and re-runs the tests.

### Yarn updates

Just run `yarn set version from sources` to upgrade the Yarn release.
