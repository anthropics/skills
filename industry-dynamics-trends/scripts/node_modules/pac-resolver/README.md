pac-resolver
============
### Generates an asynchronous resolver function from a [PAC file][pac-wikipedia]


This module accepts a JavaScript String of code, which is meant to be a
[PAC proxy file][pac-wikipedia], and returns a generated asynchronous
`FindProxyForURL()` function.

Example
-------

Given the PAC proxy file named `proxy.pac`:

```js
function FindProxyForURL(url, host) {
  if (isInNet(myIpAddress(), "10.1.10.0", "255.255.255.0")) {
    return "PROXY 1.2.3.4:8080";
  } else {
    return "DIRECT";
  }
}
```

You can consume this PAC file with `pac-resolver` like so:

```ts
import { readFileSync } from 'fs';
import { createPacResolver } from 'pac-resolver';

const FindProxyForURL = createPacResolver(readFileSync('proxy.pac'));

const res = await FindProxyForURL('http://foo.com/');
console.log(res);
// "DIRECT"
```


API
---

### pac(qjs: QuickJSWASMModule, pacFileContents: string | Buffer, options?: PacResolverOptions) → Function

Returns an asynchronous `FindProxyForURL()` function based off of the given JS
string `pacFileContents` PAC proxy file. An optional `options` object may be
passed in which respects the following options:

 * `filename` - String - the filename to use in error stack traces. Defaults to `proxy.pac`.
 * `sandbox` - Object - a map of functions to include in the sandbox of the
 JavaScript environment where the JS code will be executed. i.e. if you wanted to
 include the common `alert` function you could pass `alert: console.log`. For
 async functions, you must set the `async = true` property on the function
 instance, and the JS code will be able to invoke the function as if it were
 synchronous.

 The `qjs` parameter is a QuickJS module instance as returned from `getQuickJS()` from the `quickjs-emscripten` module.

[pac-file-docs]: https://web.archive.org/web/20070602031929/http://wp.netscape.com/eng/mozilla/2.0/relnotes/demo/proxy-live.html
[pac-wikipedia]: http://wikipedia.org/wiki/Proxy_auto-config
