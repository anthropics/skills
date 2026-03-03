degenerator
===========
### Compiles sync functions into async functions

Sometimes you need to write sync looking code that's really async under the hood.
This module takes a String to one or more synchronous JavaScript functions, and
returns a new String that with those JS functions transpiled into `async`
functions.

So this:

```js
function foo() {
  return a('bar') || b();
}
```

Gets compiled into:

```js
async function foo() {
    return await a('bar') || await b();
}
```

With the compiled output code, you can evaluate the code using the `vm` module
in Node.js, or save the code to a file and require it, or whatever.

Example
-------

You must explicitly specify the names of the functions that should be
"asyncified". So say we wanted to expose a `get(url)` function that did
and HTTP request and returned the response body.

The user has provided us with this implementation:

``` js
function myFn() {
  const one = get('https://google.com');
  const two = get('http://nodejs.org');
  const three = JSON.parse(get('http://jsonip.org'));
  return [one, two, three];
}
```

Now we can compile this into an asyncronous function, implement the
async `get()` function, and finally evaluate it into a real JavaScript function
instance with the `vm` module:


```typescript
import vm from 'vm';
import { degenerator } from 'degenerator';

// The `get()` function is Promise-based (error handling omitted for brevity)
function get(endpoint: string) {
  return new Promise((resolve, reject) => {
    var mod = 0 == endpoint.indexOf('https:') ? require('https') : require('http');
    var req = mod.get(endpoint);
    req.on('response', function (res) {
      var data = '';
      res.setEncoding('utf8');
      res.on('data', function (b) { data += b; });
      res.on('end', function () {
        resolve(data);
      });
    });
  });
}

// Convert the JavaScript string provided from the user (assumed to be `str` var)
str = degenerator(str, [ 'get' ]);

// Turn the JS String into a real async function instance
const asyncFn = vm.runInNewContext(`(${str})`, { get });

// Now we can invoke the function asynchronously
asyncFn().then((res) => {
  // Do something with `res`...
});
```


API
---

### degenerator(code: string, names: Array<string|RegExp>): String

Returns a "degeneratorified" JavaScript string, with `async`/`await` transplanted.


License
-------

(The MIT License)

Copyright (c) 2013 Nathan Rajlich &lt;nathan@tootallnate.net&gt;

Permission is hereby granted, free of charge, to any person obtaining
a copy of this software and associated documentation files (the
'Software'), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be
included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED 'AS IS', WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
