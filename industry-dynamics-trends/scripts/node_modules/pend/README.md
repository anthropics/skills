# Pend

Dead-simple optimistic async helper.

## Usage

```js
var Pend = require('pend');
var pend = new Pend();
pend.max = 10; // defaults to Infinity
setTimeout(pend.hold(), 1000); // pend.wait will have to wait for this hold to finish
pend.go(function(cb) {
  console.log("this function is immediately executed");
  setTimeout(function() {
    console.log("calling cb 1");
    cb();
  }, 500);
});
pend.go(function(cb) {
  console.log("this function is also immediately executed");
  setTimeout(function() {
    console.log("calling cb 2");
    cb();
  }, 1000);
});
pend.wait(function(err) {
  console.log("this is excuted when the first 2 have returned.");
  console.log("err is a possible error in the standard callback style.");
});
```

Output:

```
this function is immediately executed
this function is also immediately executed
calling cb 1
calling cb 2
this is excuted when the first 2 have returned.
err is a possible error in the standard callback style.
```
