# fd-slicer

[![Build Status](https://travis-ci.org/andrewrk/node-fd-slicer.svg?branch=master)](https://travis-ci.org/andrewrk/node-fd-slicer)

Safe `fs.ReadStream` and `fs.WriteStream` using the same fd.

Let's say that you want to perform a parallel upload of a file to a remote
server. To do this, we want to create multiple read streams. The first thing
you might think of is to use the `{start: 0, end: 0}` API of
`fs.createReadStream`. This gives you two choices:

 0. Use the same file descriptor for all `fs.ReadStream` objects.
 0. Open the file multiple times, resulting in a separate file descriptor
    for each read stream.

Neither of these are acceptable options. The first one is a severe bug,
because the API docs for `fs.write` state:

> Note that it is unsafe to use `fs.write` multiple times on the same file
> without waiting for the callback. For this scenario, `fs.createWriteStream`
> is strongly recommended.

`fs.createWriteStream` will solve the problem if you only create one of them
for the file descriptor, but it will exhibit this unsafety if you create
multiple write streams per file descriptor.

The second option suffers from a race condition. For each additional time the
file is opened after the first, it is possible that the file is modified. So
in our parallel uploading example, we might upload a corrupt file that never
existed on the client's computer.

This module solves this problem by providing `createReadStream` and
`createWriteStream` that operate on a shared file descriptor and provides
the convenient stream API while still allowing slicing and dicing.

This module also gives you some additional power that the builtin
`fs.createWriteStream` do not give you. These features are:

 * Emitting a 'progress' event on write.
 * Ability to set a maximum size and emit an error if this size is exceeded.
 * Ability to create an `FdSlicer` instance from a `Buffer`. This enables you
   to provide API for handling files as well as buffers using the same API.

## Usage

```js
var fdSlicer = require('fd-slicer');
var fs = require('fs');

fs.open("file.txt", 'r', function(err, fd) {
  if (err) throw err;
  var slicer = fdSlicer.createFromFd(fd);
  var firstPart = slicer.createReadStream({start: 0, end: 100});
  var secondPart = slicer.createReadStream({start: 100});
  var firstOut = fs.createWriteStream("first.txt");
  var secondOut = fs.createWriteStream("second.txt");
  firstPart.pipe(firstOut);
  secondPart.pipe(secondOut);
});
```

You can also create from a buffer:

```js
var fdSlicer = require('fd-slicer');
var slicer = FdSlicer.createFromBuffer(someBuffer);
var firstPart = slicer.createReadStream({start: 0, end: 100});
var secondPart = slicer.createReadStream({start: 100});
var firstOut = fs.createWriteStream("first.txt");
var secondOut = fs.createWriteStream("second.txt");
firstPart.pipe(firstOut);
secondPart.pipe(secondOut);
```

## API Documentation

### fdSlicer.createFromFd(fd, [options])

```js
var fdSlicer = require('fd-slicer');
fs.open("file.txt", 'r', function(err, fd) {
  if (err) throw err;
  var slicer = fdSlicer.createFromFd(fd);
  // ...
});
```

Make sure `fd` is a properly initialized file descriptor. If you want to
use `createReadStream` make sure you open it for reading and if you want
to use `createWriteStream` make sure you open it for writing.

`options` is an optional object which can contain:

 * `autoClose` - if set to `true`, the file descriptor will be automatically
   closed once the last stream that references it is closed. Defaults to
   `false`. `ref()` and `unref()` can be used to increase or decrease the
   reference count, respectively.

### fdSlicer.createFromBuffer(buffer, [options])

```js
var fdSlicer = require('fd-slicer');
var slicer = fdSlicer.createFromBuffer(someBuffer);
// ...
```

`options` is an optional object which can contain:

 * `maxChunkSize` - A `Number` of bytes. see `createReadStream()`.
   If falsey, defaults to unlimited.

#### Properties

##### fd

The file descriptor passed in. `undefined` if created from a buffer.

#### Methods

##### createReadStream(options)

Available `options`:

 * `start` - Number. The offset into the file to start reading from. Defaults
   to 0.
 * `end` - Number. Exclusive upper bound offset into the file to stop reading
   from.
 * `highWaterMark` - Number. The maximum number of bytes to store in the
   internal buffer before ceasing to read from the underlying resource.
   Defaults to 16 KB.
 * `encoding` - String. If specified, then buffers will be decoded to strings
   using the specified encoding. Defaults to `null`.

The ReadableStream that this returns has these additional methods:

 * `destroy(err)` - stop streaming. `err` is optional and is the error that
   will be emitted in order to cause the streaming to stop. Defaults to
   `new Error("stream destroyed")`.

If `maxChunkSize` was specified (see `createFromBuffer()`), the read stream
will provide chunks of at most that size. Normally, the read stream provides
the entire range requested in a single chunk, but this can cause performance
problems in some circumstances.
See [thejoshwolfe/yauzl#87](https://github.com/thejoshwolfe/yauzl/issues/87).

##### createWriteStream(options)

Available `options`:

 * `start` - Number. The offset into the file to start writing to. Defaults to
   0.
 * `end` - Number. Exclusive upper bound offset into the file. If this offset
   is reached, the write stream will emit an 'error' event and stop functioning.
   In this situation, `err.code === 'ETOOBIG'`. Defaults to `Infinity`.
 * `highWaterMark` - Number. Buffer level when `write()` starts returning
   false. Defaults to 16KB.
 * `decodeStrings` - Boolean. Whether or not to decode strings into Buffers
   before passing them to` _write()`. Defaults to `true`.

The WritableStream that this returns has these additional methods:

 * `destroy()` - stop streaming

And these additional properties:

 * `bytesWritten` - number of bytes written to the stream

And these additional events:

 * 'progress' - emitted when `bytesWritten` changes.

##### read(buffer, offset, length, position, callback)

Equivalent to `fs.read`, but with concurrency protection.
`callback` must be defined.

##### write(buffer, offset, length, position, callback)

Equivalent to `fs.write`, but with concurrency protection.
`callback` must be defined.

##### ref()

Increase the `autoClose` reference count by 1.

##### unref()

Decrease the `autoClose` reference count by 1.

#### Events

##### 'error'

Emitted if `fs.close` returns an error when auto closing.

##### 'close'

Emitted when fd-slicer closes the file descriptor due to `autoClose`. Never
emitted if created from a buffer.
