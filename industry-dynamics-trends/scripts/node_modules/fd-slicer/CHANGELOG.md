### 1.0.1

 * use `setImmediate` instead of `nextTick`

### 1.0.0

 * `new FdSlicer(fd, options)` must now be `fdSlicer.createFromFd(fd, options)`
 * fix behavior when `end` is 0.
 * fix `createWriteStream` when using `createFromBuffer`

### 0.4.0

 * add ability to create an FdSlicer instance from a Buffer

### 0.3.2

 * fix write stream and read stream destroy behavior

### 0.3.1

 * write stream: fix end option behavior

### 0.3.0

 * write stream emits 'progress' events
 * write stream supports 'end' option which causes the stream to emit an error
   if a maximum size is exceeded
 * improve documentation

### 0.2.1

 * Update pend dependency to latest bugfix version.

### 0.2.0

 * Add read and write functions

### 0.1.0

 * Add `autoClose` option and `ref()` and `unref()`.

### 0.0.2

 * Add API documentation
 * read stream: create buffer at last possible moment

### 0.0.1

 * Initial release
