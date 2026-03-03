# buffer-crc32

[![Build Status](https://secure.travis-ci.org/brianloveswords/buffer-crc32.png?branch=master)](http://travis-ci.org/brianloveswords/buffer-crc32)

crc32 that works with binary data and fancy character sets, outputs
buffer, signed or unsigned data and has tests.

Derived from the sample CRC implementation in the PNG specification: http://www.w3.org/TR/PNG/#D-CRCAppendix

# install
```
npm install buffer-crc32
```

# example
```js
var crc32 = require('buffer-crc32');
// works with buffers
var buf = Buffer([0x00, 0x73, 0x75, 0x70, 0x20, 0x62, 0x72, 0x6f, 0x00])
crc32(buf) // -> <Buffer 94 5a ab 4a>

// has convenience methods for getting signed or unsigned ints
crc32.signed(buf) // -> -1805997238
crc32.unsigned(buf) // -> 2488970058

// will cast to buffer if given a string, so you can
// directly use foreign characters safely
crc32('自動販売機') // -> <Buffer cb 03 1a c5>

// and works in append mode too
var partialCrc = crc32('hey');
var partialCrc = crc32(' ', partialCrc);
var partialCrc = crc32('sup', partialCrc);
var partialCrc = crc32(' ', partialCrc);
var finalCrc = crc32('bros', partialCrc); // -> <Buffer 47 fa 55 70>
```

# tests
This was tested against the output of zlib's crc32 method. You can run
the tests with`npm test` (requires tap)

# see also
https://github.com/alexgorbatchev/node-crc, `crc.buffer.crc32` also
supports buffer inputs and return unsigned ints (thanks @tjholowaychuk).

# license
MIT/X11
