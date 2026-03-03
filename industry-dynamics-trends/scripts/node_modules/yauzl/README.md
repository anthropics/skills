# yauzl

[![Build Status](https://travis-ci.org/thejoshwolfe/yauzl.svg?branch=master)](https://travis-ci.org/thejoshwolfe/yauzl)
[![Coverage Status](https://img.shields.io/coveralls/thejoshwolfe/yauzl.svg)](https://coveralls.io/r/thejoshwolfe/yauzl)

yet another unzip library for node. For zipping, see
[yazl](https://github.com/thejoshwolfe/yazl).

Design principles:

 * Follow the spec.
   Don't scan for local file headers.
   Read the central directory for file metadata.
   (see [No Streaming Unzip API](#no-streaming-unzip-api)).
 * Don't block the JavaScript thread.
   Use and provide async APIs.
 * Keep memory usage under control.
   Don't attempt to buffer entire files in RAM at once.
 * Never crash (if used properly).
   Don't let malformed zip files bring down client applications who are trying to catch errors.
 * Catch unsafe file names.
   See `validateFileName()`.

## Usage

```js
var yauzl = require("yauzl");

yauzl.open("path/to/file.zip", {lazyEntries: true}, function(err, zipfile) {
  if (err) throw err;
  zipfile.readEntry();
  zipfile.on("entry", function(entry) {
    if (/\/$/.test(entry.fileName)) {
      // Directory file names end with '/'.
      // Note that entires for directories themselves are optional.
      // An entry's fileName implicitly requires its parent directories to exist.
      zipfile.readEntry();
    } else {
      // file entry
      zipfile.openReadStream(entry, function(err, readStream) {
        if (err) throw err;
        readStream.on("end", function() {
          zipfile.readEntry();
        });
        readStream.pipe(somewhere);
      });
    }
  });
});
```

See also `examples/` for more usage examples.

## API

The default for every optional `callback` parameter is:

```js
function defaultCallback(err) {
  if (err) throw err;
}
```

### open(path, [options], [callback])

Calls `fs.open(path, "r")` and reads the `fd` effectively the same as `fromFd()` would.

`options` may be omitted or `null`. The defaults are `{autoClose: true, lazyEntries: false, decodeStrings: true, validateEntrySizes: true, strictFileNames: false}`.

`autoClose` is effectively equivalent to:

```js
zipfile.once("end", function() {
  zipfile.close();
});
```

`lazyEntries` indicates that entries should be read only when `readEntry()` is called.
If `lazyEntries` is `false`, `entry` events will be emitted as fast as possible to allow `pipe()`ing
file data from all entries in parallel.
This is not recommended, as it can lead to out of control memory usage for zip files with many entries.
See [issue #22](https://github.com/thejoshwolfe/yauzl/issues/22).
If `lazyEntries` is `true`, an `entry` or `end` event will be emitted in response to each call to `readEntry()`.
This allows processing of one entry at a time, and will keep memory usage under control for zip files with many entries.

`decodeStrings` is the default and causes yauzl to decode strings with `CP437` or `UTF-8` as required by the spec.
The exact effects of turning this option off are:

* `zipfile.comment`, `entry.fileName`, and `entry.fileComment` will be `Buffer` objects instead of `String`s.
* Any Info-ZIP Unicode Path Extra Field will be ignored. See `extraFields`.
* Automatic file name validation will not be performed. See `validateFileName()`.

`validateEntrySizes` is the default and ensures that an entry's reported uncompressed size matches its actual uncompressed size.
This check happens as early as possible, which is either before emitting each `"entry"` event (for entries with no compression),
or during the `readStream` piping after calling `openReadStream()`.
See `openReadStream()` for more information on defending against zip bomb attacks.

When `strictFileNames` is `false` (the default) and `decodeStrings` is `true`,
all backslash (`\`) characters in each `entry.fileName` are replaced with forward slashes (`/`).
The spec forbids file names with backslashes,
but Microsoft's `System.IO.Compression.ZipFile` class in .NET versions 4.5.0 until 4.6.1
creates non-conformant zipfiles with backslashes in file names.
`strictFileNames` is `false` by default so that clients can read these
non-conformant zipfiles without knowing about this Microsoft-specific bug.
When `strictFileNames` is `true` and `decodeStrings` is `true`,
entries with backslashes in their file names will result in an error. See `validateFileName()`.
When `decodeStrings` is `false`, `strictFileNames` has no effect.

The `callback` is given the arguments `(err, zipfile)`.
An `err` is provided if the End of Central Directory Record cannot be found, or if its metadata appears malformed.
This kind of error usually indicates that this is not a zip file.
Otherwise, `zipfile` is an instance of `ZipFile`.

### fromFd(fd, [options], [callback])

Reads from the fd, which is presumed to be an open .zip file.
Note that random access is required by the zip file specification,
so the fd cannot be an open socket or any other fd that does not support random access.

`options` may be omitted or `null`. The defaults are `{autoClose: false, lazyEntries: false, decodeStrings: true, validateEntrySizes: true, strictFileNames: false}`.

See `open()` for the meaning of the options and callback.

### fromBuffer(buffer, [options], [callback])

Like `fromFd()`, but reads from a RAM buffer instead of an open file.
`buffer` is a `Buffer`.

If a `ZipFile` is acquired from this method,
it will never emit the `close` event,
and calling `close()` is not necessary.

`options` may be omitted or `null`. The defaults are `{lazyEntries: false, decodeStrings: true, validateEntrySizes: true, strictFileNames: false}`.

See `open()` for the meaning of the options and callback.
The `autoClose` option is ignored for this method.

### fromRandomAccessReader(reader, totalSize, [options], [callback])

This method of reading a zip file allows clients to implement their own back-end file system.
For example, a client might translate read calls into network requests.

The `reader` parameter must be of a type that is a subclass of
[RandomAccessReader](#class-randomaccessreader) that implements the required methods.
The `totalSize` is a Number and indicates the total file size of the zip file.

`options` may be omitted or `null`. The defaults are `{autoClose: true, lazyEntries: false, decodeStrings: true, validateEntrySizes: true, strictFileNames: false}`.

See `open()` for the meaning of the options and callback.

### dosDateTimeToDate(date, time)

Converts MS-DOS `date` and `time` data into a JavaScript `Date` object.
Each parameter is a `Number` treated as an unsigned 16-bit integer.
Note that this format does not support timezones,
so the returned object will use the local timezone.

### validateFileName(fileName)

Returns `null` or a `String` error message depending on the validity of `fileName`.
If `fileName` starts with `"/"` or `/[A-Za-z]:\//` or if it contains `".."` path segments or `"\\"`,
this function returns an error message appropriate for use like this:

```js
var errorMessage = yauzl.validateFileName(fileName);
if (errorMessage != null) throw new Error(errorMessage);
```

This function is automatically run for each entry, as long as `decodeStrings` is `true`.
See `open()`, `strictFileNames`, and `Event: "entry"` for more information.

### Class: ZipFile

The constructor for the class is not part of the public API.
Use `open()`, `fromFd()`, `fromBuffer()`, or `fromRandomAccessReader()` instead.

#### Event: "entry"

Callback gets `(entry)`, which is an `Entry`.
See `open()` and `readEntry()` for when this event is emitted.

If `decodeStrings` is `true`, entries emitted via this event have already passed file name validation.
See `validateFileName()` and `open()` for more information.

If `validateEntrySizes` is `true` and this entry's `compressionMethod` is `0` (stored without compression),
this entry has already passed entry size validation.
See `open()` for more information.

#### Event: "end"

Emitted after the last `entry` event has been emitted.
See `open()` and `readEntry()` for more info on when this event is emitted.

#### Event: "close"

Emitted after the fd is actually closed.
This is after calling `close()` (or after the `end` event when `autoClose` is `true`),
and after all stream pipelines created from `openReadStream()` have finished reading data from the fd.

If this `ZipFile` was acquired from `fromRandomAccessReader()`,
the "fd" in the previous paragraph refers to the `RandomAccessReader` implemented by the client.

If this `ZipFile` was acquired from `fromBuffer()`, this event is never emitted.

#### Event: "error"

Emitted in the case of errors with reading the zip file.
(Note that other errors can be emitted from the streams created from `openReadStream()` as well.)
After this event has been emitted, no further `entry`, `end`, or `error` events will be emitted,
but the `close` event may still be emitted.

#### readEntry()

Causes this `ZipFile` to emit an `entry` or `end` event (or an `error` event).
This method must only be called when this `ZipFile` was created with the `lazyEntries` option set to `true` (see `open()`).
When this `ZipFile` was created with the `lazyEntries` option set to `true`,
`entry` and `end` events are only ever emitted in response to this method call.

The event that is emitted in response to this method will not be emitted until after this method has returned,
so it is safe to call this method before attaching event listeners.

After calling this method, calling this method again before the response event has been emitted will cause undefined behavior.
Calling this method after the `end` event has been emitted will cause undefined behavior.
Calling this method after calling `close()` will cause undefined behavior.

#### openReadStream(entry, [options], callback)

`entry` must be an `Entry` object from this `ZipFile`.
`callback` gets `(err, readStream)`, where `readStream` is a `Readable Stream` that provides the file data for this entry.
If this zipfile is already closed (see `close()`), the `callback` will receive an `err`.

`options` may be omitted or `null`, and has the following defaults:

```js
{
  decompress: entry.isCompressed() ? true : null,
  decrypt: null,
  start: 0,                  // actually the default is null, see below
  end: entry.compressedSize, // actually the default is null, see below
}
```

If the entry is compressed (with a supported compression method),
and the `decompress` option is `true` (or omitted),
the read stream provides the decompressed data.
Omitting the `decompress` option is what most clients should do.

The `decompress` option must be `null` (or omitted) when the entry is not compressed (see `isCompressed()`),
and either `true` (or omitted) or `false` when the entry is compressed.
Specifying `decompress: false` for a compressed entry causes the read stream
to provide the raw compressed file data without going through a zlib inflate transform.

If the entry is encrypted (see `isEncrypted()`), clients may want to avoid calling `openReadStream()` on the entry entirely.
Alternatively, clients may call `openReadStream()` for encrypted entries and specify `decrypt: false`.
If the entry is also compressed, clients must *also* specify `decompress: false`.
Specifying `decrypt: false` for an encrypted entry causes the read stream to provide the raw, still-encrypted file data.
(This data includes the 12-byte header described in the spec.)

The `decrypt` option must be `null` (or omitted) for non-encrypted entries, and `false` for encrypted entries.
Omitting the `decrypt` option (or specifying it as `null`) for an encrypted entry
will result in the `callback` receiving an `err`.
This default behavior is so that clients not accounting for encrypted files aren't surprised by bogus file data.

The `start` (inclusive) and `end` (exclusive) options are byte offsets into this entry's file data,
and can be used to obtain part of an entry's file data rather than the whole thing.
If either of these options are specified and non-`null`,
then the above options must be used to obain the file's raw data.
Speficying `{start: 0, end: entry.compressedSize}` will result in the complete file,
which is effectively the default values for these options,
but note that unlike omitting the options, when you specify `start` or `end` as any non-`null` value,
the above requirement is still enforced that you must also pass the appropriate options to get the file's raw data.

It's possible for the `readStream` provided to the `callback` to emit errors for several reasons.
For example, if zlib cannot decompress the data, the zlib error will be emitted from the `readStream`.
Two more error cases (when `validateEntrySizes` is `true`) are if the decompressed data has too many
or too few actual bytes compared to the reported byte count from the entry's `uncompressedSize` field.
yauzl notices this false information and emits an error from the `readStream`
after some number of bytes have already been piped through the stream.

This check allows clients to trust the `uncompressedSize` field in `Entry` objects.
Guarding against [zip bomb](http://en.wikipedia.org/wiki/Zip_bomb) attacks can be accomplished by
doing some heuristic checks on the size metadata and then watching out for the above errors.
Such heuristics are outside the scope of this library,
but enforcing the `uncompressedSize` is implemented here as a security feature.

It is possible to destroy the `readStream` before it has piped all of its data.
To do this, call `readStream.destroy()`.
You must `unpipe()` the `readStream` from any destination before calling `readStream.destroy()`.
If this zipfile was created using `fromRandomAccessReader()`, the `RandomAccessReader` implementation
must provide readable streams that implement a `.destroy()` method (see `randomAccessReader._readStreamForRange()`)
in order for calls to `readStream.destroy()` to work in this context.

#### close()

Causes all future calls to `openReadStream()` to fail,
and closes the fd, if any, after all streams created by `openReadStream()` have emitted their `end` events.

If the `autoClose` option is set to `true` (see `open()`),
this function will be called automatically effectively in response to this object's `end` event.

If the `lazyEntries` option is set to `false` (see `open()`) and this object's `end` event has not been emitted yet,
this function causes undefined behavior.
If the `lazyEntries` option is set to `true`,
you can call this function instead of calling `readEntry()` to abort reading the entries of a zipfile.

It is safe to call this function multiple times; after the first call, successive calls have no effect.
This includes situations where the `autoClose` option effectively calls this function for you.

If `close()` is never called, then the zipfile is "kept open".
For zipfiles created with `fromFd()`, this will leave the `fd` open, which may be desirable.
For zipfiles created with `open()`, this will leave the underlying `fd` open, thereby "leaking" it, which is probably undesirable.
For zipfiles created with `fromRandomAccessReader()`, the reader's `close()` method will never be called.
For zipfiles created with `fromBuffer()`, the `close()` function has no effect whether called or not.

Regardless of how this `ZipFile` was created, there are no resources other than those listed above that require cleanup from this function.
This means it may be desirable to never call `close()` in some usecases.

#### isOpen

`Boolean`. `true` until `close()` is called; then it's `false`.

#### entryCount

`Number`. Total number of central directory records.

#### comment

`String`. Always decoded with `CP437` per the spec.

If `decodeStrings` is `false` (see `open()`), this field is the undecoded `Buffer` instead of a decoded `String`.

### Class: Entry

Objects of this class represent Central Directory Records.
Refer to the zipfile specification for more details about these fields.

These fields are of type `Number`:

 * `versionMadeBy`
 * `versionNeededToExtract`
 * `generalPurposeBitFlag`
 * `compressionMethod`
 * `lastModFileTime` (MS-DOS format, see `getLastModDateTime`)
 * `lastModFileDate` (MS-DOS format, see `getLastModDateTime`)
 * `crc32`
 * `compressedSize`
 * `uncompressedSize`
 * `fileNameLength` (bytes)
 * `extraFieldLength` (bytes)
 * `fileCommentLength` (bytes)
 * `internalFileAttributes`
 * `externalFileAttributes`
 * `relativeOffsetOfLocalHeader`

#### fileName

`String`.
Following the spec, the bytes for the file name are decoded with
`UTF-8` if `generalPurposeBitFlag & 0x800`, otherwise with `CP437`.
Alternatively, this field may be populated from the Info-ZIP Unicode Path Extra Field
(see `extraFields`).

This field is automatically validated by `validateFileName()` before yauzl emits an "entry" event.
If this field would contain unsafe characters, yauzl emits an error instead of an entry.

If `decodeStrings` is `false` (see `open()`), this field is the undecoded `Buffer` instead of a decoded `String`.
Therefore, `generalPurposeBitFlag` and any Info-ZIP Unicode Path Extra Field are ignored.
Furthermore, no automatic file name validation is performed for this file name.

#### extraFields

`Array` with each entry in the form `{id: id, data: data}`,
where `id` is a `Number` and `data` is a `Buffer`.

This library looks for and reads the ZIP64 Extended Information Extra Field (0x0001)
in order to support ZIP64 format zip files.

This library also looks for and reads the Info-ZIP Unicode Path Extra Field (0x7075)
in order to support some zipfiles that use it instead of General Purpose Bit 11
to convey `UTF-8` file names.
When the field is identified and verified to be reliable (see the zipfile spec),
the the file name in this field is stored in the `fileName` property,
and the file name in the central directory record for this entry is ignored.
Note that when `decodeStrings` is false, all Info-ZIP Unicode Path Extra Fields are ignored.

None of the other fields are considered significant by this library.
Fields that this library reads are left unalterned in the `extraFields` array.

#### fileComment

`String` decoded with the charset indicated by `generalPurposeBitFlag & 0x800` as with the `fileName`.
(The Info-ZIP Unicode Path Extra Field has no effect on the charset used for this field.)

If `decodeStrings` is `false` (see `open()`), this field is the undecoded `Buffer` instead of a decoded `String`.

Prior to yauzl version 2.7.0, this field was erroneously documented as `comment` instead of `fileComment`.
For compatibility with any code that uses the field name `comment`,
yauzl creates an alias field named `comment` which is identical to `fileComment`.

#### getLastModDate()

Effectively implemented as:

```js
return dosDateTimeToDate(this.lastModFileDate, this.lastModFileTime);
```

#### isEncrypted()

Returns is this entry encrypted with "Traditional Encryption".
Effectively implemented as:

```js
return (this.generalPurposeBitFlag & 0x1) !== 0;
```

See `openReadStream()` for the implications of this value.

Note that "Strong Encryption" is not supported, and will result in an `"error"` event emitted from the `ZipFile`.

#### isCompressed()

Effectively implemented as:

```js
return this.compressionMethod === 8;
```

See `openReadStream()` for the implications of this value.

### Class: RandomAccessReader

This class is meant to be subclassed by clients and instantiated for the `fromRandomAccessReader()` function.

An example implementation can be found in `test/test.js`.

#### randomAccessReader._readStreamForRange(start, end)

Subclasses *must* implement this method.

`start` and `end` are Numbers and indicate byte offsets from the start of the file.
`end` is exclusive, so `_readStreamForRange(0x1000, 0x2000)` would indicate to read `0x1000` bytes.
`end - start` will always be at least `1`.

This method should return a readable stream which will be `pipe()`ed into another stream.
It is expected that the readable stream will provide data in several chunks if necessary.
If the readable stream provides too many or too few bytes, an error will be emitted.
(Note that `validateEntrySizes` has no effect on this check,
because this is a low-level API that should behave correctly regardless of the contents of the file.)
Any errors emitted on the readable stream will be handled and re-emitted on the client-visible stream
(returned from `zipfile.openReadStream()`) or provided as the `err` argument to the appropriate callback
(for example, for `fromRandomAccessReader()`).

The returned stream *must* implement a method `.destroy()`
if you call `readStream.destroy()` on streams you get from `openReadStream()`.
If you never call `readStream.destroy()`, then streams returned from this method do not need to implement a method `.destroy()`.
`.destroy()` should abort any streaming that is in progress and clean up any associated resources.
`.destroy()` will only be called after the stream has been `unpipe()`d from its destination.

Note that the stream returned from this method might not be the same object that is provided by `openReadStream()`.
The stream returned from this method might be `pipe()`d through one or more filter streams (for example, a zlib inflate stream).

#### randomAccessReader.read(buffer, offset, length, position, callback)

Subclasses may implement this method.
The default implementation uses `createReadStream()` to fill the `buffer`.

This method should behave like `fs.read()`.

#### randomAccessReader.close(callback)

Subclasses may implement this method.
The default implementation is effectively `setImmediate(callback);`.

`callback` takes parameters `(err)`.

This method is called once the all streams returned from `_readStreamForRange()` have ended,
and no more `_readStreamForRange()` or `read()` requests will be issued to this object.

## How to Avoid Crashing

When a malformed zipfile is encountered, the default behavior is to crash (throw an exception).
If you want to handle errors more gracefully than this,
be sure to do the following:

 * Provide `callback` parameters where they are allowed, and check the `err` parameter.
 * Attach a listener for the `error` event on any `ZipFile` object you get from `open()`, `fromFd()`, `fromBuffer()`, or `fromRandomAccessReader()`.
 * Attach a listener for the `error` event on any stream you get from `openReadStream()`.

Minor version updates to yauzl will not add any additional requirements to this list.

## Limitations

### No Streaming Unzip API

Due to the design of the .zip file format, it's impossible to interpret a .zip file from start to finish
(such as from a readable stream) without sacrificing correctness.
The Central Directory, which is the authority on the contents of the .zip file, is at the end of a .zip file, not the beginning.
A streaming API would need to either buffer the entire .zip file to get to the Central Directory before interpreting anything
(defeating the purpose of a streaming interface), or rely on the Local File Headers which are interspersed through the .zip file.
However, the Local File Headers are explicitly denounced in the spec as being unreliable copies of the Central Directory,
so trusting them would be a violation of the spec.

Any library that offers a streaming unzip API must make one of the above two compromises,
which makes the library either dishonest or nonconformant (usually the latter).
This library insists on correctness and adherence to the spec, and so does not offer a streaming API.

Here is a way to create a spec-conformant .zip file using the `zip` command line program (Info-ZIP)
available in most unix-like environments, that is (nearly) impossible to parse correctly with a streaming parser:

```
$ echo -ne '\x50\x4b\x07\x08\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00' > file.txt
$ zip -q0 - file.txt | cat > out.zip
```

This .zip file contains a single file entry that uses General Purpose Bit 3,
which means the Local File Header doesn't know the size of the file.
Any streaming parser that encounters this situation will either immediately fail,
or attempt to search for the Data Descriptor after the file's contents.
The file's contents is a sequence of 16-bytes crafted to exactly mimic a valid Data Descriptor for an empty file,
which will fool any parser that gets this far into thinking that the file is empty rather than containing 16-bytes.
What follows the file's real contents is the file's real Data Descriptor,
which will likely cause some kind of signature mismatch error for a streaming parser (if one hasn't occurred already).

By using General Purpose Bit 3 (and compression method 0),
it's possible to create arbitrarily ambiguous .zip files that
distract parsers with file contents that contain apparently valid .zip file metadata.

### Limitted ZIP64 Support

For ZIP64, only zip files smaller than `8PiB` are supported,
not the full `16EiB` range that a 64-bit integer should be able to index.
This is due to the JavaScript Number type being an IEEE 754 double precision float.

The Node.js `fs` module probably has this same limitation.

### ZIP64 Extensible Data Sector Is Ignored

The spec does not allow zip file creators to put arbitrary data here,
but rather reserves its use for PKWARE and mentions something about Z390.
This doesn't seem useful to expose in this library, so it is ignored.

### No Multi-Disk Archive Support

This library does not support multi-disk zip files.
The multi-disk fields in the zipfile spec were intended for a zip file to span multiple floppy disks,
which probably never happens now.
If the "number of this disk" field in the End of Central Directory Record is not `0`,
the `open()`, `fromFd()`, `fromBuffer()`, or `fromRandomAccessReader()` `callback` will receive an `err`.
By extension the following zip file fields are ignored by this library and not provided to clients:

 * Disk where central directory starts
 * Number of central directory records on this disk
 * Disk number where file starts

### Limited Encryption Handling

You can detect when a file entry is encrypted with "Traditional Encryption" via `isEncrypted()`,
but yauzl will not help you decrypt it.
See `openReadStream()`.

If a zip file contains file entries encrypted with "Strong Encryption", yauzl emits an error.

If the central directory is encrypted or compressed, yauzl emits an error.

### Local File Headers Are Ignored

Many unzip libraries mistakenly read the Local File Header data in zip files.
This data is officially defined to be redundant with the Central Directory information,
and is not to be trusted.
Aside from checking the signature, yauzl ignores the content of the Local File Header.

### No CRC-32 Checking

This library provides the `crc32` field of `Entry` objects read from the Central Directory.
However, this field is not used for anything in this library.

### versionNeededToExtract Is Ignored

The field `versionNeededToExtract` is ignored,
because this library doesn't support the complete zip file spec at any version,

### No Support For Obscure Compression Methods

Regarding the `compressionMethod` field of `Entry` objects,
only method `0` (stored with no compression)
and method `8` (deflated) are supported.
Any of the other 15 official methods will cause the `openReadStream()` `callback` to receive an `err`.

### Data Descriptors Are Ignored

There may or may not be Data Descriptor sections in a zip file.
This library provides no support for finding or interpreting them.

### Archive Extra Data Record Is Ignored

There may or may not be an Archive Extra Data Record section in a zip file.
This library provides no support for finding or interpreting it.

### No Language Encoding Flag Support

Zip files officially support charset encodings other than CP437 and UTF-8,
but the zip file spec does not specify how it works.
This library makes no attempt to interpret the Language Encoding Flag.

## Change History

 * 2.10.0
   * Added support for non-conformant zipfiles created by Microsoft, and added option `strictFileNames` to disable the workaround. [issue #66](https://github.com/thejoshwolfe/yauzl/issues/66), [issue #88](https://github.com/thejoshwolfe/yauzl/issues/88)
 * 2.9.2
   * Removed `tools/hexdump-zip.js` and `tools/hex2bin.js`. Those tools are now located here: [thejoshwolfe/hexdump-zip](https://github.com/thejoshwolfe/hexdump-zip) and [thejoshwolfe/hex2bin](https://github.com/thejoshwolfe/hex2bin)
   * Worked around performance problem with zlib when using `fromBuffer()` and `readStream.destroy()` for large compressed files. [issue #87](https://github.com/thejoshwolfe/yauzl/issues/87)
 * 2.9.1
   * Removed `console.log()` accidentally introduced in 2.9.0. [issue #64](https://github.com/thejoshwolfe/yauzl/issues/64)
 * 2.9.0
   * Throw an exception if `readEntry()` is called without `lazyEntries:true`. Previously this caused undefined behavior. [issue #63](https://github.com/thejoshwolfe/yauzl/issues/63)
 * 2.8.0
   * Added option `validateEntrySizes`. [issue #53](https://github.com/thejoshwolfe/yauzl/issues/53)
   * Added `examples/promises.js`
   * Added ability to read raw file data via `decompress` and `decrypt` options. [issue #11](https://github.com/thejoshwolfe/yauzl/issues/11), [issue #38](https://github.com/thejoshwolfe/yauzl/issues/38), [pull #39](https://github.com/thejoshwolfe/yauzl/pull/39)
   * Added `start` and `end` options to `openReadStream()`. [issue #38](https://github.com/thejoshwolfe/yauzl/issues/38)
 * 2.7.0
   * Added option `decodeStrings`. [issue #42](https://github.com/thejoshwolfe/yauzl/issues/42)
   * Fixed documentation for `entry.fileComment` and added compatibility alias. [issue #47](https://github.com/thejoshwolfe/yauzl/issues/47)
 * 2.6.0
   * Support Info-ZIP Unicode Path Extra Field, used by WinRAR for Chinese file names. [issue #33](https://github.com/thejoshwolfe/yauzl/issues/33)
 * 2.5.0
   * Ignore malformed Extra Field that is common in Android .apk files. [issue #31](https://github.com/thejoshwolfe/yauzl/issues/31)
 * 2.4.3
   * Fix crash when parsing malformed Extra Field buffers. [issue #31](https://github.com/thejoshwolfe/yauzl/issues/31)
 * 2.4.2
   * Remove .npmignore and .travis.yml from npm package.
 * 2.4.1
   * Fix error handling.
 * 2.4.0
   * Add ZIP64 support. [issue #6](https://github.com/thejoshwolfe/yauzl/issues/6)
   * Add `lazyEntries` option. [issue #22](https://github.com/thejoshwolfe/yauzl/issues/22)
   * Add `readStream.destroy()` method. [issue #26](https://github.com/thejoshwolfe/yauzl/issues/26)
   * Add `fromRandomAccessReader()`. [issue #14](https://github.com/thejoshwolfe/yauzl/issues/14)
   * Add `examples/unzip.js`.
 * 2.3.1
   * Documentation updates.
 * 2.3.0
   * Check that `uncompressedSize` is correct, or else emit an error. [issue #13](https://github.com/thejoshwolfe/yauzl/issues/13)
 * 2.2.1
   * Update dependencies.
 * 2.2.0
   * Update dependencies.
 * 2.1.0
   * Remove dependency on `iconv`.
 * 2.0.3
   * Fix crash when trying to read a 0-byte file.
 * 2.0.2
   * Fix event behavior after errors.
 * 2.0.1
   * Fix bug with using `iconv`.
 * 2.0.0
   * Initial release.
