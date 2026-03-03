get-uri
=======
### Returns a `stream.Readable` from a URI string

This high-level module accepts a URI string and returns a `Readable` stream
instance. There is built-in support for a variety of "protocols", and it's
easily extensible with more:

| Protocol  | Description                     | Example
|:---------:|:-------------------------------:|:---------------------------------:
| `data`    | [Data URIs][data]               | `data:text/plain;base64,SGVsbG8sIFdvcmxkIQ%3D%3D`
| `file`    | [File URIs][file]               | `file:///c:/windows/example.ini`
| `ftp`     | [FTP URIs][ftp]                 | `ftp://ftp.kernel.org/pub/site/README`
| `http`    | [HTTP URIs][http]               | `http://www.example.com/path/to/name`
| `https`   | [HTTPS URIs][https]             | `https://www.example.com/path/to/name`

Example
-------

To simply get a `stream.Readable` instance from a `file:` URI, try something like:

```ts
import { getUri } from 'get-uri';

// `file:` maps to a `fs.ReadStream` instance…
const stream = await getUri('file:///Users/nrajlich/wat.json');
stream.pipe(process.stdout);
```


Missing Endpoints
-----------------

When you pass in a URI in which the resource referenced does not exist on the
destination server, then a `NotFoundError` will be thrown. The `code` of the
error instance is set to `"ENOTFOUND"`, so you can check for that value
to detect when a bad filename is requested:

```ts
try {
  await getUri('http://example.com/resource.json');
} catch (err) {
  if (err.code === 'ENOTFOUND') {
    // bad file path requested
  } else {
    // something else bad happened...
    throw err;
  }
}
```


Cacheability
------------

When calling `getUri()` with the same URI multiple times, the `get-uri` module
supports sending an indicator that the remote resource has not been modified
since the last time it has been retrieved from that node process.

To do this, define a `cache` property on the "options object" argument
with the value set to the `stream.Readable` instance that was previously
returned. If the remote resource has not been changed since the last call for
that same URI, then a `NotModifiedError` instance will be thrown with its
`code` property set to `"ENOTMODIFIED"`.

When the `"ENOTMODIFIED"` error occurs, then you can safely re-use the
results from the previous `getUri()` call for that same URI:

``` js
// First time fetches for real
const stream = await getUri('http://example.com/resource.json');

try {
  // … some time later, if you need to get this same URI again, pass in the
  // previous `stream.Readable` instance as `cache` option to potentially
  // have an "ENOTMODIFIED" error thrown:
  await getUri('http://example.com/resource.json', { cache: stream });
} catch (err) {
  if (err.code === 'ENOTMODIFIED') {
    // source file has not been modified since last time it was requested,
    // so you are expected to re-use results from a previous call to `getUri()`
  } else {
    // something else bad happened...
    throw err;
  }
}
```


API
---

### getUri(uri: string | URL, options?: Object]): Promise<Readable>

A `uri` is required. An optional `options` object may be passed in:

 - `cache` - A `stream.Readable` instance from a previous call to `getUri()` with the same URI. If this option is passed in, and the destination endpoint has not been modified, then an `ENOTMODIFIED` error is thrown

Any other options passed in to the `options` object will be passed through
to the low-level connection creation functions (`http.get()`, `ftp.connect()`,
etc).

Returns a `stream.Readable` instance to read the resource at the given `uri`.

[data]: http://tools.ietf.org/html/rfc2397
[file]: http://tools.ietf.org/html/draft-hoffman-file-uri-03
[ftp]: http://www.w3.org/Protocols/rfc959/
[http]: http://www.w3.org/Protocols/rfc2616/rfc2616.html
[https]: http://wikipedia.org/wiki/HTTP_Secure
