data-uri-to-buffer
==================
### Create an ArrayBuffer instance from a [Data URI][rfc] string

This module accepts a ["data" URI][rfc] String of data, and returns
an `ArrayBuffer` instance with the decoded data.

This module is intended to work on a large variety of JavaScript
runtimes, including Node.js and web browsers.

Example
-------

```typescript
import { dataUriToBuffer } from 'data-uri-to-buffer';

// plain-text data is supported
let uri = 'data:,Hello%2C%20World!';
let parsed = dataUriToBuffer(uri);
console.log(new TextDecoder().decode(parsed.buffer));
// 'Hello, World!'

// base64-encoded data is supported
uri = 'data:text/plain;base64,SGVsbG8sIFdvcmxkIQ%3D%3D';
parsed = dataUriToBuffer(uri);
console.log(new TextDecoder().decode(parsed.buffer));
// 'Hello, World!'
```


API
---

```typescript
export interface ParsedDataURI {
	type: string;
	typeFull: string;
	charset: string;
	buffer: ArrayBuffer;
}
```

### dataUriToBuffer(uri: string | URL) → ParsedDataURI

The `type` property gets set to the main type portion of
the "mediatype" portion of the "data" URI, or defaults to `"text/plain"` if not
specified.

The `typeFull` property gets set to the entire
"mediatype" portion of the "data" URI (including all parameters), or defaults
to `"text/plain;charset=US-ASCII"` if not specified.

The `charset` property gets set to the Charset portion of
the "mediatype" portion of the "data" URI, or defaults to `"US-ASCII"` if the
entire type is not specified, or defaults to `""` otherwise.

*Note*: If only the main type is specified but not the charset, e.g.
`"data:text/plain,abc"`, the charset is set to the empty string. The spec only
defaults to US-ASCII as charset if the entire type is not specified.

[rfc]: http://tools.ietf.org/html/rfc2397
