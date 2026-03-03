pac-proxy-agent
===============
### A [PAC file][pac-wikipedia] proxy `http.Agent` implementation for HTTP and HTTPS

This module provides an `http.Agent` implementation that retreives the specified
[PAC proxy file][pac-wikipedia] and uses it to resolve which HTTP, HTTPS, or
SOCKS proxy, or if a direct connection should be used to connect to the
HTTP endpoint.

It is designed to be be used with the built-in `http` and `https` modules.

Example
-------

```ts
import * as http from 'http';
import { PacProxyAgent } from 'pac-proxy-agent';

const agent = new PacProxyAgent('pac+https://cloudup.com/ceGH2yZ0Bjp+');

http.get('http://nodejs.org/api/', { agent }, (res) => {
  console.log('"response" event!', res.headers);
  res.pipe(process.stdout);
});
```

[pac-wikipedia]: http://wikipedia.org/wiki/Proxy_auto-config
