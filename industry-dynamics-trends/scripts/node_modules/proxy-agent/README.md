proxy-agent
===========
### Maps proxy protocols to `http.Agent` implementations

This module provides an `http.Agent` implementation which automatically uses
proxy servers based off of the various proxy-related environment variables
(`HTTP_PROXY`, `HTTPS_PROXY` and `NO_PROXY` among others).

Which proxy is used for each HTTP request is determined by the
[`proxy-from-env`](https://www.npmjs.com/package/proxy-from-env) module, so
check its documentation for instructions on configuring your environment variables.

An LRU cache is used so that `http.Agent` instances are transparently re-used for
subsequent HTTP requests to the same proxy server.

The currently implemented protocol mappings are listed in the table below:


| Protocol   | Proxy Agent for `http` requests | Proxy Agent for `https` requests | Example
|:----------:|:-------------------------------:|:--------------------------------:|:--------:
| `http`     | [http-proxy-agent][]            | [https-proxy-agent][]            | `http://proxy-server-over-tcp.com:3128`
| `https`    | [http-proxy-agent][]            | [https-proxy-agent][]            | `https://proxy-server-over-tls.com:3129`
| `socks(v5)`| [socks-proxy-agent][]           | [socks-proxy-agent][]            | `socks://username:password@some-socks-proxy.com:9050` (username & password are optional)
| `socks5`   | [socks-proxy-agent][]           | [socks-proxy-agent][]            | `socks5://username:password@some-socks-proxy.com:9050` (username & password are optional)
| `socks4`   | [socks-proxy-agent][]           | [socks-proxy-agent][]            | `socks4://some-socks-proxy.com:9050`
| `pac-*`    | [pac-proxy-agent][]             | [pac-proxy-agent][]              | `pac+http://www.example.com/proxy.pac`

Example
-------

```ts
import * as https from 'https';
import { ProxyAgent } from 'proxy-agent';

// The correct proxy `Agent` implementation to use will be determined
// via the `http_proxy` / `https_proxy` / `no_proxy` / etc. env vars
const agent = new ProxyAgent();

// The rest works just like any other normal HTTP request
https.get('https://jsonip.com', { agent }, (res) => {
  console.log(res.statusCode, res.headers);
  res.pipe(process.stdout);
});
```


API
---

### new ProxyAgent(options?: ProxyAgentOptions)

Creates an `http.Agent` instance which relies on the various proxy-related
environment variables. An LRU cache is used, so the same `http.Agent` instance
will be returned if identical args are passed in.

[http-proxy-agent]: ../http-proxy-agent
[https-proxy-agent]: ../https-proxy-agent
[socks-proxy-agent]: ../socks-proxy-agent
[pac-proxy-agent]: ../pac-proxy-agent
