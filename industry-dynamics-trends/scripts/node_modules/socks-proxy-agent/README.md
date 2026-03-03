socks-proxy-agent
================
### A SOCKS proxy `http.Agent` implementation for HTTP and HTTPS

This module provides an `http.Agent` implementation that connects to a
specified SOCKS proxy server, and can be used with the built-in `http`
and `https` modules.

It can also be used in conjunction with the `ws` module to establish a WebSocket
connection over a SOCKS proxy. See the "Examples" section below.

Examples
--------

```ts
import https from 'https';
import { SocksProxyAgent } from 'socks-proxy-agent';

const agent = new SocksProxyAgent(
	'socks://your-name%40gmail.com:abcdef12345124@br41.nordvpn.com'
);

https.get('https://ipinfo.io', { agent }, (res) => {
	console.log(res.headers);
	res.pipe(process.stdout);
});
```

#### `ws` WebSocket connection example

```ts
import WebSocket from 'ws';
import { SocksProxyAgent } from 'socks-proxy-agent';

const agent = new SocksProxyAgent(
	'socks://your-name%40gmail.com:abcdef12345124@br41.nordvpn.com'
);

var socket = new WebSocket('ws://echo.websocket.events', { agent });

socket.on('open', function () {
	console.log('"open" event!');
	socket.send('hello world');
});

socket.on('message', function (data, flags) {
	console.log('"message" event! %j %j', data, flags);
	socket.close();
});
```