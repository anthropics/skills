import assert from "node:assert/strict";
import http from "node:http";
import net from "node:net";
import test, { type TestContext } from "node:test";

import { createSocksClient } from "./wechat-socks-http.ts";

interface EchoServer {
  baseUrl: string;
  port: number;
  received: Array<{ method: string; url: string; headers: http.IncomingHttpHeaders; body: Buffer }>;
}

async function startEchoServer(t: TestContext): Promise<EchoServer> {
  const received: EchoServer["received"] = [];
  const server = http.createServer((req, res) => {
    const chunks: Buffer[] = [];
    req.on("data", (chunk: Buffer) => chunks.push(chunk));
    req.on("end", () => {
      received.push({
        method: req.method ?? "",
        url: req.url ?? "",
        headers: req.headers,
        body: Buffer.concat(chunks),
      });
      res.statusCode = 200;
      res.setHeader("Content-Type", "application/json");
      res.end(JSON.stringify({ ok: true, url: req.url }));
    });
  });
  await new Promise<void>((resolve) => server.listen(0, "127.0.0.1", resolve));
  const address = server.address();
  if (!address || typeof address === "string") throw new Error("echo server bind failed");
  const port = address.port;
  t.after(async () => {
    await new Promise<void>((resolve) => server.close(() => resolve()));
  });
  return { baseUrl: `http://127.0.0.1:${port}`, port, received };
}

interface FakeSocks5 {
  port: number;
  connectionCount: () => number;
  destinations: () => Array<{ host: string; port: number }>;
}

async function startFakeSocks5(t: TestContext): Promise<FakeSocks5> {
  let connectionCount = 0;
  const destinations: Array<{ host: string; port: number }> = [];

  const server = net.createServer((client) => {
    connectionCount++;
    let phase: "greeting" | "request" | "tunnel" = "greeting";
    let buf = Buffer.alloc(0);
    let upstream: net.Socket | undefined;

    const tryParse = () => {
      if (phase === "greeting") {
        if (buf.length < 2) return;
        const nMethods = buf[1]!;
        if (buf.length < 2 + nMethods) return;
        buf = buf.subarray(2 + nMethods);
        client.write(Buffer.from([0x05, 0x00]));
        phase = "request";
      }
      if (phase === "request") {
        if (buf.length < 5) return;
        if (buf[0] !== 0x05 || buf[1] !== 0x01) {
          client.destroy();
          return;
        }
        const atyp = buf[3];
        let addrEnd: number;
        let host: string;
        if (atyp === 0x01) {
          if (buf.length < 4 + 4 + 2) return;
          host = `${buf[4]}.${buf[5]}.${buf[6]}.${buf[7]}`;
          addrEnd = 4 + 4;
        } else if (atyp === 0x03) {
          const dlen = buf[4]!;
          if (buf.length < 4 + 1 + dlen + 2) return;
          host = buf.subarray(5, 5 + dlen).toString("ascii");
          addrEnd = 4 + 1 + dlen;
        } else {
          client.destroy();
          return;
        }
        const port = (buf[addrEnd]! << 8) | buf[addrEnd + 1]!;
        destinations.push({ host, port });
        const totalLen = addrEnd + 2;
        const remaining = buf.subarray(totalLen);
        buf = Buffer.alloc(0);

        upstream = net.connect({ host, port }, () => {
          client.write(Buffer.from([0x05, 0x00, 0x00, 0x01, 0, 0, 0, 0, 0, 0]));
          phase = "tunnel";
          if (remaining.length > 0) {
            upstream!.write(remaining);
          }
        });
        upstream.on("data", (data: Buffer) => {
          client.write(data);
        });
        upstream.on("end", () => {
          try { client.end(); } catch { /* noop */ }
        });
        upstream.on("error", () => {
          try { client.destroy(); } catch { /* noop */ }
        });
      }
    };

    client.on("data", (chunk: Buffer) => {
      if (phase === "tunnel") {
        upstream?.write(chunk);
        return;
      }
      buf = Buffer.concat([buf, chunk]);
      tryParse();
    });
    client.on("end", () => {
      try { upstream?.end(); } catch { /* noop */ }
    });
    client.on("error", () => {
      try { upstream?.destroy(); } catch { /* noop */ }
    });
  });

  await new Promise<void>((resolve) => server.listen(0, "127.0.0.1", resolve));
  const address = server.address();
  if (!address || typeof address === "string") throw new Error("socks server bind failed");
  const port = address.port;
  t.after(async () => {
    await new Promise<void>((resolve) => server.close(() => resolve()));
  });
  return {
    port,
    connectionCount: () => connectionCount,
    destinations: () => destinations,
  };
}

test("createSocksClient routes plain HTTP through the SOCKS5 proxy", async (t) => {
  const echo = await startEchoServer(t);
  const socks = await startFakeSocks5(t);

  const client = createSocksClient({ host: "127.0.0.1", port: socks.port });

  const res = await client(`${echo.baseUrl}/cgi-bin/token?appid=AID`);

  assert.equal(res.status, 200);
  const data = await res.json<{ ok: boolean; url: string }>();
  assert.equal(data.ok, true);
  assert.equal(data.url, "/cgi-bin/token?appid=AID");

  assert.equal(
    socks.connectionCount(),
    1,
    "SOCKS5 proxy must have received exactly one connection (proves bytes were routed through it)",
  );

  const dests = socks.destinations();
  assert.equal(dests.length, 1);
  assert.equal(dests[0]!.host, "127.0.0.1");
  assert.equal(dests[0]!.port, echo.port);

  assert.equal(echo.received.length, 1);
  assert.equal(echo.received[0]!.method, "GET");
  assert.equal(echo.received[0]!.url, "/cgi-bin/token?appid=AID");
});

test("createSocksClient sends POST body through the SOCKS5 proxy", async (t) => {
  const echo = await startEchoServer(t);
  const socks = await startFakeSocks5(t);

  const client = createSocksClient({ host: "127.0.0.1", port: socks.port });

  const body = JSON.stringify({ articles: [{ title: "hi" }] });
  const res = await client(`${echo.baseUrl}/cgi-bin/draft/add?access_token=T`, {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body,
  });

  assert.equal(res.status, 200);
  assert.equal(socks.connectionCount(), 1);
  assert.equal(echo.received.length, 1);
  assert.equal(echo.received[0]!.method, "POST");
  assert.equal(echo.received[0]!.headers["content-type"], "application/json");
  assert.equal(echo.received[0]!.headers["content-length"], String(Buffer.byteLength(body)));
  assert.equal(echo.received[0]!.body.toString("utf-8"), body);
});

test("createSocksClient rejects invalid proxy ports", () => {
  assert.throws(
    () => createSocksClient({ host: "127.0.0.1", port: 0 }),
    /Invalid SOCKS proxy port/,
  );
  assert.throws(
    () => createSocksClient({ host: "127.0.0.1", port: 70_000 }),
    /Invalid SOCKS proxy port/,
  );
  assert.throws(
    () => createSocksClient({ host: "", port: 1080 }),
    /SOCKS proxy host required/,
  );
});
