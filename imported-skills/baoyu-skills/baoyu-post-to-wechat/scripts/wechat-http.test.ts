import assert from "node:assert/strict";
import http from "node:http";
import test, { type TestContext } from "node:test";

import { buildMultipart, wechatHttp } from "./wechat-http.ts";

interface ReceivedRequest {
  method: string;
  url: string;
  headers: http.IncomingHttpHeaders;
  body: Buffer;
}

async function startEchoServer(t: TestContext): Promise<{ baseUrl: string; received: ReceivedRequest[] }> {
  const received: ReceivedRequest[] = [];
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
      res.end(JSON.stringify({ ok: true, echo: { url: req.url, method: req.method } }));
    });
  });

  await new Promise<void>((resolve) => server.listen(0, "127.0.0.1", resolve));
  const address = server.address();
  if (!address || typeof address === "string") {
    throw new Error("Failed to start echo server");
  }
  const baseUrl = `http://127.0.0.1:${address.port}`;

  t.after(async () => {
    await new Promise<void>((resolve) => server.close(() => resolve()));
  });

  return { baseUrl, received };
}

test("wechatHttp performs a GET and passes through query string", async (t) => {
  const { baseUrl, received } = await startEchoServer(t);
  const res = await wechatHttp(`${baseUrl}/cgi-bin/token?grant_type=client_credential&appid=AID`);
  assert.equal(res.status, 200);
  const data = await res.json<{ ok: boolean; echo: { url: string; method: string } }>();
  assert.equal(data.ok, true);
  assert.equal(received.length, 1);
  assert.equal(received[0]!.method, "GET");
  assert.equal(received[0]!.url, "/cgi-bin/token?grant_type=client_credential&appid=AID");
  assert.equal(received[0]!.body.length, 0);
});

test("wechatHttp POST sends JSON body with content-length header", async (t) => {
  const { baseUrl, received } = await startEchoServer(t);
  const body = JSON.stringify({ articles: [{ title: "hi" }] });
  const res = await wechatHttp(`${baseUrl}/cgi-bin/draft/add?access_token=T`, {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body,
  });
  assert.equal(res.status, 200);
  assert.equal(received.length, 1);
  assert.equal(received[0]!.method, "POST");
  assert.equal(received[0]!.headers["content-type"], "application/json");
  assert.equal(received[0]!.headers["content-length"], String(Buffer.byteLength(body)));
  assert.equal(received[0]!.body.toString("utf-8"), body);
});

test("wechatHttp .text() returns the raw response body", async (t) => {
  const { baseUrl } = await startEchoServer(t);
  const res = await wechatHttp(`${baseUrl}/hello`);
  const text = await res.text();
  assert.match(text, /"ok":true/);
});

test("wechatHttp .buffer() returns a Buffer of the response body", async (t) => {
  const { baseUrl } = await startEchoServer(t);
  const res = await wechatHttp(`${baseUrl}/`);
  const buf = await res.buffer();
  assert.ok(Buffer.isBuffer(buf));
  assert.ok(buf.length > 0);
});

test("buildMultipart produces a parsable multipart payload", () => {
  const fileData = Buffer.from("ZZZ");
  const { contentType, body } = buildMultipart([
    {
      name: "media",
      filename: "image.png",
      contentType: "image/png",
      data: fileData,
    },
  ]);

  const boundaryMatch = contentType.match(/^multipart\/form-data; boundary=(.+)$/);
  assert.ok(boundaryMatch, `expected boundary in Content-Type, got ${contentType}`);
  const boundary = boundaryMatch![1]!;
  const text = body.toString("binary");
  assert.ok(text.startsWith(`--${boundary}\r\n`), "body must start with opening boundary");
  assert.ok(
    text.endsWith(`--${boundary}--\r\n`),
    "body must end with closing boundary",
  );
  assert.match(
    text,
    /Content-Disposition: form-data; name="media"; filename="image\.png"\r\n/,
  );
  assert.match(text, /Content-Type: image\/png\r\n/);
  // The raw file bytes must appear verbatim after a blank line.
  assert.ok(
    text.includes("\r\n\r\nZZZ\r\n"),
    "body must contain the raw file bytes after the part headers",
  );
});

test("wechatHttp accepts a multipart body produced by buildMultipart", async (t) => {
  const { baseUrl, received } = await startEchoServer(t);
  const fileData = Buffer.from("HELLO");
  const multipart = buildMultipart([
    { name: "media", filename: "x.png", contentType: "image/png", data: fileData },
  ]);
  const res = await wechatHttp(`${baseUrl}/cgi-bin/media/uploadimg?access_token=T`, {
    method: "POST",
    headers: { "Content-Type": multipart.contentType },
    body: multipart.body,
  });
  assert.equal(res.status, 200);
  assert.equal(received.length, 1);
  assert.equal(received[0]!.method, "POST");
  assert.match(received[0]!.headers["content-type"]!, /^multipart\/form-data; boundary=/);
  assert.ok(received[0]!.body.includes(Buffer.from("HELLO")));
});

