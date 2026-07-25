import net from "node:net";
import tls from "node:tls";
import { URL } from "node:url";
import { SocksClient } from "socks";

import type {
  WechatClient,
  WechatHttpInit,
  WechatHttpResponse,
} from "./wechat-http.ts";

export interface SocksProxyEndpoint {
  host: string;
  port: number;
}

export function createSocksClient(proxy: SocksProxyEndpoint): WechatClient {
  if (!proxy.host) throw new Error("SOCKS proxy host required");
  if (!Number.isInteger(proxy.port) || proxy.port < 1 || proxy.port > 65535) {
    throw new Error(`Invalid SOCKS proxy port: ${proxy.port}`);
  }

  return async (url, init = {}) => {
    return wechatHttpViaSocks(url, init, proxy);
  };
}

async function wechatHttpViaSocks(
  rawUrl: string,
  init: WechatHttpInit,
  proxy: SocksProxyEndpoint,
): Promise<WechatHttpResponse> {
  const url = new URL(rawUrl);
  const isHttps = url.protocol === "https:";
  if (url.protocol !== "https:" && url.protocol !== "http:") {
    throw new Error(`Unsupported protocol for SOCKS client: ${url.protocol}`);
  }
  const targetPort = url.port ? Number(url.port) : isHttps ? 443 : 80;

  const { socket: tcpSocket } = await SocksClient.createConnection({
    proxy: { host: proxy.host, port: proxy.port, type: 5 },
    command: "connect",
    destination: { host: url.hostname, port: targetPort },
  });

  let stream: net.Socket | tls.TLSSocket;
  if (isHttps) {
    const tlsSocket = tls.connect({ socket: tcpSocket, servername: url.hostname });
    await new Promise<void>((resolve, reject) => {
      const onSecure = () => {
        tlsSocket.removeListener("error", onError);
        resolve();
      };
      const onError = (err: Error) => {
        tlsSocket.removeListener("secureConnect", onSecure);
        try {
          tlsSocket.destroy();
        } catch {
          /* noop */
        }
        try {
          tcpSocket.destroy();
        } catch {
          /* noop */
        }
        reject(err);
      };
      tlsSocket.once("secureConnect", onSecure);
      tlsSocket.once("error", onError);
    });
    stream = tlsSocket;
  } else {
    stream = tcpSocket;
  }

  try {
    return await sendRequestAndReadResponse(stream, url, init);
  } finally {
    try {
      stream.destroy();
    } catch {
      /* noop */
    }
  }
}

async function sendRequestAndReadResponse(
  stream: net.Socket | tls.TLSSocket,
  url: URL,
  init: WechatHttpInit,
): Promise<WechatHttpResponse> {
  const method = init.method ?? (init.body !== undefined ? "POST" : "GET");
  const body =
    init.body === undefined
      ? undefined
      : Buffer.isBuffer(init.body)
        ? init.body
        : Buffer.from(init.body, "utf-8");

  const userHeaders = init.headers ?? {};
  const headerMap = new Map<string, string>();
  for (const [k, v] of Object.entries(userHeaders)) {
    headerMap.set(k.toLowerCase(), `${k}: ${v}`);
  }
  if (!headerMap.has("host")) headerMap.set("host", `Host: ${url.host}`);
  if (!headerMap.has("user-agent")) {
    headerMap.set("user-agent", "User-Agent: baoyu-skills-wechat-api");
  }
  headerMap.set("connection", "Connection: close");
  if (body && !headerMap.has("content-length")) {
    headerMap.set("content-length", `Content-Length: ${body.length}`);
  }

  const path = `${url.pathname || "/"}${url.search}`;
  const requestHeader = Buffer.from(
    `${method} ${path} HTTP/1.1\r\n` +
      Array.from(headerMap.values()).join("\r\n") +
      "\r\n\r\n",
    "utf-8",
  );

  await writeAll(stream, requestHeader);
  if (body) await writeAll(stream, body);

  const raw = await readToEnd(stream);
  return parseHttpResponse(raw);
}

function writeAll(stream: net.Socket | tls.TLSSocket, data: Buffer): Promise<void> {
  return new Promise((resolve, reject) => {
    stream.write(data, (err) => {
      if (err) reject(err);
      else resolve();
    });
  });
}

function readToEnd(stream: net.Socket | tls.TLSSocket): Promise<Buffer> {
  return new Promise((resolve, reject) => {
    const chunks: Buffer[] = [];
    stream.on("data", (chunk: Buffer) => chunks.push(chunk));
    stream.once("end", () => resolve(Buffer.concat(chunks)));
    stream.once("error", reject);
  });
}

function parseHttpResponse(raw: Buffer): WechatHttpResponse {
  const headerEnd = raw.indexOf("\r\n\r\n");
  if (headerEnd < 0) {
    throw new Error("Malformed HTTP response: missing header terminator");
  }
  const headerText = raw.subarray(0, headerEnd).toString("utf-8");
  let bodyBytes = raw.subarray(headerEnd + 4);

  const lines = headerText.split("\r\n");
  const statusLine = lines.shift() ?? "";
  const statusMatch = statusLine.match(/^HTTP\/[\d.]+\s+(\d+)(?:\s+(.*))?$/);
  if (!statusMatch) {
    throw new Error(`Malformed HTTP status line: ${statusLine}`);
  }
  const status = Number.parseInt(statusMatch[1]!, 10);
  const statusText = statusMatch[2] ?? "";

  const headers: Record<string, string | string[] | undefined> = {};
  const lowercaseHeaders: Record<string, string> = {};
  for (const line of lines) {
    const colon = line.indexOf(":");
    if (colon < 0) continue;
    const key = line.slice(0, colon).trim();
    const value = line.slice(colon + 1).trim();
    const lower = key.toLowerCase();
    const existing = headers[lower];
    if (existing === undefined) {
      headers[lower] = value;
    } else if (Array.isArray(existing)) {
      existing.push(value);
    } else {
      headers[lower] = [existing, value];
    }
    lowercaseHeaders[lower] = value;
  }

  const transferEncoding = (lowercaseHeaders["transfer-encoding"] ?? "").toLowerCase();
  if (transferEncoding.split(",").map((s) => s.trim()).includes("chunked")) {
    bodyBytes = dechunk(bodyBytes);
  } else if (lowercaseHeaders["content-length"] !== undefined) {
    const length = Number.parseInt(lowercaseHeaders["content-length"]!, 10);
    if (Number.isFinite(length) && length >= 0) {
      bodyBytes = bodyBytes.subarray(0, length);
    }
  }

  return {
    status,
    statusText,
    headers,
    async buffer() {
      return bodyBytes;
    },
    async text() {
      return bodyBytes.toString("utf-8");
    },
    async json<T = unknown>() {
      return JSON.parse(bodyBytes.toString("utf-8")) as T;
    },
  };
}

function dechunk(raw: Buffer): Buffer {
  const parts: Buffer[] = [];
  let offset = 0;
  while (offset < raw.length) {
    const lineEnd = raw.indexOf("\r\n", offset);
    if (lineEnd < 0) break;
    const sizeText = raw.subarray(offset, lineEnd).toString("ascii").split(";")[0]!.trim();
    const size = Number.parseInt(sizeText, 16);
    if (!Number.isFinite(size) || size < 0) {
      throw new Error(`Invalid chunked-encoding size: ${sizeText}`);
    }
    offset = lineEnd + 2;
    if (size === 0) break;
    if (offset + size > raw.length) {
      throw new Error("Chunked-encoding body truncated");
    }
    parts.push(raw.subarray(offset, offset + size));
    offset += size + 2;
  }
  return Buffer.concat(parts);
}
