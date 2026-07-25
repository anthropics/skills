export interface WechatHttpInit {
  method?: string;
  headers?: Record<string, string>;
  body?: string | Buffer;
}

export interface WechatHttpResponse {
  status: number;
  statusText: string;
  headers: Record<string, string | string[] | undefined>;
  buffer(): Promise<Buffer>;
  text(): Promise<string>;
  json<T = unknown>(): Promise<T>;
}

export type WechatClient = (
  url: string,
  init?: WechatHttpInit,
) => Promise<WechatHttpResponse>;

export interface MultipartFilePart {
  name: string;
  filename: string;
  contentType: string;
  data: Buffer;
}

export interface MultipartBody {
  contentType: string;
  body: Buffer;
}

export function buildMultipart(parts: MultipartFilePart[]): MultipartBody {
  const boundary = `----WebKitFormBoundary${Date.now().toString(16)}${Math.random().toString(16).slice(2, 10)}`;
  const chunks: Buffer[] = [];

  for (const part of parts) {
    const header =
      `--${boundary}\r\n` +
      `Content-Disposition: form-data; name="${part.name}"; filename="${part.filename}"\r\n` +
      `Content-Type: ${part.contentType}\r\n\r\n`;
    chunks.push(Buffer.from(header, "utf-8"));
    chunks.push(part.data);
    chunks.push(Buffer.from("\r\n", "utf-8"));
  }
  chunks.push(Buffer.from(`--${boundary}--\r\n`, "utf-8"));

  return {
    contentType: `multipart/form-data; boundary=${boundary}`,
    body: Buffer.concat(chunks),
  };
}

function headersToRecord(headers: Headers): Record<string, string | string[] | undefined> {
  const out: Record<string, string | string[] | undefined> = {};
  headers.forEach((value, key) => {
    const existing = out[key];
    if (existing === undefined) {
      out[key] = value;
    } else if (Array.isArray(existing)) {
      existing.push(value);
    } else {
      out[key] = [existing, value];
    }
  });
  return out;
}

export const wechatHttp: WechatClient = async (url, init = {}) => {
  const method = init.method ?? (init.body !== undefined ? "POST" : "GET");
  const headers: Record<string, string> = { ...(init.headers ?? {}) };

  let body: BodyInit | undefined;
  if (init.body !== undefined) {
    body = Buffer.isBuffer(init.body)
      ? new Uint8Array(init.body.buffer, init.body.byteOffset, init.body.byteLength)
      : init.body;
  }

  const res = await fetch(url, { method, headers, body });
  const buf = Buffer.from(await res.arrayBuffer());

  return {
    status: res.status,
    statusText: res.statusText,
    headers: headersToRecord(res.headers),
    async buffer() {
      return buf;
    },
    async text() {
      return buf.toString("utf-8");
    },
    async json<T = unknown>() {
      return JSON.parse(buf.toString("utf-8")) as T;
    },
  };
};
