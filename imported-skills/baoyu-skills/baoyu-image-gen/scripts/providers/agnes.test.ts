import assert from "node:assert/strict";
import fs from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import test, { type TestContext } from "node:test";

import type { CliArgs } from "../types.ts";
import {
  buildRequestBody,
  extractImageFromResponse,
  parseAspectRatio,
  resolveReferenceImages,
  resolveSize,
  snapDim,
  validateArgs,
} from "./agnes.ts";

function useEnv(
  t: TestContext,
  values: Record<string, string | null>,
): void {
  const previous = new Map<string, string | undefined>();
  for (const [key, value] of Object.entries(values)) {
    previous.set(key, process.env[key]);
    if (value == null) {
      delete process.env[key];
    } else {
      process.env[key] = value;
    }
  }

  t.after(() => {
    for (const [key, value] of previous.entries()) {
      if (value == null) {
        delete process.env[key];
      } else {
        process.env[key] = value;
      }
    }
  });
}

function makeArgs(overrides: Partial<CliArgs> = {}): CliArgs {
  return {
    prompt: null,
    promptFiles: [],
    imagePath: null,
    provider: null,
    model: null,
    aspectRatio: null,
    size: null,
    quality: null,
    imageSize: null,
    imageApiDialect: null,
    referenceImages: [],
    n: 1,
    batchFile: null,
    jobs: null,
    json: false,
    help: false,
    responseFormat: null,
    ...overrides,
  };
}

test("snapDim rounds to the nearest multiple of 32", () => {
  assert.equal(snapDim(767), 768);
  assert.equal(snapDim(1023), 1024);
  assert.equal(snapDim(1024), 1024);
  assert.equal(snapDim(32), 32);
  assert.equal(snapDim(0), 32);
  assert.equal(snapDim(16), 32);
  assert.equal(snapDim(48), 64);
});

test("parseAspectRatio parses valid ratios and rejects invalid inputs", () => {
  assert.deepEqual(parseAspectRatio("3:4"), { width: 3, height: 4 });
  assert.deepEqual(parseAspectRatio("16:9"), { width: 16, height: 9 });
  assert.deepEqual(parseAspectRatio("1:1"), { width: 1, height: 1 });
  assert.deepEqual(parseAspectRatio("1.5:1"), { width: 1.5, height: 1 });

  assert.equal(parseAspectRatio(""), null);
  assert.equal(parseAspectRatio("invalid"), null);
  assert.equal(parseAspectRatio("3x4"), null);
  assert.equal(parseAspectRatio("0:1"), null);
  assert.equal(parseAspectRatio("1:0"), null);
});

test("resolveSize returns explicit --size directly", () => {
  assert.equal(resolveSize({ size: "1024x1024" }), "1024x1024");
  assert.equal(resolveSize({ size: "768x1024", aspectRatio: "16:9" }), "768x1024");
});

test("resolveSize returns default 1024x1024 when no size or ratio given", () => {
  assert.equal(resolveSize({}), "1024x1024");
  assert.equal(resolveSize({ size: null, aspectRatio: null }), "1024x1024");
});

test("resolveSize computes 32-aligned size within 2048 max edge", () => {
  assert.equal(resolveSize({ aspectRatio: "1:1" }), "1024x1024");
  assert.equal(resolveSize({ aspectRatio: "16:9" }), "2048x1152");
  assert.equal(resolveSize({ aspectRatio: "4:3" }), "2048x1536");
  assert.equal(resolveSize({ aspectRatio: "3:4" }), "1536x2048");
  assert.equal(resolveSize({ aspectRatio: "9:16" }), "1152x2048");
});

test("resolveSize aligns to 32 and respects max edge", () => {
  assert.equal(resolveSize({ aspectRatio: "3:1" }), "2048x672");
  assert.equal(resolveSize({ aspectRatio: "1:3" }), "672x2048");
});

test("validateArgs rejects --n > 1", () => {
  assert.throws(
    () => validateArgs("agnes-image-2.1-flash", makeArgs({ n: 2 })),
    /returns a single image per request/,
  );
  assert.doesNotThrow(() =>
    validateArgs("agnes-image-2.1-flash", makeArgs({ n: 1 })),
  );
});

test("buildRequestBody maps prompt, model, size, and reference images", () => {
  const body = buildRequestBody("a cat", "agnes-image-2.1-flash", {
    size: "1024x1024",
    aspectRatio: null,
    referenceImages: [],
  });
  assert.equal(body.model, "agnes-image-2.1-flash");
  assert.equal(body.prompt, "a cat");
  assert.equal(body.size, "1024x1024");
  assert.deepEqual(body.extra_body, { response_format: "url" });

  const bodyWithRef = buildRequestBody("a cat", "agnes-image-2.1-flash", {
    size: null,
    aspectRatio: "3:4",
    referenceImages: ["https://example.com/ref.jpg"],
  });
  assert.equal(bodyWithRef.size, "1536x2048");
  assert.deepEqual(bodyWithRef.image, ["https://example.com/ref.jpg"]);
});

test("extractImageFromResponse decodes b64_json payloads", async () => {
  const fromBase64 = await extractImageFromResponse({
    data: [{ b64_json: Buffer.from("hello").toString("base64") }],
  });
  assert.equal(Buffer.from(fromBase64).toString("utf8"), "hello");
});

test("extractImageFromResponse downloads URL payloads", async (t) => {
  const originalFetch = globalThis.fetch;
  t.after(() => {
    globalThis.fetch = originalFetch;
  });

  globalThis.fetch = async () =>
    new Response(Uint8Array.from([1, 2, 3]), {
      status: 200,
      headers: { "Content-Type": "image/png" },
    });

  const fromUrl = await extractImageFromResponse({
    data: [{ url: "https://example.com/output.png" }],
  });
  assert.deepEqual([...fromUrl], [1, 2, 3]);
});

test("extractImageFromResponse throws on empty data", async () => {
  await assert.rejects(
    () => extractImageFromResponse({ data: [] }),
    /No image/,
  );
  await assert.rejects(
    () => extractImageFromResponse({ data: [{}] }),
    /No image/,
  );
});

test("resolveReferenceImages converts local files to data URIs and passes URLs through", async (t) => {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), "agnes-ref-"));
  t.after(() => fs.rm(dir, { recursive: true, force: true }));

  const localPath = path.join(dir, "ref.png");
  const localBytes = Buffer.from([0x89, 0x50, 0x4e, 0x47]);
  await fs.writeFile(localPath, localBytes);

  const jpegPath = path.join(dir, "photo.jpeg");
  await fs.writeFile(jpegPath, Buffer.from([0xff, 0xd8]));

  const results = await resolveReferenceImages([
    localPath,
    "https://example.com/remote.jpg",
    jpegPath,
  ]);

  assert.equal(results.length, 3);
  assert.match(results[0]!, /^data:image\/png;base64,/);
  assert.match(results[1]!, /^https:\/\/example.com\/remote.jpg$/);
  assert.match(results[2]!, /^data:image\/jpeg;base64,/);
});

test("resolveReferenceImages detects gif and webp mime types", async (t) => {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), "agnes-mime-"));
  t.after(() => fs.rm(dir, { recursive: true, force: true }));

  const webpPath = path.join(dir, "ref.webp");
  const gifPath = path.join(dir, "ref.gif");
  await fs.writeFile(webpPath, Buffer.from([0x00]));
  await fs.writeFile(gifPath, Buffer.from([0x00]));

  const results = await resolveReferenceImages([webpPath, gifPath]);
  assert.match(results[0]!, /^data:image\/webp;base64,/);
  assert.match(results[1]!, /^data:image\/gif;base64,/);
});
