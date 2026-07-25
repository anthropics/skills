import assert from "node:assert/strict";
import fs from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import test, { type TestContext } from "node:test";

import type { CliArgs } from "../types.ts";
import {
  buildMinimaxUrl,
  buildRequestBody,
  buildSubjectReference,
  extractImageFromResponse,
  parsePixelSize,
  validateArgs,
} from "./minimax.ts";

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
    ...overrides,
  };
}

test("MiniMax URL builder uses documented default and normalizes /v1 suffixes", (t) => {
  useEnv(t, { MINIMAX_BASE_URL: null });
  assert.equal(buildMinimaxUrl(), "https://api.minimaxi.com/v1/image_generation");

  process.env.MINIMAX_BASE_URL = "https://api.minimax.io";
  assert.equal(buildMinimaxUrl(), "https://api.minimax.io/v1/image_generation");

  process.env.MINIMAX_BASE_URL = "https://proxy.example.com/custom/v1/";
  assert.equal(buildMinimaxUrl(), "https://proxy.example.com/custom/v1/image_generation");
});

test("MiniMax size parsing and validation follow documented constraints", () => {
  assert.deepEqual(parsePixelSize("1536x1024"), { width: 1536, height: 1024 });
  assert.deepEqual(parsePixelSize("1536*1024"), { width: 1536, height: 1024 });
  assert.equal(parsePixelSize("wide"), null);

  validateArgs("image-01", makeArgs({ size: "1536x1024", n: 9 }));

  assert.throws(
    () => validateArgs("image-01-live", makeArgs({ size: "1536x1024" })),
    /only supported with model image-01/,
  );
  assert.throws(
    () => validateArgs("image-01", makeArgs({ size: "1537x1024" })),
    /divisible by 8/,
  );
  assert.throws(
    () => validateArgs("image-01", makeArgs({ aspectRatio: "2.35:1" })),
    /aspect_ratio must be one of/,
  );
  assert.throws(
    () => validateArgs("image-01", makeArgs({ n: 10 })),
    /at most 9 images/,
  );
});

test("MiniMax request body maps aspect ratio, size, n, and subject references", async (t) => {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), "minimax-test-"));
  t.after(() => fs.rm(dir, { recursive: true, force: true }));

  const refPath = path.join(dir, "portrait.png");
  await fs.writeFile(refPath, Buffer.from("portrait"));

  const ratioBody = await buildRequestBody(
    "A portrait by the window",
    "image-01",
    makeArgs({ aspectRatio: "16:9", n: 2, referenceImages: [refPath] }),
  );
  assert.equal(ratioBody.aspect_ratio, "16:9");
  assert.equal(ratioBody.n, 2);
  assert.equal(ratioBody.response_format, "base64");
  assert.match(ratioBody.subject_reference?.[0]?.image_file || "", /^data:image\/png;base64,/);

  const sizeBody = await buildRequestBody(
    "A portrait by the window",
    "image-01",
    makeArgs({ size: "1536x1024" }),
  );
  assert.equal(sizeBody.width, 1536);
  assert.equal(sizeBody.height, 1024);
  assert.equal(sizeBody.aspect_ratio, undefined);
});

test("MiniMax subject references require supported file types", async (t) => {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), "minimax-ref-"));
  t.after(() => fs.rm(dir, { recursive: true, force: true }));

  const good = path.join(dir, "portrait.jpg");
  const bad = path.join(dir, "portrait.webp");
  await fs.writeFile(good, Buffer.from("portrait"));
  await fs.writeFile(bad, Buffer.from("portrait"));

  const subjectReference = await buildSubjectReference([good]);
  assert.equal(subjectReference?.[0]?.type, "character");

  await assert.rejects(
    () => buildSubjectReference([bad]),
    /only supports JPG, JPEG, or PNG/,
  );
});

test("MiniMax response extraction supports base64 and URL payloads", async (t) => {
  const originalFetch = globalThis.fetch;
  t.after(() => {
    globalThis.fetch = originalFetch;
  });

  const fromBase64 = await extractImageFromResponse({
    data: {
      image_base64: [Buffer.from("hello").toString("base64")],
    },
  });
  assert.equal(Buffer.from(fromBase64).toString("utf8"), "hello");

  globalThis.fetch = async () =>
    new Response(Uint8Array.from([1, 2, 3]), {
      status: 200,
      headers: { "Content-Type": "image/jpeg" },
    });

  const fromUrl = await extractImageFromResponse({
    data: {
      image_urls: ["https://example.com/output.jpg"],
    },
  });
  assert.deepEqual([...fromUrl], [1, 2, 3]);

  await assert.rejects(
    () => extractImageFromResponse({ base_resp: { status_code: 1001, status_msg: "blocked" } }),
    /blocked/,
  );
});
