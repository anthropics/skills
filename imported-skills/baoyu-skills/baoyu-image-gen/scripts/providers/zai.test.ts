import assert from "node:assert/strict";
import test, { type TestContext } from "node:test";

import type { CliArgs } from "../types.ts";
import {
  buildRequestBody,
  buildZaiUrl,
  extractImageFromResponse,
  getDefaultModel,
  getModelFamily,
  parseAspectRatio,
  parseSize,
  resolveSizeForModel,
  validateArgs,
} from "./zai.ts";

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

test("Z.AI default model prefers env override and otherwise uses glm-image", (t) => {
  useEnv(t, {
    ZAI_IMAGE_MODEL: null,
    BIGMODEL_IMAGE_MODEL: null,
  });
  assert.equal(getDefaultModel(), "glm-image");

  process.env.BIGMODEL_IMAGE_MODEL = "cogview-4-250304";
  assert.equal(getDefaultModel(), "cogview-4-250304");
});

test("Z.AI URL builder normalizes host, v4 base, and full endpoint inputs", (t) => {
  useEnv(t, { ZAI_BASE_URL: "https://api.z.ai" });
  assert.equal(buildZaiUrl(), "https://api.z.ai/api/paas/v4/images/generations");

  process.env.ZAI_BASE_URL = "https://proxy.example.com/api/paas/v4/";
  assert.equal(buildZaiUrl(), "https://proxy.example.com/api/paas/v4/images/generations");

  process.env.ZAI_BASE_URL = "https://proxy.example.com/custom/images/generations";
  assert.equal(buildZaiUrl(), "https://proxy.example.com/custom/images/generations");
});

test("Z.AI model family and parsing helpers recognize documented formats", () => {
  assert.equal(getModelFamily("glm-image"), "glm");
  assert.equal(getModelFamily("cogview-4-250304"), "legacy");
  assert.deepEqual(parseAspectRatio("16:9"), { width: 16, height: 9 });
  assert.equal(parseAspectRatio("wide"), null);
  assert.deepEqual(parseSize("1280x1280"), { width: 1280, height: 1280 });
  assert.deepEqual(parseSize("1472*1088"), { width: 1472, height: 1088 });
  assert.equal(parseSize("big"), null);
});

test("Z.AI size resolution follows documented recommended ratios and validates custom sizes", () => {
  assert.equal(
    resolveSizeForModel("glm-image", makeArgs({ aspectRatio: "16:9", quality: "2k" })),
    "1728x960",
  );
  assert.equal(
    resolveSizeForModel("cogview-4-250304", makeArgs({ aspectRatio: "4:3", quality: "normal" })),
    "1152x864",
  );
  assert.equal(
    resolveSizeForModel("glm-image", makeArgs({ size: "1568x1056", quality: "2k" })),
    "1568x1056",
  );

  const uncommon = resolveSizeForModel(
    "glm-image",
    makeArgs({ aspectRatio: "5:2", quality: "normal" }),
  );
  const parsed = parseSize(uncommon);
  assert.ok(parsed);
  assert.ok(parsed.width % 32 === 0);
  assert.ok(parsed.height % 32 === 0);
  assert.ok(parsed.width * parsed.height <= 2 ** 22);

  assert.throws(
    () => resolveSizeForModel("glm-image", makeArgs({ size: "1000x1000", quality: "2k" })),
    /between 1024 and 2048/,
  );
  assert.throws(
    () => resolveSizeForModel("glm-image", makeArgs({ size: "1280x1260", quality: "2k" })),
    /divisible by 32/,
  );
  assert.throws(
    () => resolveSizeForModel("cogview-4-250304", makeArgs({ size: "2048x2048", quality: "2k" })),
    /must not exceed 2\^21 total pixels/,
  );
});

test("Z.AI validation rejects unsupported refs and multi-image requests", () => {
  assert.throws(
    () => validateArgs("glm-image", makeArgs({ referenceImages: ["ref.png"] })),
    /text-to-image only/,
  );
  assert.throws(
    () => validateArgs("glm-image", makeArgs({ n: 2 })),
    /single image per request/,
  );
});

test("Z.AI request body maps skill quality and resolved size into provider fields", () => {
  const body = buildRequestBody(
    "A cinematic science poster",
    "glm-image",
    makeArgs({ aspectRatio: "4:3", quality: "normal" }),
  );

  assert.deepEqual(body, {
    model: "glm-image",
    prompt: "A cinematic science poster",
    quality: "standard",
    size: "1472x1088",
  });
});

test("Z.AI response extraction downloads the returned image URL", async (t) => {
  const originalFetch = globalThis.fetch;
  t.after(() => {
    globalThis.fetch = originalFetch;
  });

  globalThis.fetch = async () =>
    new Response(Uint8Array.from([1, 2, 3]), {
      status: 200,
      headers: { "Content-Type": "image/png" },
    });

  const image = await extractImageFromResponse({
    data: [{ url: "https://cdn.example.com/glm-image.png" }],
  });
  assert.deepEqual([...image], [1, 2, 3]);

  await assert.rejects(
    () => extractImageFromResponse({ data: [{}] }),
    /No image URL/,
  );
});
