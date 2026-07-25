import assert from "node:assert/strict";
import fs from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import test, { type TestContext } from "node:test";

import type { CliArgs } from "../types.ts";
import {
  buildImageInput,
  buildRequestBody,
  generateImage,
  getDefaultOutputExtension,
  resolveSeedreamSize,
  validateArgs,
} from "./seedream.ts";

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

async function makeTempPng(t: TestContext, name: string): Promise<string> {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), "seedream-test-"));
  t.after(() => fs.rm(dir, { recursive: true, force: true }));

  const filePath = path.join(dir, name);
  const png1x1 =
    "iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAQAAAC1HAwCAAAAC0lEQVR42mP8/x8AAwMCAO+a7m0AAAAASUVORK5CYII=";
  await fs.writeFile(filePath, Buffer.from(png1x1, "base64"));
  return filePath;
}

test("Seedream request body and default extensions follow official model capabilities", () => {
  const five = buildRequestBody(
    "A robot illustrator",
    "doubao-seedream-5-0-260128",
    makeArgs(),
  );
  assert.equal(five.size, "2K");
  assert.equal(five.response_format, "url");
  assert.equal(five.output_format, "png");
  assert.equal(getDefaultOutputExtension("doubao-seedream-5-0-260128"), ".png");

  const fourFive = buildRequestBody(
    "A robot illustrator",
    "doubao-seedream-4-5-251128",
    makeArgs(),
  );
  assert.equal(fourFive.size, "2K");
  assert.equal(fourFive.response_format, "url");
  assert.ok(!("output_format" in fourFive));
  assert.equal(getDefaultOutputExtension("doubao-seedream-4-5-251128"), ".jpg");

  assert.throws(
    () =>
      buildRequestBody(
        "Change the bubbles into hearts",
        "doubao-seededit-3-0-i2i-250628",
        makeArgs({ referenceImages: ["ref.png"] }),
        "data:image/png;base64,AAAA",
      ),
    /no longer supported/,
  );
});

test("Seedream size selection validates model-specific presets", () => {
  assert.equal(
    resolveSeedreamSize("doubao-seedream-4-0-250828", makeArgs({ quality: "normal" })),
    "1K",
  );
  assert.equal(
    resolveSeedreamSize("doubao-seedream-3-0-t2i-250415", makeArgs({ quality: "2k" })),
    "2048x2048",
  );

  assert.throws(
    () =>
      resolveSeedreamSize("doubao-seedream-5-0-260128", makeArgs({ size: "4K" })),
    /only supports 2K, 3K/,
  );
  assert.throws(
    () =>
      resolveSeedreamSize("doubao-seedream-3-0-t2i-250415", makeArgs({ imageSize: "2K" })),
    /only supports explicit WxH sizes/,
  );
  assert.throws(
    () =>
      resolveSeedreamSize("doubao-seededit-3-0-i2i-250628", makeArgs({ size: "1024x1024" })),
    /no longer supported/,
  );
});

test("Seedream reference-image support is model-specific", () => {
  assert.doesNotThrow(() =>
    validateArgs(
      "doubao-seedream-5-0-260128",
      makeArgs({ referenceImages: ["a.png", "b.png"] }),
    ),
  );

  assert.throws(
    () =>
      validateArgs(
        "doubao-seedream-3-0-t2i-250415",
        makeArgs({ referenceImages: ["a.png"] }),
      ),
    /does not support reference images/,
  );

  assert.throws(
    () =>
      validateArgs(
        "doubao-seededit-3-0-i2i-250628",
        makeArgs(),
      ),
    /no longer supported/,
  );

  assert.throws(
    () =>
      validateArgs(
        "ep-20260315171508-t8br2",
        makeArgs({ referenceImages: ["a.png"] }),
      ),
    /require a known model ID/,
  );
});

test("Seedream image input encodes local references as data URLs", async (t) => {
  const refOne = await makeTempPng(t, "one.png");
  const refTwo = await makeTempPng(t, "two.png");

  const single = await buildImageInput("doubao-seedream-4-5-251128", [refOne]);
  assert.match(String(single), /^data:image\/png;base64,/);

  const multiple = await buildImageInput("doubao-seedream-5-0-260128", [refOne, refTwo]);
  assert.ok(Array.isArray(multiple));
  assert.equal(multiple.length, 2);
});

test("Seedream generateImage posts the documented response_format and downloads the returned URL", async (t) => {
  useEnv(t, { ARK_API_KEY: "test-key", SEEDREAM_BASE_URL: null });

  const originalFetch = globalThis.fetch;
  t.after(() => {
    globalThis.fetch = originalFetch;
  });

  const calls: Array<{
    input: string;
    init?: RequestInit;
  }> = [];

  globalThis.fetch = async (input, init) => {
    calls.push({
      input: String(input),
      init,
    });

    if (calls.length === 1) {
      return Response.json({
        model: "doubao-seedream-4-5-251128",
        created: 1740000000,
        data: [
          {
            url: "https://example.com/generated-image",
            size: "2048x2048",
          },
        ],
        usage: {
          generated_images: 1,
          output_tokens: 1,
          total_tokens: 1,
        },
      });
    }

    return new Response(Uint8Array.from([7, 8, 9]), {
      status: 200,
      headers: { "Content-Type": "image/jpeg" },
    });
  };

  const image = await generateImage(
    "A robot illustrator",
    "doubao-seedream-4-5-251128",
    makeArgs(),
  );

  assert.deepEqual([...image], [7, 8, 9]);
  assert.equal(calls.length, 2);
  assert.equal(
    calls[0]?.input,
    "https://ark.cn-beijing.volces.com/api/v3/images/generations",
  );

  const requestBody = JSON.parse(String(calls[0]?.init?.body)) as Record<string, unknown>;
  assert.equal(requestBody.model, "doubao-seedream-4-5-251128");
  assert.equal(requestBody.size, "2K");
  assert.equal(requestBody.response_format, "url");
  assert.ok(!("output_format" in requestBody));
  assert.equal(calls[1]?.input, "https://example.com/generated-image");
});
