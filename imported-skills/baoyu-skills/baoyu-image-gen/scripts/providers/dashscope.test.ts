import assert from "node:assert/strict";
import test, { type TestContext } from "node:test";

import {
  generateImage,
  getDefaultModel,
  getModelFamily,
  getQwen2SizeFromAspectRatio,
  getSizeFromAspectRatio,
  getWan27SizeFromAspectRatio,
  normalizeSize,
  parseAspectRatio,
  parseSize,
  resolveSizeForModel,
} from "./dashscope.ts";
import type { CliArgs } from "../types.ts";

function makeCliArgs(overrides: Partial<CliArgs> = {}): CliArgs {
  return {
    prompt: null,
    promptFiles: [],
    imagePath: null,
    provider: "dashscope",
    model: null,
    aspectRatio: null,
    aspectRatioSource: null,
    size: null,
    quality: "2k",
    imageSize: null,
    imageSizeSource: null,
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

test("DashScope default model prefers env override and otherwise uses qwen-image-2.0-pro", (t) => {
  useEnv(t, { DASHSCOPE_IMAGE_MODEL: null });
  assert.equal(getDefaultModel(), "qwen-image-2.0-pro");

  process.env.DASHSCOPE_IMAGE_MODEL = "qwen-image-max";
  assert.equal(getDefaultModel(), "qwen-image-max");
});

test("DashScope aspect-ratio parsing accepts numeric ratios only", () => {
  assert.deepEqual(parseAspectRatio("3:2"), { width: 3, height: 2 });
  assert.equal(parseAspectRatio("square"), null);
  assert.equal(parseAspectRatio("-1:2"), null);
});

test("DashScope model family routing distinguishes qwen-2.0, fixed-size qwen, wan2.7, and legacy models", () => {
  assert.equal(getModelFamily("qwen-image-2.0-pro"), "qwen2");
  assert.equal(getModelFamily("qwen-image"), "qwenFixed");
  assert.equal(getModelFamily("wan2.7-image"), "wan27");
  assert.equal(getModelFamily("wan2.7-image-pro"), "wan27");
  assert.equal(getModelFamily("z-image-turbo"), "legacy");
  assert.equal(getModelFamily("wanx-v1"), "legacy");
});

test("Legacy DashScope size selection keeps the previous quality-based heuristic", () => {
  assert.equal(getSizeFromAspectRatio(null, "normal"), "1024*1024");
  assert.equal(getSizeFromAspectRatio("16:9", "normal"), "1280*720");
  assert.equal(getSizeFromAspectRatio("16:9", "2k"), "2048*1152");
  assert.equal(getSizeFromAspectRatio("invalid", "2k"), "1536*1536");
});

test("Qwen 2.0 recommended sizes follow the official common-ratio table", () => {
  assert.equal(getQwen2SizeFromAspectRatio(null, "normal"), "1024*1024");
  assert.equal(getQwen2SizeFromAspectRatio(null, "2k"), "1536*1536");
  assert.equal(getQwen2SizeFromAspectRatio("16:9", "normal"), "1280*720");
  assert.equal(getQwen2SizeFromAspectRatio("21:9", "2k"), "2048*872");
});

test("Qwen 2.0 derives free-form sizes within pixel budget for uncommon ratios", () => {
  const size = getQwen2SizeFromAspectRatio("5:2", "normal");
  const parsed = parseSize(size);
  assert.ok(parsed);
  assert.ok(parsed.width * parsed.height >= 512 * 512);
  assert.ok(parsed.width * parsed.height <= 2048 * 2048);
  assert.ok(Math.abs(parsed.width / parsed.height - 2.5) < 0.08);
});

test("resolveSizeForModel validates explicit qwen-image-2.0 sizes by total pixels", () => {
  assert.equal(
    resolveSizeForModel("qwen-image-2.0-pro", {
      size: "2048x872",
      aspectRatio: null,
      quality: "2k",
    }),
    "2048*872",
  );

  assert.throws(
    () =>
      resolveSizeForModel("qwen-image-2.0-pro", {
        size: "4096x4096",
        aspectRatio: null,
        quality: "2k",
      }),
    /total pixels between/,
  );
});

test("resolveSizeForModel enforces fixed sizes for qwen-image-max/plus/image", () => {
  assert.equal(
    resolveSizeForModel("qwen-image-max", {
      size: null,
      aspectRatio: "1:1",
      quality: "2k",
    }),
    "1328*1328",
  );

  assert.equal(
    resolveSizeForModel("qwen-image", {
      size: "1664x928",
      aspectRatio: "9:16",
      quality: "normal",
    }),
    "1664*928",
  );

  assert.throws(
    () =>
      resolveSizeForModel("qwen-image-max", {
        size: null,
        aspectRatio: "21:9",
        quality: "2k",
      }),
    /supports only fixed ratios/,
  );

  assert.throws(
    () =>
      resolveSizeForModel("qwen-image-plus", {
        size: "1024x1024",
        aspectRatio: null,
        quality: "2k",
      }),
    /support only these sizes/,
  );
});

test("DashScope size normalization converts WxH into provider format", () => {
  assert.equal(normalizeSize("1024x1024"), "1024*1024");
  assert.equal(normalizeSize("2048*1152"), "2048*1152");
});

test("Wan 2.7 derives sizes that match the requested ratio at the chosen pixel budget", () => {
  const square2k = getWan27SizeFromAspectRatio(null, "2k", 2048 * 2048);
  const parsedSquare = parseSize(square2k);
  assert.ok(parsedSquare);
  assert.equal(parsedSquare.width, parsedSquare.height);
  assert.ok(parsedSquare.width * parsedSquare.height <= 2048 * 2048);

  const widescreen = getWan27SizeFromAspectRatio("16:9", "2k", 2048 * 2048);
  const parsedWide = parseSize(widescreen);
  assert.ok(parsedWide);
  assert.ok(Math.abs(parsedWide.width / parsedWide.height - 16 / 9) < 0.05);
  assert.ok(parsedWide.width * parsedWide.height <= 2048 * 2048);

  const pro4k = getWan27SizeFromAspectRatio("16:9", "2k", 4096 * 4096);
  const parsed4k = parseSize(pro4k);
  assert.ok(parsed4k);
  assert.ok(parsed4k.width * parsed4k.height > 2048 * 2048);
  assert.ok(parsed4k.width * parsed4k.height <= 4096 * 4096);
});

test("Wan 2.7 rejects aspect ratios outside the [1:8, 8:1] range", () => {
  assert.throws(
    () => getWan27SizeFromAspectRatio("9:1", "2k", 2048 * 2048),
    /1:8, 8:1/,
  );
  assert.throws(
    () => getWan27SizeFromAspectRatio("1:9", "normal", 2048 * 2048),
    /1:8, 8:1/,
  );
});

test("Wan 2.7 derived sizes stay inside the boundary ratio limits after rounding", () => {
  for (const ar of ["8:1", "1:8"]) {
    const size = getWan27SizeFromAspectRatio(ar, "2k", 2048 * 2048);
    const parsed = parseSize(size);
    assert.ok(parsed);
    const ratio = parsed.width / parsed.height;
    assert.ok(ratio >= 1 / 8);
    assert.ok(ratio <= 8);
    assert.ok(parsed.width * parsed.height <= 2048 * 2048);
  }
});

test("resolveSizeForModel routes wan2.7-image to the 2K-capped derivation", () => {
  const size = resolveSizeForModel("wan2.7-image", {
    size: null,
    aspectRatio: "16:9",
    quality: "2k",
  });
  const parsed = parseSize(size);
  assert.ok(parsed);
  assert.ok(parsed.width * parsed.height <= 2048 * 2048);
  assert.ok(Math.abs(parsed.width / parsed.height - 16 / 9) < 0.05);
});

test("resolveSizeForModel allows wan2.7-image-pro 4K only when there are no reference images", () => {
  assert.equal(
    resolveSizeForModel("wan2.7-image-pro", {
      size: "4096*4096",
      aspectRatio: null,
      quality: "2k",
    }),
    "4096*4096",
  );

  assert.throws(
    () =>
      resolveSizeForModel("wan2.7-image-pro", {
        size: "4096*4096",
        aspectRatio: null,
        quality: "2k",
        referenceImages: ["a.png"],
      }),
    /total pixels between 768\*768 and 2048\*2048/,
  );

  const proWithRef = resolveSizeForModel("wan2.7-image-pro", {
    size: null,
    aspectRatio: "1:1",
    quality: "2k",
    referenceImages: ["a.png"],
  });
  const parsedRef = parseSize(proWithRef);
  assert.ok(parsedRef);
  assert.ok(parsedRef.width * parsedRef.height <= 2048 * 2048);
});

test("Wan 2.7 request body forces n=1 and omits prompt_extend / negative_prompt", async (t) => {
  useEnv(t, { DASHSCOPE_API_KEY: "fake-key" });

  const originalFetch = globalThis.fetch;
  let capturedBody: any = null;
  globalThis.fetch = (async (_url: string, init?: RequestInit) => {
    capturedBody = JSON.parse(String(init?.body));
    return new Response(
      JSON.stringify({
        output: {
          choices: [
            {
              message: {
                content: [{ image: "data:image/png;base64,iVBORw0KGgo=" }],
              },
            },
          ],
        },
      }),
      { status: 200, headers: { "content-type": "application/json" } },
    );
  }) as typeof fetch;
  t.after(() => {
    globalThis.fetch = originalFetch;
  });

  await generateImage("hello", "wan2.7-image-pro", makeCliArgs({ aspectRatio: "1:1" }));

  assert.equal(capturedBody.model, "wan2.7-image-pro");
  assert.deepEqual(Object.keys(capturedBody.parameters).sort(), ["n", "size", "watermark"]);
  assert.equal(capturedBody.parameters.n, 1);
  assert.equal(capturedBody.parameters.watermark, false);
  assert.equal(typeof capturedBody.parameters.size, "string");
  assert.ok(!("prompt_extend" in capturedBody.parameters));
  assert.ok(!("negative_prompt" in capturedBody.parameters));

  assert.deepEqual(capturedBody.input.messages[0].content, [{ text: "hello" }]);
});

test("Wan 2.7 request body forwards remote reference image URLs", async (t) => {
  useEnv(t, { DASHSCOPE_API_KEY: "fake-key" });

  const originalFetch = globalThis.fetch;
  let capturedBody: any = null;
  globalThis.fetch = (async (_url: string, init?: RequestInit) => {
    capturedBody = JSON.parse(String(init?.body));
    return new Response(
      JSON.stringify({
        output: {
          choices: [
            {
              message: {
                content: [{ image: "data:image/png;base64,iVBORw0KGgo=" }],
              },
            },
          ],
        },
      }),
      { status: 200, headers: { "content-type": "application/json" } },
    );
  }) as typeof fetch;
  t.after(() => {
    globalThis.fetch = originalFetch;
  });

  await generateImage(
    "combine these",
    "wan2.7-image-pro",
    makeCliArgs({ referenceImages: ["https://example.com/ref.png"] }),
  );

  assert.deepEqual(capturedBody.input.messages[0].content, [
    { image: "https://example.com/ref.png" },
    { text: "combine these" },
  ]);
});

test("Wan 2.7 rejects --n > 1 to prevent silent multi-image billing", async (t) => {
  useEnv(t, { DASHSCOPE_API_KEY: "fake-key" });

  await assert.rejects(
    () => generateImage("hi", "wan2.7-image-pro", makeCliArgs({ n: 2 })),
    /support exactly one output image/,
  );
});

test("resolveSizeForModel validates explicit wan2.7 sizes by pixel budget and ratio", () => {
  assert.equal(
    resolveSizeForModel("wan2.7-image-pro", {
      size: "3840x2160",
      aspectRatio: null,
      quality: "2k",
    }),
    "3840*2160",
  );

  assert.throws(
    () =>
      resolveSizeForModel("wan2.7-image-pro", {
        size: "3840x2160",
        aspectRatio: null,
        quality: "2k",
        referenceImages: ["a.png"],
      }),
    /total pixels between 768\*768 and 2048\*2048/,
  );

  assert.throws(
    () =>
      resolveSizeForModel("wan2.7-image", {
        size: "4096x4096",
        aspectRatio: null,
        quality: "2k",
      }),
    /total pixels between 768\*768 and 2048\*2048/,
  );

  assert.throws(
    () =>
      resolveSizeForModel("wan2.7-image-pro", {
        size: "3072*256",
        aspectRatio: null,
        quality: "2k",
      }),
    /1:8, 8:1/,
  );
});
