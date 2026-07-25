import assert from "node:assert/strict";
import test from "node:test";

import type { CliArgs } from "../types.ts";
import {
  buildOpenAIGenerationsBody,
  extractImageFromResponse,
  getDefaultModel,
  getOpenAIAspectRatio,
  getOpenAIImageApiDialect,
  getOpenAIResolution,
  getMimeType,
  getOpenAISize,
  getOrientationFromAspectRatio,
  inferAspectRatioFromSize,
  inferResolutionFromSize,
  parseAspectRatio,
  validateArgs,
} from "./openai.ts";

function makeArgs(overrides: Partial<CliArgs> = {}): CliArgs {
  return {
    prompt: null,
    promptFiles: [],
    imagePath: null,
    provider: null,
    model: null,
    aspectRatio: null,
    size: null,
    quality: "2k",
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

test("OpenAI aspect-ratio parsing and size selection match model families", () => {
  assert.equal(getDefaultModel(), "gpt-image-2");
  assert.deepEqual(parseAspectRatio("16:9"), { width: 16, height: 9 });
  assert.equal(parseAspectRatio("wide"), null);
  assert.equal(parseAspectRatio("0:1"), null);

  assert.equal(getOpenAISize("dall-e-3", "16:9", "2k"), "1792x1024");
  assert.equal(getOpenAISize("dall-e-3", "9:16", "normal"), "1024x1792");
  assert.equal(getOpenAISize("dall-e-2", "16:9", "2k"), "1024x1024");
  assert.equal(getOpenAISize("gpt-image-1.5", "16:9", "2k"), "1536x1024");
  assert.equal(getOpenAISize("gpt-image-1.5", "4:3", "2k"), "1024x1024");
  assert.equal(getOpenAISize("gpt-image-2", "16:9", "2k"), "2048x1152");
  assert.equal(getOpenAISize("gpt-image-2", "9:16", "2k"), "1152x2048");
  assert.equal(getOpenAISize("gpt-image-2", "4:3", "2k"), "2048x1536");
  assert.equal(getOpenAISize("gpt-image-2", "2.35:1", "normal"), "1248x528");
  assert.equal(inferAspectRatioFromSize("1536x1024"), "3:2");
  assert.equal(inferResolutionFromSize("1536x1024"), "2K");
  assert.equal(getOpenAIAspectRatio({ aspectRatio: null, size: "2048x1152" }), "16:9");
  assert.equal(getOpenAIResolution({ imageSize: null, size: "2048x1152", quality: "normal" }), "2K");
  assert.equal(getOrientationFromAspectRatio("16:9"), "landscape");
  assert.equal(getOrientationFromAspectRatio("9:16"), "portrait");
  assert.equal(getOrientationFromAspectRatio("1:1"), null);
  assert.equal(getOpenAIImageApiDialect({ imageApiDialect: null }), "openai-native");
});

test("OpenAI generations body switches between native and ratio-metadata dialects", () => {
  assert.deepEqual(
    buildOpenAIGenerationsBody("Draw a skyline", "gpt-image-2", {
      aspectRatio: "16:9",
      size: null,
      quality: "2k",
      imageSize: null,
      imageApiDialect: null,
    }),
    {
      model: "gpt-image-2",
      prompt: "Draw a skyline",
      size: "2048x1152",
      quality: "high",
    },
  );

  assert.deepEqual(
    buildOpenAIGenerationsBody("Draw a skyline", "gemini-3-pro-image-preview", {
      aspectRatio: "16:9",
      size: null,
      quality: "2k",
      imageSize: null,
      imageApiDialect: "ratio-metadata",
    }),
    {
      model: "gemini-3-pro-image-preview",
      prompt: "Draw a skyline",
      size: "16:9",
      metadata: {
        resolution: "2K",
        orientation: "landscape",
      },
    },
  );

  assert.deepEqual(
    buildOpenAIGenerationsBody("Draw a portrait", "gemini-3-pro-image-preview", {
      aspectRatio: null,
      size: "1152x2048",
      quality: "normal",
      imageSize: null,
      imageApiDialect: "ratio-metadata",
    }),
    {
      model: "gemini-3-pro-image-preview",
      prompt: "Draw a portrait",
      size: "9:16",
      metadata: {
        resolution: "2K",
        orientation: "portrait",
      },
    },
  );
});

test("OpenAI validates gpt-image-2 custom size constraints", () => {
  assert.doesNotThrow(() =>
    validateArgs("gpt-image-2", makeArgs({ size: "3840x2160" })),
  );
  assert.doesNotThrow(() =>
    validateArgs("gpt-image-2-2026-04-21", makeArgs({ aspectRatio: "2.35:1" })),
  );

  assert.throws(
    () => validateArgs("gpt-image-2", makeArgs({ size: "1024x576" })),
    /total pixels/,
  );
  assert.throws(
    () => validateArgs("gpt-image-2", makeArgs({ size: "1025x1024" })),
    /multiples of 16px/,
  );
  assert.throws(
    () => validateArgs("gpt-image-2", makeArgs({ aspectRatio: "4:1" })),
    /must not exceed 3:1/,
  );
});

test("OpenAI mime-type detection covers supported reference image extensions", () => {
  assert.equal(getMimeType("frame.png"), "image/png");
  assert.equal(getMimeType("frame.jpg"), "image/jpeg");
  assert.equal(getMimeType("frame.webp"), "image/webp");
  assert.equal(getMimeType("frame.gif"), "image/gif");
});

test("OpenAI response extraction supports base64 and URL download flows", async (t) => {
  const originalFetch = globalThis.fetch;
  t.after(() => {
    globalThis.fetch = originalFetch;
  });

  const fromBase64 = await extractImageFromResponse({
    data: [{ b64_json: Buffer.from("hello").toString("base64") }],
  });
  assert.equal(Buffer.from(fromBase64).toString("utf8"), "hello");

  globalThis.fetch = async () =>
    new Response(Uint8Array.from([1, 2, 3]), {
      status: 200,
      headers: { "Content-Type": "application/octet-stream" },
    });

  const fromUrl = await extractImageFromResponse({
    data: [{ url: "https://example.com/image.png" }],
  });
  assert.deepEqual([...fromUrl], [1, 2, 3]);

  await assert.rejects(
    () => extractImageFromResponse({ data: [{}] }),
    /No image in response/,
  );
});
