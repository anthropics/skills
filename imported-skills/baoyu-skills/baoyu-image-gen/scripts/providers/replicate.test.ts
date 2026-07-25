import assert from "node:assert/strict";
import test from "node:test";

import type { CliArgs } from "../types.ts";
import {
  buildInput,
  extractOutputUrl,
  getDefaultModel,
  getModelFamily,
  parseModelId,
  validateArgs,
} from "./replicate.ts";

function makeArgs(overrides: Partial<CliArgs> = {}): CliArgs {
  return {
    prompt: null,
    promptFiles: [],
    imagePath: null,
    provider: null,
    model: null,
    aspectRatio: null,
    aspectRatioSource: null,
    size: null,
    quality: null,
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

test("Replicate default model now points at nano-banana-2", () => {
  const previous = process.env.REPLICATE_IMAGE_MODEL;
  delete process.env.REPLICATE_IMAGE_MODEL;
  try {
    assert.equal(getDefaultModel(), "google/nano-banana-2");
  } finally {
    if (previous == null) {
      delete process.env.REPLICATE_IMAGE_MODEL;
    } else {
      process.env.REPLICATE_IMAGE_MODEL = previous;
    }
  }
});

test("Replicate model parsing and family detection accept supported official ids", () => {
  assert.deepEqual(parseModelId("google/nano-banana-2"), {
    owner: "google",
    name: "nano-banana-2",
    version: null,
  });
  assert.deepEqual(parseModelId("owner/model:abc123"), {
    owner: "owner",
    name: "model",
    version: "abc123",
  });

  assert.equal(getModelFamily("google/nano-banana-pro"), "nano-banana");
  assert.equal(getModelFamily("bytedance/seedream-4.5"), "seedream45");
  assert.equal(getModelFamily("bytedance/seedream-5-lite"), "seedream5lite");
  assert.equal(getModelFamily("wan-video/wan-2.7-image"), "wan27image");
  assert.equal(getModelFamily("wan-video/wan-2.7-image-pro"), "wan27imagepro");
  assert.equal(getModelFamily("stability-ai/sdxl"), "unknown");

  assert.throws(
    () => parseModelId("just-a-model-name"),
    /Invalid Replicate model format/,
  );
});

test("Replicate nano-banana input builder maps refs, aspect ratio, and quality presets", () => {
  assert.deepEqual(
    buildInput(
      "google/nano-banana-2",
      "A robot painter",
      makeArgs({
        aspectRatio: "16:9",
        quality: "2k",
      }),
      ["data:image/png;base64,AAAA"],
    ),
    {
      prompt: "A robot painter",
      resolution: "2K",
      output_format: "png",
      aspect_ratio: "16:9",
      image_input: ["data:image/png;base64,AAAA"],
    },
  );

  assert.deepEqual(
    buildInput(
      "google/nano-banana-2",
      "A robot painter",
      makeArgs({ size: "1024x1024", quality: "normal" }),
      [],
    ),
    {
      prompt: "A robot painter",
      resolution: "1K",
      output_format: "png",
      aspect_ratio: "1:1",
    },
  );
});

test("Replicate Seedream and Wan inputs use family-specific request fields", () => {
  assert.deepEqual(
    buildInput(
      "bytedance/seedream-4.5",
      "A cinematic portrait",
      makeArgs({ quality: "2k", referenceImages: ["local.png"] }),
      ["data:image/png;base64,AAAA"],
    ),
    {
      prompt: "A cinematic portrait",
      size: "4K",
      image_input: ["data:image/png;base64,AAAA"],
      aspect_ratio: "match_input_image",
    },
  );

  assert.deepEqual(
    buildInput(
      "bytedance/seedream-4.5",
      "A cinematic portrait",
      makeArgs({ size: "1536x1024" }),
      [],
    ),
    {
      prompt: "A cinematic portrait",
      size: "custom",
      width: 1536,
      height: 1024,
    },
  );

  assert.deepEqual(
    buildInput(
      "bytedance/seedream-5-lite",
      "A poster",
      makeArgs({ aspectRatio: "21:9", quality: "2k" }),
      [],
    ),
    {
      prompt: "A poster",
      size: "3K",
      aspect_ratio: "21:9",
    },
  );

  assert.deepEqual(
    buildInput(
      "wan-video/wan-2.7-image",
      "A storyboard frame",
      makeArgs({ aspectRatio: "16:9", quality: "2k" }),
      [],
    ),
    {
      prompt: "A storyboard frame",
      size: "2048*1152",
    },
  );

  assert.deepEqual(
    buildInput(
      "wan-video/wan-2.7-image-pro",
      "Blend these references",
      makeArgs({ size: "2K", referenceImages: ["a.png", "b.png"] }),
      ["ref-a", "ref-b"],
    ),
    {
      prompt: "Blend these references",
      size: "2K",
      images: ["ref-a", "ref-b"],
    },
  );
});

test("Replicate validateArgs blocks misleading multi-output and unsupported family options locally", () => {
  assert.throws(
    () =>
      validateArgs(
        "google/nano-banana-2",
        makeArgs({ n: 2 }),
      ),
    /exactly one output image/,
  );

  assert.throws(
    () =>
      validateArgs(
        "bytedance/seedream-4.5",
        makeArgs({ size: "1K" }),
      ),
    /2K, 4K, or an explicit WxH size/,
  );

  assert.throws(
    () =>
      validateArgs(
        "bytedance/seedream-5-lite",
        makeArgs({ size: "4K" }),
      ),
    /supports 2K or 3K output/,
  );

  assert.throws(
    () =>
      validateArgs(
        "wan-video/wan-2.7-image",
        makeArgs({ referenceImages: new Array(10).fill("ref.png") }),
      ),
    /at most 9 reference images/,
  );

  assert.throws(
    () =>
      validateArgs(
        "wan-video/wan-2.7-image-pro",
        makeArgs({ referenceImages: ["ref.png"], size: "4K" }),
      ),
    /only supports 4K text-to-image/,
  );

  assert.throws(
    () =>
      validateArgs(
        "stability-ai/sdxl",
        makeArgs({ aspectRatio: "16:9" }),
      ),
    /compatibility list/,
  );

  assert.doesNotThrow(() =>
    validateArgs(
      "google/nano-banana-2",
      makeArgs({ imageSize: "2K", imageSizeSource: "config" }),
    ),
  );

  assert.throws(
    () =>
      validateArgs(
        "google/nano-banana-2",
        makeArgs({ imageSize: "2K", imageSizeSource: "cli" }),
      ),
    /do not use --imageSize/,
  );

  assert.doesNotThrow(() =>
    validateArgs(
      "stability-ai/sdxl",
      makeArgs({ aspectRatio: "16:9", aspectRatioSource: "config" }),
    ),
  );

  assert.throws(
    () =>
      validateArgs(
        "stability-ai/sdxl",
        makeArgs({ aspectRatio: "16:9", aspectRatioSource: "cli" }),
      ),
    /compatibility list/,
  );

  assert.doesNotThrow(() =>
    validateArgs(
      "stability-ai/sdxl",
      makeArgs(),
    ),
  );
});

test("Replicate output extraction supports single outputs and rejects silent multi-image drops", () => {
  assert.equal(
    extractOutputUrl({ output: "https://example.com/a.png" } as never),
    "https://example.com/a.png",
  );
  assert.equal(
    extractOutputUrl({ output: ["https://example.com/b.png"] } as never),
    "https://example.com/b.png",
  );
  assert.equal(
    extractOutputUrl({ output: { url: "https://example.com/c.png" } } as never),
    "https://example.com/c.png",
  );

  assert.throws(
    () =>
      extractOutputUrl({
        output: [
          "https://example.com/one.png",
          "https://example.com/two.png",
        ],
      } as never),
    /supports saving exactly one image/,
  );

  assert.throws(
    () => extractOutputUrl({ output: { invalid: true } } as never),
    /Unexpected Replicate output format/,
  );
});
