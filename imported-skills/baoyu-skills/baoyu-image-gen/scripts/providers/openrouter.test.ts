import assert from "node:assert/strict";
import test from "node:test";

import type { CliArgs } from "../types.ts";
import {
  buildContent,
  buildRequestBody,
  extractImageFromResponse,
  getAspectRatio,
  getImageSize,
  validateArgs,
} from "./openrouter.ts";

const GEMINI_MODEL = "google/gemini-3.1-flash-image-preview";
const GEMINI_25_MODEL = "google/gemini-2.5-flash-image";
const GPT_5_IMAGE_MODEL = "openai/gpt-5-image";
const OPENROUTER_AUTO_MODEL = "openrouter/auto";
const FLUX_MODEL = "black-forest-labs/flux.2-pro";

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

test("OpenRouter request body uses image_config and string content for text-only prompts", () => {
  const args = makeArgs({ aspectRatio: "16:9", quality: "2k" });
  const body = buildRequestBody("hello", GEMINI_MODEL, args, []);

  assert.deepEqual(body.image_config, {
    image_size: "2K",
    aspect_ratio: "16:9",
  });
  assert.deepEqual(body.provider, {
    require_parameters: true,
  });
  assert.deepEqual(body.modalities, ["image", "text"]);
  assert.equal(body.stream, false);
  assert.equal(body.messages[0].content, "hello");
});

test("OpenRouter request body keeps text+image modalities for current text+image models", () => {
  for (const model of [GEMINI_MODEL, GEMINI_25_MODEL, GPT_5_IMAGE_MODEL, OPENROUTER_AUTO_MODEL]) {
    const body = buildRequestBody("hello", model, makeArgs({ quality: "2k" }), []);

    assert.deepEqual(body.image_config, {
      image_size: "2K",
    });
    assert.deepEqual(body.provider, {
      require_parameters: true,
    });
    assert.deepEqual(body.modalities, ["image", "text"]);
    assert.equal(body.messages[0].content, "hello");
  }
});

test("OpenRouter request body uses image-only modalities for image-only models under CLI defaults", () => {
  const body = buildRequestBody("hello", FLUX_MODEL, makeArgs({ quality: "2k" }), []);

  assert.deepEqual(body.image_config, {
    image_size: "2K",
  });
  assert.deepEqual(body.provider, {
    require_parameters: true,
  });
  assert.deepEqual(body.modalities, ["image"]);
  assert.equal(body.stream, false);
  assert.equal(body.messages[0].content, "hello");
});

test("OpenRouter helper omits image_config when no size or quality is passed", () => {
  const body = buildRequestBody("hello", FLUX_MODEL, makeArgs(), []);

  assert.equal(body.image_config, undefined);
  assert.equal(body.provider, undefined);
  assert.deepEqual(body.modalities, ["image"]);
  assert.equal(body.stream, false);
  assert.equal(body.messages[0].content, "hello");
});

test("OpenRouter request body keeps multimodal array content when references are provided", () => {
  const content = buildContent("hello", ["data:image/png;base64,abc"]);
  assert.ok(Array.isArray(content));
  assert.deepEqual(content[0], { type: "text", text: "hello" });
  assert.deepEqual(content[1], {
    type: "image_url",
    image_url: { url: "data:image/png;base64,abc" },
  });
});

test("OpenRouter size and aspect helpers infer supported values", () => {
  assert.equal(getImageSize(makeArgs()), null);
  assert.equal(getImageSize(makeArgs({ quality: "normal" })), "1K");
  assert.equal(getImageSize(makeArgs({ size: "2048x1024" })), "2K");
  assert.equal(getAspectRatio(GEMINI_MODEL, makeArgs({ size: "1600x900" })), "16:9");
  assert.equal(getAspectRatio(GEMINI_MODEL, makeArgs({ size: "1024x4096" })), "1:4");
  assert.equal(getAspectRatio(GEMINI_25_MODEL, makeArgs({ size: "1600x900" })), "16:9");
  assert.equal(getAspectRatio(FLUX_MODEL, makeArgs({ size: "1024x4096" })), null);
});

test("OpenRouter validates explicit aspect ratios and inferred size ratios against model support", () => {
  assert.doesNotThrow(() =>
    validateArgs(GEMINI_MODEL, makeArgs({ aspectRatio: "1:4" })),
  );
  assert.doesNotThrow(() =>
    validateArgs(GEMINI_MODEL, makeArgs({ size: "1024x4096" })),
  );
  assert.throws(
    () => validateArgs(GEMINI_25_MODEL, makeArgs({ aspectRatio: "1:4" })),
    /does not support aspect ratio 1:4/,
  );
  assert.throws(
    () => validateArgs(FLUX_MODEL, makeArgs({ aspectRatio: "1:4" })),
    /does not support aspect ratio 1:4/,
  );
  assert.throws(
    () => validateArgs(GEMINI_MODEL, makeArgs({ size: "2048x1024" })),
    /does not support size 2048x1024 \(aspect ratio 2:1\)/,
  );
});

test("OpenRouter response extraction supports inline image data and finish_reason errors", async () => {
  const bytes = await extractImageFromResponse({
    choices: [
      {
        message: {
          images: [
            {
              image_url: {
                url: `data:image/png;base64,${Buffer.from("hello").toString("base64")}`,
              },
            },
          ],
        },
      },
    ],
  });
  assert.equal(Buffer.from(bytes).toString("utf8"), "hello");

  await assert.rejects(
    () =>
      extractImageFromResponse({
        choices: [
          {
            finish_reason: "error",
            native_finish_reason: "MALFORMED_FUNCTION_CALL",
            message: { content: null },
          },
        ],
      }),
    /finish_reason=MALFORMED_FUNCTION_CALL/,
  );
});
