import assert from "node:assert/strict";
import test from "node:test";

import type { CliArgs } from "../types.ts";
import {
  getDefaultModel,
  getDefaultOutputExtension,
  validateArgs,
} from "./codex-cli.ts";

function makeArgs(overrides: Partial<CliArgs> = {}): CliArgs {
  return {
    prompt: null,
    promptFiles: [],
    imagePath: null,
    provider: "codex-cli",
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

test("codex-cli defaults to codex-image-gen model and PNG output", () => {
  assert.equal(getDefaultModel(), "codex-image-gen");
  assert.equal(getDefaultOutputExtension(), ".png");
});

test("codex-cli validateArgs rejects n>1 with a non-retryable message", () => {
  assert.throws(
    () => validateArgs("codex-image-gen", makeArgs({ n: 2 })),
    /supports only n=1/,
  );
});

test("codex-cli validateArgs rejects ratio-metadata dialect", () => {
  assert.throws(
    () => validateArgs("codex-image-gen", makeArgs({ imageApiDialect: "ratio-metadata" })),
    /Invalid imageApiDialect/,
  );
});

test("codex-cli validateArgs accepts default n=1 with no dialect", () => {
  assert.doesNotThrow(() => validateArgs("codex-image-gen", makeArgs()));
});

test("codex-cli validateArgs accepts reference images (Codex image_gen supports refs)", () => {
  assert.doesNotThrow(() =>
    validateArgs("codex-image-gen", makeArgs({ referenceImages: ["/tmp/a.png", "/tmp/b.png"] })),
  );
});
