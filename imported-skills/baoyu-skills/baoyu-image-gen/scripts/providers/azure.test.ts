import assert from "node:assert/strict";
import fs from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import test, { type TestContext } from "node:test";

import type { CliArgs } from "../types.ts";
import {
  generateImage,
  getDefaultModel,
  parseAzureBaseURL,
  validateArgs,
} from "./azure.ts";

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

async function makeTempDir(prefix: string): Promise<string> {
  return fs.mkdtemp(path.join(os.tmpdir(), prefix));
}

test("Azure endpoint parsing and default deployment selection follow env precedence", (t) => {
  assert.deepEqual(parseAzureBaseURL("https://example.openai.azure.com"), {
    resourceBaseURL: "https://example.openai.azure.com/openai",
    deployment: null,
  });
  assert.deepEqual(
    parseAzureBaseURL("https://example.openai.azure.com/openai/deployments/from-url"),
    {
      resourceBaseURL: "https://example.openai.azure.com/openai",
      deployment: "from-url",
    },
  );

  useEnv(t, {
    AZURE_OPENAI_BASE_URL: "https://example.openai.azure.com/openai/deployments/from-url",
    AZURE_OPENAI_DEPLOYMENT: "explicit-deploy",
    AZURE_OPENAI_IMAGE_MODEL: "env-fallback",
  });
  assert.equal(getDefaultModel(), "explicit-deploy");
});

test("Azure validateArgs rejects unsupported edit input formats before the API call", () => {
  assert.doesNotThrow(() =>
    validateArgs("demo-deployment", makeArgs({ referenceImages: ["hero.png", "photo.jpeg"] })),
  );
  assert.throws(
    () => validateArgs("demo-deployment", makeArgs({ referenceImages: ["hero.webp"] })),
    /PNG or JPG\/JPEG/,
  );
});

test("Azure image generation routes model to deployment and sends mapped quality", async (t) => {
  useEnv(t, {
    AZURE_OPENAI_API_KEY: "azure-key",
    AZURE_OPENAI_BASE_URL: "https://example.openai.azure.com/openai/deployments/default-deploy",
    AZURE_API_VERSION: null,
    AZURE_OPENAI_DEPLOYMENT: null,
    AZURE_OPENAI_IMAGE_MODEL: null,
  });

  const originalFetch = globalThis.fetch;
  t.after(() => {
    globalThis.fetch = originalFetch;
  });

  const calls: Array<{ url: string; body: string }> = [];
  globalThis.fetch = async (input, init) => {
    calls.push({
      url: String(input),
      body: String(init?.body ?? ""),
    });
    return Response.json({
      data: [{ b64_json: Buffer.from("azure-image").toString("base64") }],
    });
  };

  const bytes = await generateImage(
    "A calm lake at sunset",
    "custom-deploy",
    makeArgs({ quality: "normal" }),
  );

  assert.equal(Buffer.from(bytes).toString("utf8"), "azure-image");
  assert.equal(
    calls[0]?.url,
    "https://example.openai.azure.com/openai/deployments/custom-deploy/images/generations?api-version=2025-04-01-preview",
  );

  const body = JSON.parse(calls[0]!.body) as Record<string, string>;
  assert.equal(body.quality, "medium");
  assert.equal(body.size, "1024x1024");
});

test("Azure image edits include quality in multipart requests", async (t) => {
  const root = await makeTempDir("baoyu-image-gen-azure-");
  t.after(() => fs.rm(root, { recursive: true, force: true }));

  const pngPath = path.join(root, "ref.png");
  const jpgPath = path.join(root, "ref.jpg");
  await fs.writeFile(pngPath, "png-bytes");
  await fs.writeFile(jpgPath, "jpg-bytes");

  useEnv(t, {
    AZURE_OPENAI_API_KEY: "azure-key",
    AZURE_OPENAI_BASE_URL: "https://example.openai.azure.com",
    AZURE_API_VERSION: "2025-04-01-preview",
    AZURE_OPENAI_DEPLOYMENT: null,
    AZURE_OPENAI_IMAGE_MODEL: null,
  });

  const originalFetch = globalThis.fetch;
  t.after(() => {
    globalThis.fetch = originalFetch;
  });

  const calls: Array<{ url: string; form: FormData }> = [];
  globalThis.fetch = async (input, init) => {
    calls.push({
      url: String(input),
      form: init?.body as FormData,
    });
    return Response.json({
      data: [{ b64_json: Buffer.from("edited-image").toString("base64") }],
    });
  };

  const bytes = await generateImage(
    "Add warm lighting",
    "edit-deploy",
    makeArgs({
      quality: "2k",
      referenceImages: [pngPath, jpgPath],
    }),
  );

  assert.equal(Buffer.from(bytes).toString("utf8"), "edited-image");
  assert.equal(
    calls[0]?.url,
    "https://example.openai.azure.com/openai/deployments/edit-deploy/images/edits?api-version=2025-04-01-preview",
  );
  assert.equal(calls[0]?.form.get("quality"), "high");
  assert.equal(calls[0]?.form.get("size"), "1024x1024");
  assert.equal(calls[0]?.form.getAll("image[]").length, 2);
});
