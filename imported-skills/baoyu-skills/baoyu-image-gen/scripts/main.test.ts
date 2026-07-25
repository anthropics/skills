import assert from "node:assert/strict";
import fs from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import test, { type TestContext } from "node:test";

import type { CliArgs, ExtendConfig } from "./types.ts";
import {
  createTaskArgs,
  detectProvider,
  ensureDir,
  getConfiguredMaxWorkers,
  getConfiguredProviderRateLimits,
  getWorkerCount,
  isRetryableGenerationError,
  loadBatchTasks,
  loadExtendConfig,
  mergeConfig,
  normalizeOutputImagePath,
  parseArgs,
  parseOpenAIImageApiDialect,
  parseSimpleYaml,
  validateReferenceImages,
} from "./main.ts";

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

async function makeTempDir(prefix: string): Promise<string> {
  return fs.mkdtemp(path.join(os.tmpdir(), prefix));
}

test("parseArgs parses the main baoyu-image-gen CLI flags", () => {
  const args = parseArgs([
    "--promptfiles",
    "prompts/system.md",
    "prompts/content.md",
    "--image",
    "out/hero",
    "--provider",
    "zai",
    "--quality",
    "2k",
    "--imageSize",
    "4k",
    "--imageApiDialect",
    "ratio-metadata",
    "--ref",
    "ref/one.png",
    "ref/two.jpg",
    "--n",
    "3",
    "--jobs",
    "5",
    "--json",
  ]);

  assert.deepEqual(args.promptFiles, ["prompts/system.md", "prompts/content.md"]);
  assert.equal(args.imagePath, "out/hero");
  assert.equal(args.provider, "zai");
  assert.equal(args.quality, "2k");
  assert.equal(args.aspectRatioSource, null);
  assert.equal(args.imageSize, "4K");
  assert.equal(args.imageSizeSource, "cli");
  assert.equal(args.imageApiDialect, "ratio-metadata");
  assert.deepEqual(args.referenceImages, ["ref/one.png", "ref/two.jpg"]);
  assert.equal(args.n, 3);
  assert.equal(args.jobs, 5);
  assert.equal(args.json, true);
});

test("parseArgs falls back to positional prompt and rejects invalid provider", () => {
  const positional = parseArgs(["draw", "a", "cat"]);
  assert.equal(positional.prompt, "draw a cat");

  assert.throws(
    () => parseArgs(["--provider", "stability"]),
    /Invalid provider/,
  );
});

test("validateReferenceImages can skip remote URLs for providers that support them", async () => {
  await validateReferenceImages(["https://example.com/ref.png"], { allowRemoteUrls: true });

  await assert.rejects(
    () => validateReferenceImages(["https://example.com/ref.png"]),
    /Reference image not found/,
  );
});

test("parseSimpleYaml parses nested defaults and provider limits", () => {
  const yaml = `
version: 2
default_provider: openrouter
default_quality: normal
default_aspect_ratio: '16:9'
default_image_size: 2K
default_image_api_dialect: ratio-metadata
default_model:
  google: gemini-3-pro-image
  openai: gpt-image-2
  zai: glm-image
  azure: image-prod
  minimax: image-01
batch:
  max_workers: 8
  provider_limits:
    google:
      concurrency: 2
      start_interval_ms: 900
    openai:
      concurrency: 4
    zai:
      concurrency: 2
      start_interval_ms: 1000
    minimax:
      concurrency: 2
      start_interval_ms: 1400
    azure:
      concurrency: 1
      start_interval_ms: 1500
`;

  const config = parseSimpleYaml(yaml);

  assert.equal(config.version, 2);
  assert.equal(config.default_provider, "openrouter");
  assert.equal(config.default_quality, "normal");
  assert.equal(config.default_aspect_ratio, "16:9");
  assert.equal(config.default_image_size, "2K");
  assert.equal(config.default_image_api_dialect, "ratio-metadata");
  assert.equal(config.default_model?.google, "gemini-3-pro-image");
  assert.equal(config.default_model?.openai, "gpt-image-2");
  assert.equal(config.default_model?.zai, "glm-image");
  assert.equal(config.default_model?.azure, "image-prod");
  assert.equal(config.default_model?.minimax, "image-01");
  assert.equal(config.batch?.max_workers, 8);
  assert.deepEqual(config.batch?.provider_limits?.google, {
    concurrency: 2,
    start_interval_ms: 900,
  });
  assert.deepEqual(config.batch?.provider_limits?.openai, {
    concurrency: 4,
  });
  assert.deepEqual(config.batch?.provider_limits?.zai, {
    concurrency: 2,
    start_interval_ms: 1000,
  });
  assert.deepEqual(config.batch?.provider_limits?.minimax, {
    concurrency: 2,
    start_interval_ms: 1400,
  });
  assert.deepEqual(config.batch?.provider_limits?.azure, {
    concurrency: 1,
    start_interval_ms: 1500,
  });
});

test("ensureDir creates nested dirs, is idempotent on an existing dir, and rethrows for a non-directory", async (t: TestContext) => {
  const root = await makeTempDir("ensure-dir-");
  t.after(() => fs.rm(root, { recursive: true, force: true }));

  const nested = path.join(root, "a", "b", "c");
  await ensureDir(nested);
  assert.equal((await fs.stat(nested)).isDirectory(), true);

  // Idempotent: a second call on an existing directory must not throw. This is the
  // Bun-on-Windows regression the helper guards against (Bun wrongly throws EEXIST
  // for mkdir(existingDir, { recursive: true })).
  await ensureDir(nested);

  // Rethrows when the path exists but is a file rather than a directory, so a real
  // EEXIST against a non-directory is not silently swallowed.
  const filePath = path.join(root, "not-a-dir");
  await fs.writeFile(filePath, "x");
  await assert.rejects(() => ensureDir(filePath));
});

test("loadExtendConfig renames legacy EXTEND.md when the new path is missing", async () => {
  const root = await makeTempDir("baoyu-image-gen-extend-");
  const cwd = path.join(root, "project");
  const home = path.join(root, "home");
  const legacyPath = path.join(cwd, ".baoyu-skills", "baoyu-imagine", "EXTEND.md");
  const currentPath = path.join(cwd, ".baoyu-skills", "baoyu-image-gen", "EXTEND.md");

  await fs.mkdir(path.dirname(legacyPath), { recursive: true });
  await fs.mkdir(home, { recursive: true });
  await fs.writeFile(legacyPath, `---
default_provider: google
default_quality: 2k
---
`);

  const config = await loadExtendConfig(cwd, home);

  assert.equal(config.default_provider, "google");
  assert.equal(config.default_quality, "2k");
  await fs.access(currentPath);
  await assert.rejects(() => fs.access(legacyPath));
});

test("loadExtendConfig leaves legacy EXTEND.md untouched when both paths exist", async () => {
  const root = await makeTempDir("baoyu-image-gen-extend-dual-");
  const cwd = path.join(root, "project");
  const home = path.join(root, "home");
  const legacyPath = path.join(cwd, ".baoyu-skills", "baoyu-imagine", "EXTEND.md");
  const currentPath = path.join(cwd, ".baoyu-skills", "baoyu-image-gen", "EXTEND.md");

  await fs.mkdir(path.dirname(legacyPath), { recursive: true });
  await fs.mkdir(path.dirname(currentPath), { recursive: true });
  await fs.mkdir(home, { recursive: true });
  await fs.writeFile(legacyPath, `---
default_provider: google
---
`);
  await fs.writeFile(currentPath, `---
default_provider: openai
---
`);

  const config = await loadExtendConfig(cwd, home);

  assert.equal(config.default_provider, "openai");
  assert.equal(await fs.readFile(legacyPath, "utf8"), `---
default_provider: google
---
`);
  assert.equal(await fs.readFile(currentPath, "utf8"), `---
default_provider: openai
---
`);
});

test("mergeConfig only fills values missing from CLI args", () => {
  const merged = mergeConfig(
    makeArgs({
      provider: "openai",
      quality: null,
      aspectRatio: null,
      imageSize: "4K",
    }),
    {
      default_provider: "google",
      default_quality: "2k",
      default_aspect_ratio: "3:2",
      default_image_size: "2K",
      default_image_api_dialect: "ratio-metadata",
    } satisfies Partial<ExtendConfig>,
  );

  assert.equal(merged.provider, "openai");
  assert.equal(merged.quality, "2k");
  assert.equal(merged.aspectRatio, "3:2");
  assert.equal(merged.aspectRatioSource, "config");
  assert.equal(merged.imageSize, "4K");
  assert.equal(merged.imageSizeSource, "cli");
  assert.equal(merged.imageApiDialect, "ratio-metadata");
});

test("mergeConfig tags inherited imageSize defaults so providers can ignore incompatible config", () => {
  const merged = mergeConfig(
    makeArgs(),
    {
      default_image_size: "2K",
    } satisfies Partial<ExtendConfig>,
  );

  assert.equal(merged.imageSize, "2K");
  assert.equal(merged.imageSizeSource, "config");
});

test("mergeConfig falls back to OPENAI_IMAGE_API_DIALECT when CLI and EXTEND are unset", (t) => {
  useEnv(t, {
    OPENAI_IMAGE_API_DIALECT: "ratio-metadata",
  });

  const merged = mergeConfig(makeArgs(), {});
  assert.equal(merged.imageApiDialect, "ratio-metadata");
});

test("parseOpenAIImageApiDialect validates supported values", () => {
  assert.equal(parseOpenAIImageApiDialect("openai-native"), "openai-native");
  assert.equal(parseOpenAIImageApiDialect("ratio-metadata"), "ratio-metadata");
  assert.equal(parseOpenAIImageApiDialect(null), null);
  assert.throws(
    () => parseOpenAIImageApiDialect("gateway-magic"),
    /Invalid OpenAI image API dialect/,
  );
});

test("detectProvider rejects non-ref-capable providers and prefers Google first when multiple keys exist", (t) => {
  assert.throws(
    () =>
      detectProvider(
        makeArgs({
          provider: "zai",
          referenceImages: ["ref.png"],
        }),
      ),
    /Reference images require a ref-capable provider/,
  );

  useEnv(t, {
    GOOGLE_API_KEY: "google-key",
    OPENAI_API_KEY: "openai-key",
    OPENROUTER_API_KEY: null,
    DASHSCOPE_API_KEY: null,
    MINIMAX_API_KEY: null,
    REPLICATE_API_TOKEN: null,
    JIMENG_ACCESS_KEY_ID: null,
    JIMENG_SECRET_ACCESS_KEY: null,
    ARK_API_KEY: null,
  });
  assert.equal(detectProvider(makeArgs()), "google");
});

test("detectProvider selects an available ref-capable provider for reference-image tasks", (t) => {
  useEnv(t, {
    GOOGLE_API_KEY: null,
    OPENAI_API_KEY: "openai-key",
    AZURE_OPENAI_API_KEY: null,
    AZURE_OPENAI_BASE_URL: null,
    OPENROUTER_API_KEY: null,
    DASHSCOPE_API_KEY: null,
    MINIMAX_API_KEY: null,
    REPLICATE_API_TOKEN: null,
    JIMENG_ACCESS_KEY_ID: null,
    JIMENG_SECRET_ACCESS_KEY: null,
    ARK_API_KEY: null,
  });
  assert.equal(
    detectProvider(makeArgs({ referenceImages: ["ref.png"] })),
    "openai",
  );
});

test("detectProvider selects Azure when only Azure credentials are configured", (t) => {
  useEnv(t, {
    GOOGLE_API_KEY: null,
    OPENAI_API_KEY: null,
    AZURE_OPENAI_API_KEY: "azure-key",
    AZURE_OPENAI_BASE_URL: "https://example.openai.azure.com",
    OPENROUTER_API_KEY: null,
    DASHSCOPE_API_KEY: null,
    MINIMAX_API_KEY: null,
    REPLICATE_API_TOKEN: null,
    JIMENG_ACCESS_KEY_ID: null,
    JIMENG_SECRET_ACCESS_KEY: null,
    ARK_API_KEY: null,
  });

  assert.equal(detectProvider(makeArgs()), "azure");
  assert.equal(
    detectProvider(makeArgs({ referenceImages: ["ref.png"] })),
    "azure",
  );
});

test("detectProvider selects Z.AI when credentials are present or the model id matches", (t) => {
  useEnv(t, {
    GOOGLE_API_KEY: null,
    OPENAI_API_KEY: null,
    AZURE_OPENAI_API_KEY: null,
    AZURE_OPENAI_BASE_URL: null,
    OPENROUTER_API_KEY: null,
    DASHSCOPE_API_KEY: null,
    ZAI_API_KEY: "zai-key",
    BIGMODEL_API_KEY: null,
    MINIMAX_API_KEY: null,
    REPLICATE_API_TOKEN: null,
    JIMENG_ACCESS_KEY_ID: null,
    JIMENG_SECRET_ACCESS_KEY: null,
    ARK_API_KEY: null,
  });

  assert.equal(detectProvider(makeArgs()), "zai");
  assert.equal(detectProvider(makeArgs({ model: "glm-image" })), "zai");
});

test("detectProvider infers Seedream from model id and allows Seedream reference-image workflows", (t) => {
  useEnv(t, {
    GOOGLE_API_KEY: null,
    OPENAI_API_KEY: null,
    OPENROUTER_API_KEY: null,
    DASHSCOPE_API_KEY: null,
    MINIMAX_API_KEY: null,
    REPLICATE_API_TOKEN: null,
    JIMENG_ACCESS_KEY_ID: null,
    JIMENG_SECRET_ACCESS_KEY: null,
    ARK_API_KEY: "ark-key",
  });

  assert.equal(
    detectProvider(
      makeArgs({
        model: "doubao-seedream-4-5-251128",
        referenceImages: ["ref.png"],
      }),
    ),
    "seedream",
  );

  assert.equal(
    detectProvider(
      makeArgs({
        provider: "seedream",
        referenceImages: ["ref.png"],
      }),
    ),
    "seedream",
  );
});

test("detectProvider allows DashScope reference-image workflows when explicitly chosen for wan2.7 models", (t) => {
  useEnv(t, {
    GOOGLE_API_KEY: null,
    OPENAI_API_KEY: null,
    AZURE_OPENAI_API_KEY: null,
    AZURE_OPENAI_BASE_URL: null,
    OPENROUTER_API_KEY: null,
    DASHSCOPE_API_KEY: "dashscope-key",
    MINIMAX_API_KEY: null,
    REPLICATE_API_TOKEN: null,
    JIMENG_ACCESS_KEY_ID: null,
    JIMENG_SECRET_ACCESS_KEY: null,
    ARK_API_KEY: null,
  });

  assert.equal(
    detectProvider(
      makeArgs({
        provider: "dashscope",
        model: "wan2.7-image-pro",
        referenceImages: ["ref.png"],
      }),
    ),
    "dashscope",
  );
});

test("detectProvider selects MiniMax when only MiniMax credentials are configured or the model id matches", (t) => {
  useEnv(t, {
    GOOGLE_API_KEY: null,
    OPENAI_API_KEY: null,
    AZURE_OPENAI_API_KEY: null,
    AZURE_OPENAI_BASE_URL: null,
    OPENROUTER_API_KEY: null,
    DASHSCOPE_API_KEY: null,
    MINIMAX_API_KEY: "minimax-key",
    REPLICATE_API_TOKEN: null,
    JIMENG_ACCESS_KEY_ID: null,
    JIMENG_SECRET_ACCESS_KEY: null,
    ARK_API_KEY: null,
  });

  assert.equal(detectProvider(makeArgs()), "minimax");
  assert.equal(detectProvider(makeArgs({ referenceImages: ["ref.png"] })), "minimax");
  assert.equal(detectProvider(makeArgs({ model: "image-01-live" })), "minimax");
});

test("batch worker and provider-rate-limit configuration prefer env over EXTEND config", (t) => {
  useEnv(t, {
    BAOYU_IMAGE_GEN_MAX_WORKERS: "12",
    BAOYU_IMAGE_GEN_GOOGLE_CONCURRENCY: "5",
    BAOYU_IMAGE_GEN_GOOGLE_START_INTERVAL_MS: "450",
    BAOYU_IMAGE_GEN_ZAI_CONCURRENCY: "4",
  });

  const extendConfig: Partial<ExtendConfig> = {
    batch: {
      max_workers: 7,
      provider_limits: {
        google: {
          concurrency: 2,
          start_interval_ms: 900,
        },
        zai: {
          concurrency: 1,
          start_interval_ms: 1200,
        },
        minimax: {
          concurrency: 1,
          start_interval_ms: 1500,
        },
      },
    },
  };

  assert.equal(getConfiguredMaxWorkers(extendConfig), 12);
  assert.deepEqual(getConfiguredProviderRateLimits(extendConfig).google, {
    concurrency: 5,
    startIntervalMs: 450,
  });
  assert.deepEqual(getConfiguredProviderRateLimits(extendConfig).zai, {
    concurrency: 4,
    startIntervalMs: 1200,
  });
  assert.deepEqual(getConfiguredProviderRateLimits(extendConfig).minimax, {
    concurrency: 1,
    startIntervalMs: 1500,
  });
});

test("loadBatchTasks and createTaskArgs resolve batch-relative paths", async (t) => {
  const root = await makeTempDir("baoyu-image-gen-batch-");
  t.after(() => fs.rm(root, { recursive: true, force: true }));

  const batchFile = path.join(root, "jobs", "batch.json");
  await fs.mkdir(path.dirname(batchFile), { recursive: true });
  await fs.writeFile(
    batchFile,
    JSON.stringify({
      jobs: 2,
      tasks: [
        {
          id: "hero",
          promptFiles: ["prompts/hero.md"],
          image: "out/hero",
          ref: ["refs/hero.png", "https://example.com/ref.png"],
          ar: "16:9",
        },
      ],
    }),
  );

  const loaded = await loadBatchTasks(batchFile);
  assert.equal(loaded.jobs, 2);
  assert.equal(loaded.batchDir, path.dirname(batchFile));
  assert.equal(loaded.tasks[0]?.id, "hero");

  const taskArgs = createTaskArgs(
    makeArgs({
      provider: "replicate",
      quality: "2k",
      imageApiDialect: "ratio-metadata",
      json: true,
    }),
    loaded.tasks[0]!,
    loaded.batchDir,
  );

  assert.deepEqual(taskArgs.promptFiles, [
    path.join(loaded.batchDir, "prompts/hero.md"),
  ]);
  assert.equal(taskArgs.imagePath, path.join(loaded.batchDir, "out/hero"));
  assert.deepEqual(taskArgs.referenceImages, [
    path.join(loaded.batchDir, "refs/hero.png"),
    "https://example.com/ref.png",
  ]);
  assert.equal(taskArgs.provider, "replicate");
  assert.equal(taskArgs.aspectRatio, "16:9");
  assert.equal(taskArgs.quality, "2k");
  assert.equal(taskArgs.imageApiDialect, "ratio-metadata");
  assert.equal(taskArgs.json, true);
});

test("path normalization, worker count, and retry classification follow expected rules", () => {
  assert.match(normalizeOutputImagePath("out/sample"), /out[\\/]+sample\.png$/);
  assert.match(normalizeOutputImagePath("out/sample", ".jpg"), /out[\\/]+sample\.jpg$/);
  assert.match(normalizeOutputImagePath("out/sample.webp"), /out[\\/]+sample\.webp$/);

  assert.equal(getWorkerCount(8, null, 3), 3);
  assert.equal(getWorkerCount(2, 6, 5), 2);
  assert.equal(getWorkerCount(5, 0, 4), 1);

  assert.equal(isRetryableGenerationError(new Error("API error (401): denied")), false);
  assert.equal(
    isRetryableGenerationError(
      new Error("Replicate returned 2 outputs, but baoyu-image-gen currently supports saving exactly one image per request."),
    ),
    false,
  );
  assert.equal(
    isRetryableGenerationError(
      new Error("DashScope wan2.7 image models accept at most 9 reference images. Received 10."),
    ),
    false,
  );
  assert.equal(
    isRetryableGenerationError(
      new Error("DashScope wan2.7 image models in baoyu-image-gen support exactly one output image per request."),
    ),
    false,
  );
  assert.equal(
    isRetryableGenerationError(
      new Error("DashScope wan2.7 image models support aspect ratios in [1:8, 8:1]."),
    ),
    false,
  );
  assert.equal(
    isRetryableGenerationError(
      new Error("DashScope wan2.7-image requires total pixels between 768*768 and 2048*2048."),
    ),
    false,
  );
  assert.equal(isRetryableGenerationError(new Error("socket hang up")), true);
});
