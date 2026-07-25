import path from "node:path";
import { readFile } from "node:fs/promises";
import type { CliArgs } from "../types";

const DEFAULT_MODEL = "google/nano-banana-2";
const SYNC_WAIT_SECONDS = 60;
const POLL_INTERVAL_MS = 2000;
const MAX_POLL_MS = 300_000;
const DOCUMENTED_REPLICATE_ASPECT_RATIOS = new Set([
  "1:1",
  "2:3",
  "3:2",
  "3:4",
  "4:3",
  "5:4",
  "4:5",
  "9:16",
  "16:9",
  "21:9",
]);

export type ReplicateModelFamily =
  | "nano-banana"
  | "seedream45"
  | "seedream5lite"
  | "wan27image"
  | "wan27imagepro"
  | "unknown";

type PixelSize = {
  width: number;
  height: number;
};

type Seedream45Size = "2K" | "4K" | { width: number; height: number };

export function getDefaultModel(): string {
  return process.env.REPLICATE_IMAGE_MODEL || DEFAULT_MODEL;
}

function getApiToken(): string | null {
  return process.env.REPLICATE_API_TOKEN || null;
}

function getBaseUrl(): string {
  const base = process.env.REPLICATE_BASE_URL || "https://api.replicate.com";
  return base.replace(/\/+$/g, "");
}

function normalizeModelId(model: string): string {
  return model.trim().toLowerCase().split(":")[0]!;
}

export function getModelFamily(model: string): ReplicateModelFamily {
  const normalized = normalizeModelId(model);

  if (
    normalized === "google/nano-banana" ||
    normalized === "google/nano-banana-pro" ||
    normalized === "google/nano-banana-2"
  ) {
    return "nano-banana";
  }

  if (normalized === "bytedance/seedream-4.5") {
    return "seedream45";
  }

  if (normalized === "bytedance/seedream-5-lite") {
    return "seedream5lite";
  }

  if (normalized === "wan-video/wan-2.7-image") {
    return "wan27image";
  }

  if (normalized === "wan-video/wan-2.7-image-pro") {
    return "wan27imagepro";
  }

  return "unknown";
}

export function parseModelId(model: string): { owner: string; name: string; version: string | null } {
  const [ownerName, version] = model.split(":");
  const parts = ownerName!.split("/");
  if (parts.length !== 2 || !parts[0] || !parts[1]) {
    throw new Error(
      `Invalid Replicate model format: "${model}". Expected "owner/name" or "owner/name:version".`
    );
  }
  return { owner: parts[0], name: parts[1], version: version || null };
}

function parsePixelSize(value: string): PixelSize | null {
  const match = value.trim().match(/^(\d+)\s*[xX*]\s*(\d+)$/);
  if (!match) return null;

  const width = parseInt(match[1]!, 10);
  const height = parseInt(match[2]!, 10);
  if (!Number.isFinite(width) || !Number.isFinite(height) || width <= 0 || height <= 0) {
    return null;
  }

  return { width, height };
}

function parseAspectRatio(value: string): PixelSize | null {
  const match = value.trim().match(/^(\d+)\s*:\s*(\d+)$/);
  if (!match) return null;

  const width = parseInt(match[1]!, 10);
  const height = parseInt(match[2]!, 10);
  if (!Number.isFinite(width) || !Number.isFinite(height) || width <= 0 || height <= 0) {
    return null;
  }

  return { width, height };
}

function gcd(a: number, b: number): number {
  let x = Math.abs(a);
  let y = Math.abs(b);

  while (y !== 0) {
    const next = x % y;
    x = y;
    y = next;
  }

  return x || 1;
}

function inferAspectRatioFromSize(size: string): string | null {
  const parsed = parsePixelSize(size);
  if (!parsed) return null;

  const divisor = gcd(parsed.width, parsed.height);
  const normalized = `${parsed.width / divisor}:${parsed.height / divisor}`;
  if (!DOCUMENTED_REPLICATE_ASPECT_RATIOS.has(normalized)) {
    return null;
  }

  return normalized;
}

function getQualityPreset(args: CliArgs): "normal" | "2k" {
  return args.quality === "normal" ? "normal" : "2k";
}

function validateDocumentedAspectRatio(model: string, aspectRatio: string): void {
  if (aspectRatio === "match_input_image") {
    return;
  }

  if (DOCUMENTED_REPLICATE_ASPECT_RATIOS.has(aspectRatio)) {
    return;
  }

  throw new Error(
    `Replicate model ${model} does not support aspect ratio ${aspectRatio}. Supported values: ${Array.from(DOCUMENTED_REPLICATE_ASPECT_RATIOS).join(", ")}`
  );
}

function getRequestedAspectRatio(model: string, args: CliArgs): string | null {
  if (args.aspectRatio) {
    validateDocumentedAspectRatio(model, args.aspectRatio);
    return args.aspectRatio;
  }

  if (!args.size) return null;

  const inferred = inferAspectRatioFromSize(args.size);
  if (!inferred) {
    throw new Error(
      `Replicate model ${model} cannot derive a supported aspect ratio from --size ${args.size}. Use one of: ${Array.from(DOCUMENTED_REPLICATE_ASPECT_RATIOS).join(", ")}`
    );
  }

  return inferred;
}

function getNanoBananaResolution(args: CliArgs): "1K" | "2K" {
  if (args.size) {
    const parsed = parsePixelSize(args.size);
    if (!parsed) {
      throw new Error("Replicate nano-banana --size must be in WxH format, for example 1536x1024.");
    }

    const longestEdge = Math.max(parsed.width, parsed.height);
    if (longestEdge <= 1024) return "1K";
    if (longestEdge <= 2048) return "2K";
    throw new Error("Replicate nano-banana only supports sizes that map to 1K or 2K output.");
  }

  return getQualityPreset(args) === "normal" ? "1K" : "2K";
}

function resolveSeedream45Size(args: CliArgs): Seedream45Size {
  if (args.size) {
    const upper = args.size.trim().toUpperCase();
    if (upper === "2K" || upper === "4K") {
      return upper;
    }

    const parsed = parsePixelSize(args.size);
    if (!parsed) {
      throw new Error("Replicate Seedream 4.5 --size must be 2K, 4K, or an explicit WxH size.");
    }
    if (parsed.width < 1024 || parsed.width > 4096 || parsed.height < 1024 || parsed.height > 4096) {
      throw new Error("Replicate Seedream 4.5 custom --size must keep width and height between 1024 and 4096.");
    }
    return parsed;
  }

  return getQualityPreset(args) === "normal" ? "2K" : "4K";
}

function resolveSeedream5LiteSize(args: CliArgs): "2K" | "3K" {
  if (args.size) {
    const upper = args.size.trim().toUpperCase();
    if (upper === "2K" || upper === "3K") {
      return upper;
    }

    throw new Error("Replicate Seedream 5 Lite currently supports 2K or 3K output in this tool.");
  }

  return getQualityPreset(args) === "normal" ? "2K" : "3K";
}

function formatCustomWanSize(size: PixelSize): string {
  return `${size.width}*${size.height}`;
}

function resolveWanSizeFromAspectRatio(
  aspectRatio: string,
  maxDimension: number,
): string {
  const parsedRatio = parseAspectRatio(aspectRatio);
  if (!parsedRatio) {
    throw new Error(`Replicate Wan aspect ratio must be in W:H format, got ${aspectRatio}.`);
  }

  const scale = Math.min(maxDimension / parsedRatio.width, maxDimension / parsedRatio.height);
  const width = Math.max(1, Math.floor(parsedRatio.width * scale));
  const height = Math.max(1, Math.floor(parsedRatio.height * scale));
  return formatCustomWanSize({ width, height });
}

function resolveWanSize(family: "wan27image" | "wan27imagepro", args: CliArgs): "1K" | "2K" | "4K" | string {
  const referenceMode = args.referenceImages.length > 0;
  const maxDimension = family === "wan27imagepro" && !referenceMode ? 4096 : 2048;

  if (args.size) {
    const upper = args.size.trim().toUpperCase();
    if (upper === "1K" || upper === "2K" || upper === "4K") {
      if (upper === "4K" && family !== "wan27imagepro") {
        throw new Error("Replicate Wan 2.7 Image only supports 1K, 2K, or custom sizes up to 2048px.");
      }
      if (upper === "4K" && referenceMode) {
        throw new Error("Replicate Wan 2.7 Image Pro only supports 4K text-to-image. Remove --ref or lower the size.");
      }
      return upper;
    }

    const parsed = parsePixelSize(args.size);
    if (!parsed) {
      throw new Error("Replicate Wan --size must be 1K, 2K, 4K, or an explicit WxH size.");
    }
    if (parsed.width > maxDimension || parsed.height > maxDimension) {
      throw new Error(
        `Replicate ${family === "wan27imagepro" ? "Wan 2.7 Image Pro" : "Wan 2.7 Image"} custom --size must keep width and height at or below ${maxDimension}px in the current mode.`
      );
    }
    return formatCustomWanSize(parsed);
  }

  if (args.aspectRatio) {
    return resolveWanSizeFromAspectRatio(
      args.aspectRatio,
      getQualityPreset(args) === "normal" ? 1024 : 2048,
    );
  }

  return getQualityPreset(args) === "normal" ? "1K" : "2K";
}

function buildNanoBananaInput(
  prompt: string,
  model: string,
  args: CliArgs,
  referenceImages: string[],
): Record<string, unknown> {
  const input: Record<string, unknown> = {
    prompt,
    resolution: getNanoBananaResolution(args),
    output_format: "png",
  };

  const aspectRatio = getRequestedAspectRatio(model, args);
  if (aspectRatio) {
    input.aspect_ratio = aspectRatio;
  } else if (referenceImages.length > 0) {
    input.aspect_ratio = "match_input_image";
  }

  if (referenceImages.length > 0) {
    input.image_input = referenceImages;
  }

  return input;
}

function buildSeedreamInput(
  family: "seedream45" | "seedream5lite",
  prompt: string,
  model: string,
  args: CliArgs,
  referenceImages: string[],
): Record<string, unknown> {
  const size = family === "seedream45" ? resolveSeedream45Size(args) : resolveSeedream5LiteSize(args);
  const input: Record<string, unknown> = {
    prompt,
  };

  if (family === "seedream45" && typeof size === "object") {
    input.size = "custom";
    input.width = size.width;
    input.height = size.height;
  } else {
    input.size = size;
  }

  if (referenceImages.length > 0) {
    input.image_input = referenceImages;
  }

  if (args.aspectRatio) {
    validateDocumentedAspectRatio(model, args.aspectRatio);
    input.aspect_ratio = args.aspectRatio;
  } else if (referenceImages.length > 0 && family === "seedream45") {
    input.aspect_ratio = "match_input_image";
  }

  return input;
}

function buildWanInput(
  family: "wan27image" | "wan27imagepro",
  prompt: string,
  args: CliArgs,
  referenceImages: string[],
): Record<string, unknown> {
  const input: Record<string, unknown> = {
    prompt,
    size: resolveWanSize(family, args),
  };

  if (referenceImages.length > 0) {
    input.images = referenceImages;
  }

  return input;
}

export function validateArgs(model: string, args: CliArgs): void {
  parseModelId(model);

  if (args.n !== 1) {
    throw new Error("Replicate integration currently supports exactly one output image per request. Remove --n or use --n 1.");
  }

  if (args.imageSize && args.imageSizeSource !== "config") {
    throw new Error("Replicate models in baoyu-image-gen do not use --imageSize. Use --quality, --ar, or --size instead.");
  }

  const family = getModelFamily(model);

  if (family === "nano-banana") {
    if (args.referenceImages.length > 14) {
      throw new Error("Replicate nano-banana supports at most 14 reference images.");
    }
    if (args.aspectRatio) {
      validateDocumentedAspectRatio(model, args.aspectRatio);
    }
    if (args.size) {
      getRequestedAspectRatio(model, args);
      getNanoBananaResolution(args);
    }
    return;
  }

  if (family === "seedream45") {
    if (args.referenceImages.length > 14) {
      throw new Error("Replicate Seedream 4.5 supports at most 14 reference images.");
    }
    if (args.aspectRatio) {
      validateDocumentedAspectRatio(model, args.aspectRatio);
    }
    resolveSeedream45Size(args);
    return;
  }

  if (family === "seedream5lite") {
    if (args.referenceImages.length > 14) {
      throw new Error("Replicate Seedream 5 Lite supports at most 14 reference images.");
    }
    if (args.aspectRatio) {
      validateDocumentedAspectRatio(model, args.aspectRatio);
    }
    resolveSeedream5LiteSize(args);
    return;
  }

  if (family === "wan27image" || family === "wan27imagepro") {
    if (args.referenceImages.length > 9) {
      throw new Error("Replicate Wan 2.7 image models support at most 9 reference images.");
    }
    if (args.aspectRatio) {
      const parsed = parseAspectRatio(args.aspectRatio);
      if (!parsed) {
        throw new Error(`Replicate Wan aspect ratio must be in W:H format, got ${args.aspectRatio}.`);
      }
    }
    resolveWanSize(family, args);
    return;
  }

  const hasExplicitAspectRatio = !!args.aspectRatio && args.aspectRatioSource !== "config";

  if (args.referenceImages.length > 0 || hasExplicitAspectRatio || args.size) {
    throw new Error(
      `Replicate model ${model} is not in the baoyu-image-gen compatibility list. Supported families: google/nano-banana*, bytedance/seedream-4.5, bytedance/seedream-5-lite, wan-video/wan-2.7-image, wan-video/wan-2.7-image-pro.`
    );
  }
}

export function getDefaultOutputExtension(model: string): ".png" {
  const _family = getModelFamily(model);
  return ".png";
}

export function buildInput(
  model: string,
  prompt: string,
  args: CliArgs,
  referenceImages: string[],
): Record<string, unknown> {
  const family = getModelFamily(model);

  if (family === "nano-banana") {
    return buildNanoBananaInput(prompt, model, args, referenceImages);
  }

  if (family === "seedream45" || family === "seedream5lite") {
    return buildSeedreamInput(family, prompt, model, args, referenceImages);
  }

  if (family === "wan27image" || family === "wan27imagepro") {
    return buildWanInput(family, prompt, args, referenceImages);
  }

  return { prompt };
}

async function readImageAsDataUrl(p: string): Promise<string> {
  const buf = await readFile(p);
  const ext = path.extname(p).toLowerCase();
  let mimeType = "image/png";
  if (ext === ".jpg" || ext === ".jpeg") mimeType = "image/jpeg";
  else if (ext === ".gif") mimeType = "image/gif";
  else if (ext === ".webp") mimeType = "image/webp";
  return `data:${mimeType};base64,${buf.toString("base64")}`;
}

type PredictionResponse = {
  id: string;
  status: string;
  output: unknown;
  error: string | null;
  urls?: { get?: string };
};

async function createPrediction(
  apiToken: string,
  model: { owner: string; name: string; version: string | null },
  input: Record<string, unknown>,
  sync: boolean
): Promise<PredictionResponse> {
  const baseUrl = getBaseUrl();

  let url: string;
  const body: Record<string, unknown> = { input };

  if (model.version) {
    url = `${baseUrl}/v1/predictions`;
    body.version = model.version;
  } else {
    url = `${baseUrl}/v1/models/${model.owner}/${model.name}/predictions`;
  }

  const headers: Record<string, string> = {
    Authorization: `Bearer ${apiToken}`,
    "Content-Type": "application/json",
  };

  if (sync) {
    headers["Prefer"] = `wait=${SYNC_WAIT_SECONDS}`;
  }

  const res = await fetch(url, {
    method: "POST",
    headers,
    body: JSON.stringify(body),
  });

  if (!res.ok) {
    const err = await res.text();
    throw new Error(`Replicate API error (${res.status}): ${err}`);
  }

  return (await res.json()) as PredictionResponse;
}

async function pollPrediction(apiToken: string, getUrl: string): Promise<PredictionResponse> {
  const start = Date.now();

  while (Date.now() - start < MAX_POLL_MS) {
    const res = await fetch(getUrl, {
      headers: { Authorization: `Bearer ${apiToken}` },
    });

    if (!res.ok) {
      const err = await res.text();
      throw new Error(`Replicate poll error (${res.status}): ${err}`);
    }

    const prediction = (await res.json()) as PredictionResponse;

    if (prediction.status === "succeeded") return prediction;
    if (prediction.status === "failed" || prediction.status === "canceled") {
      throw new Error(`Replicate prediction ${prediction.status}: ${prediction.error || "unknown error"}`);
    }

    await new Promise((r) => setTimeout(r, POLL_INTERVAL_MS));
  }

  throw new Error(`Replicate prediction timed out after ${MAX_POLL_MS / 1000}s`);
}

export function extractOutputUrl(prediction: PredictionResponse): string {
  const output = prediction.output;

  if (typeof output === "string") return output;

  if (Array.isArray(output)) {
    if (output.length !== 1) {
      throw new Error(
        `Replicate returned ${output.length} outputs, but baoyu-image-gen currently supports saving exactly one image per request.`
      );
    }
    const first = output[0];
    if (typeof first === "string") return first;
  }

  if (output && typeof output === "object" && "url" in output) {
    const url = (output as Record<string, unknown>).url;
    if (typeof url === "string") return url;
  }

  throw new Error(`Unexpected Replicate output format: ${JSON.stringify(output)}`);
}

async function downloadImage(url: string): Promise<Uint8Array> {
  const res = await fetch(url);
  if (!res.ok) throw new Error(`Failed to download image from Replicate: ${res.status}`);
  const buf = await res.arrayBuffer();
  return new Uint8Array(buf);
}

export async function generateImage(
  prompt: string,
  model: string,
  args: CliArgs
): Promise<Uint8Array> {
  const apiToken = getApiToken();
  if (!apiToken) throw new Error("REPLICATE_API_TOKEN is required. Get one at https://replicate.com/account/api-tokens");

  const parsedModel = parseModelId(model);
  validateArgs(model, args);

  const refDataUrls: string[] = [];
  for (const refPath of args.referenceImages) {
    refDataUrls.push(await readImageAsDataUrl(refPath));
  }

  const input = buildInput(model, prompt, args, refDataUrls);

  console.log(`Generating image with Replicate (${model})...`);

  let prediction = await createPrediction(apiToken, parsedModel, input, true);

  if (prediction.status !== "succeeded") {
    if (!prediction.urls?.get) {
      throw new Error("Replicate prediction did not return a poll URL");
    }
    console.log("Waiting for prediction to complete...");
    prediction = await pollPrediction(apiToken, prediction.urls.get);
  }

  console.log("Generation completed.");

  const outputUrl = extractOutputUrl(prediction);
  return downloadImage(outputUrl);
}
