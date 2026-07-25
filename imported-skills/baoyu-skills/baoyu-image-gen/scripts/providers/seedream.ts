import path from "node:path";
import { readFile } from "node:fs/promises";

import type { CliArgs } from "../types";

export type SeedreamModelFamily =
  | "seedream5"
  | "seedream45"
  | "seedream40"
  | "seedream30"
  | "unknown";

type SeedreamRequestImage = string | string[];

type SeedreamRequestBody = {
  model: string;
  prompt: string;
  size: string;
  response_format: "url";
  watermark: boolean;
  image?: SeedreamRequestImage;
  output_format?: "png";
};

type SeedreamImageResponse = {
  model?: string;
  created?: number;
  data?: Array<{
    url?: string;
    b64_json?: string;
    size?: string;
    error?: {
      code?: string;
      message?: string;
    };
  }>;
  usage?: {
    generated_images: number;
    output_tokens: number;
    total_tokens: number;
  };
  error?: {
    code?: string;
    message?: string;
  };
};

export function getDefaultModel(): string {
  return process.env.SEEDREAM_IMAGE_MODEL || "doubao-seedream-5-0-260128";
}

function getApiKey(): string | null {
  return process.env.ARK_API_KEY || null;
}

function getBaseUrl(): string {
  return process.env.SEEDREAM_BASE_URL || "https://ark.cn-beijing.volces.com/api/v3";
}

function parsePixelSize(value: string): { width: number; height: number } | null {
  const match = value.trim().match(/^(\d+)\s*[xX]\s*(\d+)$/);
  if (!match) return null;

  const width = parseInt(match[1]!, 10);
  const height = parseInt(match[2]!, 10);
  if (!Number.isFinite(width) || !Number.isFinite(height) || width <= 0 || height <= 0) {
    return null;
  }

  return { width, height };
}

function normalizePixelSize(value: string): string | null {
  const parsed = parsePixelSize(value);
  if (!parsed) return null;
  return `${parsed.width}x${parsed.height}`;
}

function normalizeSizePreset(value: string): string | null {
  const upper = value.trim().toUpperCase();
  if (upper === "ADAPTIVE") return "adaptive";
  if (upper === "1K" || upper === "2K" || upper === "3K" || upper === "4K") return upper;
  return null;
}

function normalizeSizeValue(value: string): string | null {
  return normalizeSizePreset(value) ?? normalizePixelSize(value);
}

function getMimeType(filename: string): string {
  const ext = path.extname(filename).toLowerCase();
  if (ext === ".jpg" || ext === ".jpeg") return "image/jpeg";
  if (ext === ".webp") return "image/webp";
  if (ext === ".gif") return "image/gif";
  if (ext === ".bmp") return "image/bmp";
  if (ext === ".tiff" || ext === ".tif") return "image/tiff";
  return "image/png";
}

async function readImageAsDataUrl(filePath: string): Promise<string> {
  const bytes = await readFile(filePath);
  return `data:${getMimeType(filePath)};base64,${bytes.toString("base64")}`;
}

export function getModelFamily(model: string): SeedreamModelFamily {
  const normalized = model.trim();
  if (/^doubao-seedream-5-0(?:-lite)?-\d+$/.test(normalized)) return "seedream5";
  if (/^doubao-seedream-4-5-\d+$/.test(normalized)) return "seedream45";
  if (/^doubao-seedream-4-0-\d+$/.test(normalized)) return "seedream40";
  if (/^doubao-seedream-3-0-t2i-\d+$/.test(normalized)) return "seedream30";
  return "unknown";
}

function isRemovedSeededitModel(model: string): boolean {
  return /^doubao-seededit-3-0-i2i-\d+$/.test(model.trim());
}

function assertSupportedModel(model: string): void {
  if (isRemovedSeededitModel(model)) {
    throw new Error(
      `${model} is no longer supported. SeedEdit 3.0 support has been removed from this tool; use Seedream 5.0/4.5/4.0/3.0 instead.`
    );
  }
}

export function supportsReferenceImages(model: string): boolean {
  const family = getModelFamily(model);
  return family === "seedream5" || family === "seedream45" || family === "seedream40";
}

function supportsOutputFormat(model: string): boolean {
  return getModelFamily(model) === "seedream5";
}

export function getDefaultOutputExtension(model: string): ".png" | ".jpg" {
  assertSupportedModel(model);
  return supportsOutputFormat(model) ? ".png" : ".jpg";
}

export function getDefaultSeedreamSize(model: string, args: CliArgs): string {
  assertSupportedModel(model);
  const family = getModelFamily(model);

  if (family === "seedream5") return "2K";
  if (family === "seedream45") return "2K";
  if (family === "seedream40") return args.quality === "normal" ? "1K" : "2K";
  if (family === "seedream30") return args.quality === "2k" ? "2048x2048" : "1024x1024";
  return "2K";
}

export function resolveSeedreamSize(model: string, args: CliArgs): string {
  assertSupportedModel(model);
  const family = getModelFamily(model);
  const requested = args.size || args.imageSize || null;
  const normalized = requested ? normalizeSizeValue(requested) : null;

  if (!normalized) {
    return getDefaultSeedreamSize(model, args);
  }

  if (family === "seedream30") {
    const pixelSize = normalizePixelSize(normalized);
    if (!pixelSize) {
      throw new Error("Seedream 3.0 only supports explicit WxH sizes such as 1024x1024.");
    }
    return pixelSize;
  }

  if (family === "seedream5") {
    if (normalized === "4K" || normalized === "1K" || normalized === "adaptive") {
      throw new Error("Seedream 5.0 only supports 2K, 3K, or explicit WxH sizes.");
    }
    return normalized;
  }

  if (family === "seedream45") {
    if (normalized === "1K" || normalized === "3K" || normalized === "adaptive") {
      throw new Error("Seedream 4.5 only supports 2K, 4K, or explicit WxH sizes.");
    }
    return normalized;
  }

  if (family === "seedream40") {
    if (normalized === "3K" || normalized === "adaptive") {
      throw new Error("Seedream 4.0 only supports 1K, 2K, 4K, or explicit WxH sizes.");
    }
    return normalized;
  }

  if (normalized === "adaptive") {
    throw new Error("Adaptive size is not supported by Seedream image generation.");
  }

  if (normalized === "1K" || normalized === "3K" || normalized === "4K") {
    throw new Error(
      "Unknown Seedream model ID. Use a documented model ID or pass an explicit WxH size instead of preset imageSize."
    );
  }

  return normalized;
}

export function validateArgs(model: string, args: CliArgs): void {
  assertSupportedModel(model);
  const family = getModelFamily(model);
  const refCount = args.referenceImages.length;

  if (refCount === 0) {
    resolveSeedreamSize(model, args);
    return;
  }

  if (family === "unknown") {
    throw new Error(
      "Reference images with Seedream require a known model ID. Use Seedream 5.0/4.5/4.0 model IDs instead of an endpoint ID."
    );
  }

  if (!supportsReferenceImages(model)) {
    throw new Error(`${model} does not support reference images.`);
  }

  if ((family === "seedream5" || family === "seedream45" || family === "seedream40") && refCount > 14) {
    throw new Error(`${model} supports at most 14 reference images.`);
  }

  resolveSeedreamSize(model, args);
}

export async function buildImageInput(
  model: string,
  referenceImages: string[],
): Promise<SeedreamRequestImage | undefined> {
  if (referenceImages.length === 0) return undefined;
  assertSupportedModel(model);

  const encoded = await Promise.all(referenceImages.map((refPath) => readImageAsDataUrl(refPath)));

  return encoded.length === 1 ? encoded[0]! : encoded;
}

export function buildRequestBody(
  prompt: string,
  model: string,
  args: CliArgs,
  imageInput?: SeedreamRequestImage,
): SeedreamRequestBody {
  validateArgs(model, args);

  const requestBody: SeedreamRequestBody = {
    model,
    prompt,
    size: resolveSeedreamSize(model, args),
    response_format: "url",
    watermark: false,
  };

  if (imageInput) {
    requestBody.image = imageInput;
  }

  if (supportsOutputFormat(model)) {
    requestBody.output_format = "png";
  }

  return requestBody;
}

async function downloadImage(url: string): Promise<Uint8Array> {
  const imgResponse = await fetch(url);
  if (!imgResponse.ok) {
    throw new Error(`Failed to download image from ${url}`);
  }

  const buffer = await imgResponse.arrayBuffer();
  return new Uint8Array(buffer);
}

export async function extractImageFromResponse(result: SeedreamImageResponse): Promise<Uint8Array> {
  const first = result.data?.find((item) => item.url || item.b64_json || item.error);

  if (!first) {
    throw new Error("No image data in Seedream response");
  }

  if (first.error) {
    throw new Error(first.error.message || "Seedream returned an image generation error");
  }

  if (first.b64_json) {
    return Uint8Array.from(Buffer.from(first.b64_json, "base64"));
  }

  if (first.url) {
    console.error(`Downloading image from ${first.url}...`);
    return downloadImage(first.url);
  }

  throw new Error("No image URL or base64 data in Seedream response");
}

export async function generateImage(
  prompt: string,
  model: string,
  args: CliArgs,
): Promise<Uint8Array> {
  const apiKey = getApiKey();
  if (!apiKey) {
    throw new Error(
      "ARK_API_KEY is required. " +
        "Get your API key from https://console.volcengine.com/ark"
    );
  }

  validateArgs(model, args);
  const imageInput = await buildImageInput(model, args.referenceImages);
  const requestBody = buildRequestBody(prompt, model, args, imageInput);

  console.error(`Calling Seedream API (${model}) with size: ${requestBody.size}`);

  const response = await fetch(`${getBaseUrl()}/images/generations`, {
    method: "POST",
    headers: {
      "Content-Type": "application/json",
      Authorization: `Bearer ${apiKey}`,
    },
    body: JSON.stringify(requestBody),
  });

  if (!response.ok) {
    const err = await response.text();
    throw new Error(`Seedream API error (${response.status}): ${err}`);
  }

  const result = (await response.json()) as SeedreamImageResponse;
  if (result.error) {
    throw new Error(result.error.message || "Seedream API returned an error");
  }

  return extractImageFromResponse(result);
}
