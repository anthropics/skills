import path from "node:path";
import { readFile } from "node:fs/promises";
import type { CliArgs } from "../types";

const DEFAULT_MODEL = "google/gemini-3.1-flash-image";
const COMMON_ASPECT_RATIOS = [
  "1:1",
  "2:3",
  "3:2",
  "3:4",
  "4:3",
  "4:5",
  "5:4",
  "9:16",
  "16:9",
  "21:9",
];
const GEMINI_EXTENDED_ASPECT_RATIOS = ["1:4", "4:1", "1:8", "8:1"];

type OpenRouterImageEntry = {
  image_url?: string | { url?: string | null } | null;
  imageUrl?: string | { url?: string | null } | null;
};

type OpenRouterMessagePart = {
  type?: string;
  text?: string;
  image_url?: string | { url?: string | null } | null;
  imageUrl?: string | { url?: string | null } | null;
};

type OpenRouterResponse = {
  choices?: Array<{
    finish_reason?: string | null;
    native_finish_reason?: string | null;
    message?: {
      images?: OpenRouterImageEntry[];
      content?: string | OpenRouterMessagePart[] | null;
    };
  }>;
};

export function getDefaultModel(): string {
  return process.env.OPENROUTER_IMAGE_MODEL || DEFAULT_MODEL;
}

function normalizeModelId(model: string): string {
  return model.trim().toLowerCase().split(":")[0]!;
}

function isTextAndImageModel(model: string): boolean {
  const normalized = normalizeModelId(model);
  if (normalized === "openrouter/auto") {
    return true;
  }

  if (normalized.startsWith("google/gemini-") && normalized.includes("image")) {
    return true;
  }

  if (normalized.startsWith("openai/gpt-") && normalized.includes("image")) {
    return true;
  }

  return false;
}

function getSupportedAspectRatios(model: string): Set<string> {
  const normalized = normalizeModelId(model);
  if (
    normalized !== "google/gemini-3.1-flash-image" &&
    normalized !== "google/gemini-3.1-flash-image-preview"
  ) {
    return new Set(COMMON_ASPECT_RATIOS);
  }

  return new Set([...COMMON_ASPECT_RATIOS, ...GEMINI_EXTENDED_ASPECT_RATIOS]);
}

function getApiKey(): string | null {
  return process.env.OPENROUTER_API_KEY || null;
}

function getBaseUrl(): string {
  const base = process.env.OPENROUTER_BASE_URL || "https://openrouter.ai/api/v1";
  return base.replace(/\/+$/g, "");
}

function getHeaders(apiKey: string): Record<string, string> {
  const headers: Record<string, string> = {
    "Content-Type": "application/json",
    Authorization: `Bearer ${apiKey}`,
  };

  const referer = process.env.OPENROUTER_HTTP_REFERER?.trim();
  if (referer) {
    headers["HTTP-Referer"] = referer;
  }

  const title = process.env.OPENROUTER_TITLE?.trim();
  if (title) {
    headers["X-OpenRouter-Title"] = title;
    headers["X-Title"] = title;
  }

  return headers;
}

function parsePixelSize(value: string): { width: number; height: number } | null {
  const match = value.match(/^(\d+)\s*[xX]\s*(\d+)$/);
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

function inferAspectRatio(size: string | null): string | null {
  if (!size) return null;
  const parsed = parsePixelSize(size);
  if (!parsed) return null;

  const divisor = gcd(parsed.width, parsed.height);
  return `${parsed.width / divisor}:${parsed.height / divisor}`;
}

function inferImageSize(size: string | null): "1K" | "2K" | "4K" | null {
  if (!size) return null;
  const parsed = parsePixelSize(size);
  if (!parsed) return null;

  const longestEdge = Math.max(parsed.width, parsed.height);
  if (longestEdge <= 1024) return "1K";
  if (longestEdge <= 2048) return "2K";
  return "4K";
}

export function getImageSize(args: CliArgs): "1K" | "2K" | "4K" | null {
  if (args.imageSize) return args.imageSize as "1K" | "2K" | "4K";

  const inferredFromSize = inferImageSize(args.size);
  if (inferredFromSize) return inferredFromSize;

  if (args.quality === "normal") return "1K";
  if (args.quality === "2k") return "2K";
  return null;
}

export function getAspectRatio(model: string, args: CliArgs): string | null {
  if (args.aspectRatio) return args.aspectRatio;

  const inferred = inferAspectRatio(args.size);
  if (!inferred || !getSupportedAspectRatios(model).has(inferred)) {
    return null;
  }

  return inferred;
}

function getModalities(model: string): string[] {
  return isTextAndImageModel(model) ? ["image", "text"] : ["image"];
}

export function validateArgs(model: string, args: CliArgs): void {
  const requestedAspectRatio = args.aspectRatio || inferAspectRatio(args.size);
  if (!requestedAspectRatio) {
    return;
  }

  const supported = getSupportedAspectRatios(model);
  if (supported.has(requestedAspectRatio)) {
    return;
  }

  const requestedValue = args.aspectRatio
    ? `aspect ratio ${requestedAspectRatio}`
    : `size ${args.size} (aspect ratio ${requestedAspectRatio})`;

  throw new Error(
    `OpenRouter model ${model} does not support ${requestedValue}. Supported values: ${Array.from(supported).join(", ")}`
  );
}

function getMimeType(filename: string): string {
  const ext = path.extname(filename).toLowerCase();
  if (ext === ".jpg" || ext === ".jpeg") return "image/jpeg";
  if (ext === ".webp") return "image/webp";
  if (ext === ".gif") return "image/gif";
  return "image/png";
}

async function readImageAsDataUrl(filePath: string): Promise<string> {
  const bytes = await readFile(filePath);
  return `data:${getMimeType(filePath)};base64,${bytes.toString("base64")}`;
}

export function buildContent(
  prompt: string,
  referenceImages: string[],
): string | Array<Record<string, unknown>> {
  if (referenceImages.length === 0) {
    return prompt;
  }

  const content: Array<Record<string, unknown>> = [{ type: "text", text: prompt }];

  for (const imageUrl of referenceImages) {
    content.push({
      type: "image_url",
      image_url: { url: imageUrl },
    });
  }

  return content;
}

function extractImageUrl(entry: OpenRouterImageEntry | OpenRouterMessagePart): string | null {
  const value = entry.image_url ?? entry.imageUrl;
  if (!value) return null;
  if (typeof value === "string") return value;
  return value.url ?? null;
}

function decodeDataUrl(value: string): Uint8Array | null {
  const match = value.match(/^data:image\/[^;]+;base64,([A-Za-z0-9+/=]+)$/);
  if (!match) return null;
  return Uint8Array.from(Buffer.from(match[1]!, "base64"));
}

async function downloadImage(value: string): Promise<Uint8Array> {
  const inline = decodeDataUrl(value);
  if (inline) return inline;

  if (value.startsWith("http://") || value.startsWith("https://")) {
    const response = await fetch(value);
    if (!response.ok) {
      throw new Error(`Failed to download OpenRouter image: ${response.status}`);
    }
    const buffer = await response.arrayBuffer();
    return new Uint8Array(buffer);
  }

  return Uint8Array.from(Buffer.from(value, "base64"));
}

export async function extractImageFromResponse(result: OpenRouterResponse): Promise<Uint8Array> {
  const choice = result.choices?.[0];
  const message = choice?.message;

  for (const image of message?.images ?? []) {
    const imageUrl = extractImageUrl(image);
    if (imageUrl) return downloadImage(imageUrl);
  }

  if (Array.isArray(message?.content)) {
    for (const item of message.content) {
      const imageUrl = extractImageUrl(item);
      if (imageUrl) return downloadImage(imageUrl);

      if (item.type === "text" && item.text) {
        const inline = decodeDataUrl(item.text);
        if (inline) return inline;
      }
    }
  } else if (typeof message?.content === "string") {
    const inline = decodeDataUrl(message.content);
    if (inline) return inline;
  }

  const finishReason =
    choice?.native_finish_reason || choice?.finish_reason || "unknown";
  throw new Error(
    `No image in OpenRouter response (finish_reason=${finishReason})`,
  );
}

export function buildRequestBody(
  prompt: string,
  model: string,
  args: CliArgs,
  referenceImages: string[],
): Record<string, unknown> {
  validateArgs(model, args);

  const imageConfig: Record<string, string> = {};

  const imageSize = getImageSize(args);
  if (imageSize) {
    imageConfig.image_size = imageSize;
  }

  const aspectRatio = getAspectRatio(model, args);
  if (aspectRatio) {
    imageConfig.aspect_ratio = aspectRatio;
  }

  const body: Record<string, unknown> = {
    messages: [
      {
        role: "user",
        content: buildContent(prompt, referenceImages),
      },
    ],
    modalities: getModalities(model),
    stream: false,
  };

  if (Object.keys(imageConfig).length > 0) {
    body.image_config = imageConfig;
    body.provider = {
      require_parameters: true,
    };
  }

  return body;
}

export async function generateImage(
  prompt: string,
  model: string,
  args: CliArgs
): Promise<Uint8Array> {
  const apiKey = getApiKey();
  if (!apiKey) {
    throw new Error("OPENROUTER_API_KEY is required. Get one at https://openrouter.ai/settings/keys");
  }

  const referenceImages: string[] = [];
  for (const refPath of args.referenceImages) {
    referenceImages.push(await readImageAsDataUrl(refPath));
  }

  const body = {
    model,
    ...buildRequestBody(prompt, model, args, referenceImages),
  };

  console.log(
    `Generating image with OpenRouter (${model})...`,
    (body.image_config as Record<string, string>),
  );

  const response = await fetch(`${getBaseUrl()}/chat/completions`, {
    method: "POST",
    headers: getHeaders(apiKey),
    body: JSON.stringify(body),
  });

  if (!response.ok) {
    const errorText = await response.text();
    throw new Error(`OpenRouter API error (${response.status}): ${errorText}`);
  }

  const result = (await response.json()) as OpenRouterResponse;
  return extractImageFromResponse(result);
}
