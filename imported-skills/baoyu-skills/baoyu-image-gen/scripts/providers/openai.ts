import path from "node:path";
import { readFile } from "node:fs/promises";
import type { CliArgs, OpenAIImageApiDialect } from "../types";

export function getDefaultModel(): string {
  return process.env.OPENAI_IMAGE_MODEL || "gpt-image-2";
}

type OpenAIImageResponse = { data: Array<{ url?: string; b64_json?: string }> };

export function parseAspectRatio(ar: string): { width: number; height: number } | null {
  const match = ar.match(/^(\d+(?:\.\d+)?):(\d+(?:\.\d+)?)$/);
  if (!match) return null;
  const w = parseFloat(match[1]!);
  const h = parseFloat(match[2]!);
  if (w <= 0 || h <= 0) return null;
  return { width: w, height: h };
}

type SizeMapping = {
  square: string;
  landscape: string;
  portrait: string;
};

type OpenAIGenerationsBody = Record<string, unknown>;

function isGptImageModel(model: string): boolean {
  return model.includes("gpt-image");
}

function isGptImage2Model(model: string): boolean {
  return model.includes("gpt-image-2");
}

function roundToMultiple(value: number, multiple: number): number {
  return Math.max(multiple, Math.round(value / multiple) * multiple);
}

function buildGptImage2SizeFromAspectRatio(
  ar: string | null,
  quality: CliArgs["quality"],
): string {
  const parsed = ar ? parseAspectRatio(ar) : null;
  const ratio = parsed ? parsed.width / parsed.height : 1;

  if (!parsed || Math.abs(ratio - 1) < 0.1) {
    const edge = quality === "2k" ? 2048 : 1024;
    return `${edge}x${edge}`;
  }

  const targetLongEdge = quality === "2k" ? 2048 : 1024;
  let width: number;
  let height: number;

  if (ratio > 1) {
    width = targetLongEdge;
    height = roundToMultiple(width / ratio, 16);
  } else {
    height = targetLongEdge;
    width = roundToMultiple(height * ratio, 16);
  }

  while (width * height < 655_360) {
    if (ratio > 1) {
      width += 16;
      height = roundToMultiple(width / ratio, 16);
    } else {
      height += 16;
      width = roundToMultiple(height * ratio, 16);
    }
  }

  return `${width}x${height}`;
}

export function getOpenAISize(
  model: string,
  ar: string | null,
  quality: CliArgs["quality"]
): string {
  const isDalle3 = model.includes("dall-e-3");
  const isDalle2 = model.includes("dall-e-2");

  if (isDalle2) {
    return "1024x1024";
  }

  if (isGptImage2Model(model)) {
    return buildGptImage2SizeFromAspectRatio(ar, quality);
  }

  const sizes: SizeMapping = isDalle3
    ? {
        square: "1024x1024",
        landscape: "1792x1024",
        portrait: "1024x1792",
      }
    : {
        square: "1024x1024",
        landscape: "1536x1024",
        portrait: "1024x1536",
      };

  if (!ar) return sizes.square;

  const parsed = parseAspectRatio(ar);
  if (!parsed) return sizes.square;

  const ratio = parsed.width / parsed.height;

  if (Math.abs(ratio - 1) < 0.1) return sizes.square;
  if (ratio > 1.5) return sizes.landscape;
  if (ratio < 0.67) return sizes.portrait;
  return sizes.square;
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

export function getOpenAIImageApiDialect(args: Pick<CliArgs, "imageApiDialect">): OpenAIImageApiDialect {
  return args.imageApiDialect ?? "openai-native";
}

export function inferAspectRatioFromSize(size: string | null): string | null {
  if (!size) return null;
  const parsed = parsePixelSize(size);
  if (!parsed) return null;

  const divisor = gcd(parsed.width, parsed.height);
  return `${parsed.width / divisor}:${parsed.height / divisor}`;
}

export function inferResolutionFromSize(size: string | null): "1K" | "2K" | "4K" | null {
  if (!size) return null;
  const parsed = parsePixelSize(size);
  if (!parsed) return null;

  const longestEdge = Math.max(parsed.width, parsed.height);
  if (longestEdge <= 1024) return "1K";
  if (longestEdge <= 2048) return "2K";
  return "4K";
}

export function getOpenAIAspectRatio(args: Pick<CliArgs, "aspectRatio" | "size">): string {
  return args.aspectRatio ?? inferAspectRatioFromSize(args.size) ?? "1:1";
}

export function getOpenAIResolution(
  args: Pick<CliArgs, "imageSize" | "size" | "quality">
): "1K" | "2K" | "4K" {
  if (args.imageSize === "1K" || args.imageSize === "2K" || args.imageSize === "4K") {
    return args.imageSize;
  }

  const inferred = inferResolutionFromSize(args.size);
  if (inferred) return inferred;

  return args.quality === "normal" ? "1K" : "2K";
}

function getOpenAIQuality(model: string, quality: CliArgs["quality"]): "standard" | "hd" | "medium" | "high" | null {
  if (model.includes("dall-e-3")) {
    return quality === "2k" ? "hd" : "standard";
  }

  if (isGptImageModel(model)) {
    return quality === "2k" ? "high" : "medium";
  }

  return null;
}

export function getOrientationFromAspectRatio(ar: string): "landscape" | "portrait" | null {
  const parsed = parseAspectRatio(ar);
  if (!parsed) return null;

  const ratio = parsed.width / parsed.height;
  if (Math.abs(ratio - 1) < 0.1) return null;
  return ratio > 1 ? "landscape" : "portrait";
}

export function buildOpenAIGenerationsBody(
  prompt: string,
  model: string,
  args: Pick<CliArgs, "aspectRatio" | "size" | "quality" | "imageSize" | "imageApiDialect">
): OpenAIGenerationsBody {
  if (getOpenAIImageApiDialect(args) === "ratio-metadata") {
    const aspectRatio = getOpenAIAspectRatio(args);
    const metadata: Record<string, string> = {
      resolution: getOpenAIResolution(args),
    };
    const orientation = getOrientationFromAspectRatio(aspectRatio);
    if (orientation) metadata.orientation = orientation;

    return {
      model,
      prompt,
      size: aspectRatio,
      metadata,
    };
  }

  const body: OpenAIGenerationsBody = {
    model,
    prompt,
    size: args.size || getOpenAISize(model, args.aspectRatio, args.quality),
  };

  const quality = getOpenAIQuality(model, args.quality);
  if (quality) {
    body.quality = quality;
  }

  return body;
}

export function validateArgs(model: string, args: CliArgs): void {
  if (!isGptImage2Model(model)) return;

  if (args.aspectRatio && !args.size) {
    const parsed = parseAspectRatio(args.aspectRatio);
    if (!parsed) {
      throw new Error(`Invalid gpt-image-2 aspect ratio: ${args.aspectRatio}`);
    }
    const ratio = parsed.width / parsed.height;
    if (Math.max(ratio, 1 / ratio) > 3) {
      throw new Error("gpt-image-2 aspect ratio must not exceed 3:1.");
    }
  }

  if (!args.size) return;

  const parsedSize = parsePixelSize(args.size);
  if (!parsedSize) {
    throw new Error(`Invalid gpt-image-2 --size: ${args.size}. Expected <width>x<height>.`);
  }

  const { width, height } = parsedSize;
  const totalPixels = width * height;
  const ratio = Math.max(width, height) / Math.min(width, height);

  if (Math.max(width, height) > 3840) {
    throw new Error("gpt-image-2 --size maximum edge length must be 3840px or less.");
  }
  if (width % 16 !== 0 || height % 16 !== 0) {
    throw new Error("gpt-image-2 --size width and height must both be multiples of 16px.");
  }
  if (ratio > 3) {
    throw new Error("gpt-image-2 --size long edge to short edge ratio must not exceed 3:1.");
  }
  if (totalPixels < 655_360 || totalPixels > 8_294_400) {
    throw new Error("gpt-image-2 --size total pixels must be between 655,360 and 8,294,400.");
  }
}

export async function generateImage(
  prompt: string,
  model: string,
  args: CliArgs
): Promise<Uint8Array> {
  const baseURL = process.env.OPENAI_BASE_URL || "https://api.openai.com/v1";
  const apiKey = process.env.OPENAI_API_KEY;

  if (!apiKey) {
    throw new Error(
      "OPENAI_API_KEY is required. Codex/ChatGPT desktop login does not automatically grant OpenAI Images API access to this script."
    );
  }

  if (process.env.OPENAI_IMAGE_USE_CHAT === "true") {
    return generateWithChatCompletions(baseURL, apiKey, prompt, model);
  }

  const imageApiDialect = getOpenAIImageApiDialect(args);

  if (args.referenceImages.length > 0) {
    if (imageApiDialect !== "openai-native") {
      throw new Error(
        "Reference images are not supported with the ratio-metadata OpenAI dialect yet. Use openai-native, Google, Azure, OpenRouter, MiniMax, Seedream, or Replicate for image-edit workflows."
      );
    }
    if (model.includes("dall-e-2") || model.includes("dall-e-3")) {
      throw new Error(
        "Reference images with OpenAI in this skill require GPT Image models. Use --model gpt-image-2 (or another gpt-image model)."
      );
    }
    const size = args.size || getOpenAISize(model, args.aspectRatio, args.quality);
    return generateWithOpenAIEdits(baseURL, apiKey, prompt, model, size, args.referenceImages, args.quality);
  }

  return generateWithOpenAIGenerations(
    baseURL,
    apiKey,
    buildOpenAIGenerationsBody(prompt, model, args)
  );
}

async function generateWithChatCompletions(
  baseURL: string,
  apiKey: string,
  prompt: string,
  model: string
): Promise<Uint8Array> {
  const res = await fetch(`${baseURL}/chat/completions`, {
    method: "POST",
    headers: {
      "Content-Type": "application/json",
      Authorization: `Bearer ${apiKey}`,
    },
    body: JSON.stringify({
      model,
      messages: [{ role: "user", content: prompt }],
    }),
  });

  if (!res.ok) {
    const err = await res.text();
    throw new Error(`OpenAI API error: ${err}`);
  }

  const result = (await res.json()) as { choices: Array<{ message: { content: string } }> };
  const content = result.choices[0]?.message?.content ?? "";

  const match = content.match(/data:image\/[^;]+;base64,([A-Za-z0-9+/=]+)/);
  if (match) {
    return Uint8Array.from(Buffer.from(match[1]!, "base64"));
  }

  throw new Error("No image found in chat completions response");
}

async function generateWithOpenAIGenerations(
  baseURL: string,
  apiKey: string,
  body: OpenAIGenerationsBody
): Promise<Uint8Array> {
  const res = await fetch(`${baseURL}/images/generations`, {
    method: "POST",
    headers: {
      "Content-Type": "application/json",
      Authorization: `Bearer ${apiKey}`,
    },
    body: JSON.stringify(body),
  });

  if (!res.ok) {
    const err = await res.text();
    throw new Error(`OpenAI API error: ${err}`);
  }

  const result = (await res.json()) as OpenAIImageResponse;
  return extractImageFromResponse(result);
}

async function generateWithOpenAIEdits(
  baseURL: string,
  apiKey: string,
  prompt: string,
  model: string,
  size: string,
  referenceImages: string[],
  quality: CliArgs["quality"]
): Promise<Uint8Array> {
  const form = new FormData();
  form.append("model", model);
  form.append("prompt", prompt);
  form.append("size", size);

  const openAIQuality = getOpenAIQuality(model, quality);
  if (openAIQuality && openAIQuality !== "standard" && openAIQuality !== "hd") {
    form.append("quality", openAIQuality);
  }

  for (const refPath of referenceImages) {
    const bytes = await readFile(refPath);
    const filename = path.basename(refPath);
    const mimeType = getMimeType(filename);
    const blob = new Blob([bytes], { type: mimeType });
    form.append("image[]", blob, filename);
  }

  const res = await fetch(`${baseURL}/images/edits`, {
    method: "POST",
    headers: {
      Authorization: `Bearer ${apiKey}`,
    },
    body: form,
  });

  if (!res.ok) {
    const err = await res.text();
    throw new Error(`OpenAI edits API error: ${err}`);
  }

  const result = (await res.json()) as OpenAIImageResponse;
  return extractImageFromResponse(result);
}

export function getMimeType(filename: string): string {
  const ext = path.extname(filename).toLowerCase();
  if (ext === ".jpg" || ext === ".jpeg") return "image/jpeg";
  if (ext === ".webp") return "image/webp";
  if (ext === ".gif") return "image/gif";
  return "image/png";
}

export async function extractImageFromResponse(result: OpenAIImageResponse): Promise<Uint8Array> {
  const img = result.data[0];

  if (img?.b64_json) {
    return Uint8Array.from(Buffer.from(img.b64_json, "base64"));
  }

  if (img?.url) {
    const imgRes = await fetch(img.url);
    if (!imgRes.ok) throw new Error("Failed to download image");
    const buf = await imgRes.arrayBuffer();
    return new Uint8Array(buf);
  }

  throw new Error("No image in response");
}
