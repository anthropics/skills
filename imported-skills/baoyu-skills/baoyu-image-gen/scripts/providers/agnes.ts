import { readFile } from "node:fs/promises";
import path from "node:path";
import type { CliArgs } from "../types";

const DEFAULT_MODEL = "agnes-image-2.1-flash";
const DEFAULT_BASE_URL = "https://apihub.agnes-ai.com/v1";
const DEFAULT_SIZE = "1024x1024";

type AgnesResponse = {
  created?: number;
  data: Array<{ url?: string; b64_json?: string }>;
};

export function getDefaultModel(): string {
  return process.env.AGNES_IMAGE_MODEL || DEFAULT_MODEL;
}

function getApiKey(): string {
  const key = process.env.AGNES_API_KEY;
  if (!key) {
    throw new Error("AGNES_API_KEY is required. Get one from https://apihub.agnes-ai.com.");
  }
  return key;
}

function getBaseUrl(): string {
  return (process.env.AGNES_BASE_URL || DEFAULT_BASE_URL).replace(/\/+$/, "");
}

export function parseAspectRatio(ar: string): { width: number; height: number } | null {
  const match = ar.match(/^(\d+(?:\.\d+)?):(\d+(?:\.\d+)?)$/);
  if (!match) return null;
  const w = parseFloat(match[1]!);
  const h = parseFloat(match[2]!);
  if (w <= 0 || h <= 0) return null;
  return { width: w, height: h };
}

export function snapDim(n: number): number {
  return Math.max(32, Math.round(n / 32) * 32);
}

export function resolveSize(args: Pick<CliArgs, "size" | "aspectRatio">): string {
  if (args.size) return args.size;

  if (args.aspectRatio) {
    const parsed = parseAspectRatio(args.aspectRatio);
    if (parsed) {
      if (parsed.width === 1 && parsed.height === 1) return "1024x1024";
      const maxEdge = 2048;
      const scale = Math.max(1, Math.floor(maxEdge / Math.max(parsed.width, parsed.height)));
      const width = parsed.width * scale;
      const height = parsed.height * scale;
      return `${snapDim(width)}x${snapDim(height)}`;
    }
  }

  return DEFAULT_SIZE;
}

function isRemoteUrl(refPath: string): boolean {
  return /^https?:\/\//i.test(refPath);
}

export async function resolveReferenceImages(
  referenceImages: string[]
): Promise<string[]> {
  const result: string[] = [];
  for (const refPath of referenceImages) {
    if (isRemoteUrl(refPath)) {
      result.push(refPath);
      continue;
    }
    const bytes = await readFile(refPath);
    const ext = path.extname(refPath).toLowerCase();
    let mime = "image/png";
    if (ext === ".jpg" || ext === ".jpeg") mime = "image/jpeg";
    else if (ext === ".webp") mime = "image/webp";
    else if (ext === ".gif") mime = "image/gif";
    const b64 = Buffer.from(bytes).toString("base64");
    result.push(`data:${mime};base64,${b64}`);
  }
  return result;
}

export function validateArgs(_model: string, args: CliArgs): void {
  if (args.n > 1) {
    throw new Error("Agnes image generation currently returns a single image per request. Set --n 1 or omit --n.");
  }
}

export function getDefaultOutputExtension(_model: string, args: CliArgs): string {
  return args.responseFormat === "url" ? ".txt" : ".png";
}

export function buildRequestBody(
  prompt: string,
  model: string,
  args: Pick<CliArgs, "size" | "aspectRatio" | "referenceImages">
): Record<string, unknown> {
  const body: Record<string, unknown> = {
    model,
    prompt,
    size: resolveSize(args),
  };

  if (args.referenceImages.length > 0) {
    body.image = args.referenceImages;
  }

  body.extra_body = { response_format: "url" };

  return body;
}

export async function extractImageFromResponse(result: AgnesResponse): Promise<Uint8Array> {
  const img = result.data[0];

  if (img?.b64_json) {
    return Uint8Array.from(Buffer.from(img.b64_json, "base64"));
  }

  if (img?.url) {
    const imgRes = await fetch(img.url);
    if (!imgRes.ok) throw new Error(`Failed to download image from Agnes: ${imgRes.status}`);
    return new Uint8Array(await imgRes.arrayBuffer());
  }

  throw new Error("No image in Agnes response");
}

export async function generateImage(
  prompt: string,
  model: string,
  args: CliArgs
): Promise<Uint8Array> {
  const apiKey = getApiKey();
  const baseUrl = getBaseUrl();

  const referenceImages = await resolveReferenceImages(args.referenceImages);

  const body = buildRequestBody(prompt, model, { ...args, referenceImages });

  const controller = new AbortController();
  const timeout = setTimeout(() => controller.abort(), 120_000);

  try {
    const res = await fetch(`${baseUrl}/images/generations`, {
      method: "POST",
      headers: {
        "Content-Type": "application/json",
        Authorization: `Bearer ${apiKey}`,
      },
      body: JSON.stringify(body),
      signal: controller.signal,
    });

    if (!res.ok) {
      const err = await res.text();
      throw new Error(`Agnes API error (${res.status}): ${err}`);
    }

    const result = (await res.json()) as AgnesResponse;

    if (args.responseFormat === "url") {
      const url = result.data[0]?.url;
      if (!url) throw new Error("No URL in Agnes response");
      return new Uint8Array(Buffer.from(url, "utf-8"));
    }

    return extractImageFromResponse(result);
  } finally {
    clearTimeout(timeout);
  }
}
