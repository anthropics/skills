import path from "node:path";
import { readFile } from "node:fs/promises";

import type { CliArgs } from "../types";

const DEFAULT_MODEL = "image-01";
const MAX_REFERENCE_IMAGE_BYTES = 10 * 1024 * 1024;
const SUPPORTED_ASPECT_RATIOS = new Set(["1:1", "16:9", "4:3", "3:2", "2:3", "3:4", "9:16", "21:9"]);

type MinimaxSubjectReference = {
  type: "character";
  image_file: string;
};

type MinimaxRequestBody = {
  model: string;
  prompt: string;
  response_format: "base64";
  aspect_ratio?: string;
  width?: number;
  height?: number;
  n?: number;
  subject_reference?: MinimaxSubjectReference[];
};

type MinimaxResponse = {
  id?: string;
  data?: {
    image_urls?: string[];
    image_base64?: string[];
  };
  base_resp?: {
    status_code?: number;
    status_msg?: string;
  };
};

export function getDefaultModel(): string {
  return process.env.MINIMAX_IMAGE_MODEL || DEFAULT_MODEL;
}

function getApiKey(): string | null {
  return process.env.MINIMAX_API_KEY || null;
}

export function buildMinimaxUrl(): string {
  const base = (process.env.MINIMAX_BASE_URL || "https://api.minimaxi.com").replace(/\/+$/g, "");
  return base.endsWith("/v1") ? `${base}/image_generation` : `${base}/v1/image_generation`;
}

function getMimeType(filename: string): "image/jpeg" | "image/png" {
  const ext = path.extname(filename).toLowerCase();
  if (ext === ".jpg" || ext === ".jpeg") return "image/jpeg";
  if (ext === ".png") return "image/png";
  throw new Error(
    `MiniMax subject_reference only supports JPG, JPEG, or PNG files: ${filename}`
  );
}

export function parsePixelSize(size: string): { width: number; height: number } | null {
  const match = size.trim().match(/^(\d+)\s*[xX*]\s*(\d+)$/);
  if (!match) return null;

  const width = parseInt(match[1]!, 10);
  const height = parseInt(match[2]!, 10);
  if (!Number.isFinite(width) || !Number.isFinite(height) || width <= 0 || height <= 0) {
    return null;
  }

  return { width, height };
}

function validatePixelSize(width: number, height: number): void {
  if (width < 512 || width > 2048 || height < 512 || height > 2048) {
    throw new Error("MiniMax custom size must keep width and height between 512 and 2048.");
  }
  if (width % 8 !== 0 || height % 8 !== 0) {
    throw new Error("MiniMax custom size requires width and height divisible by 8.");
  }
}

export function validateArgs(model: string, args: CliArgs): void {
  if (args.n > 9) {
    throw new Error("MiniMax supports at most 9 images per request.");
  }

  if (args.aspectRatio && !SUPPORTED_ASPECT_RATIOS.has(args.aspectRatio)) {
    throw new Error(
      `MiniMax aspect_ratio must be one of: ${Array.from(SUPPORTED_ASPECT_RATIOS).join(", ")}.`
    );
  }

  if (args.size && !args.aspectRatio) {
    if (model !== "image-01") {
      throw new Error("MiniMax custom --size is only supported with model image-01. Use --model image-01 or pass --ar instead.");
    }
    const parsed = parsePixelSize(args.size);
    if (!parsed) {
      throw new Error("MiniMax --size must be in WxH format, for example 1536x1024.");
    }
    validatePixelSize(parsed.width, parsed.height);
  }
}

export async function buildSubjectReference(
  referenceImages: string[],
): Promise<MinimaxSubjectReference[] | undefined> {
  if (referenceImages.length === 0) return undefined;

  const subjectReference: MinimaxSubjectReference[] = [];
  for (const refPath of referenceImages) {
    const bytes = await readFile(refPath);
    if (bytes.length > MAX_REFERENCE_IMAGE_BYTES) {
      throw new Error(`MiniMax subject_reference images must be smaller than 10MB: ${refPath}`);
    }

    subjectReference.push({
      type: "character",
      image_file: `data:${getMimeType(refPath)};base64,${bytes.toString("base64")}`,
    });
  }

  return subjectReference;
}

export async function buildRequestBody(
  prompt: string,
  model: string,
  args: CliArgs,
): Promise<MinimaxRequestBody> {
  validateArgs(model, args);

  const body: MinimaxRequestBody = {
    model,
    prompt,
    response_format: "base64",
  };

  if (args.aspectRatio) {
    body.aspect_ratio = args.aspectRatio;
  } else if (args.size) {
    const parsed = parsePixelSize(args.size);
    if (!parsed) {
      throw new Error("MiniMax --size must be in WxH format, for example 1536x1024.");
    }
    body.width = parsed.width;
    body.height = parsed.height;
  }

  if (args.n > 1) {
    body.n = args.n;
  }

  const subjectReference = await buildSubjectReference(args.referenceImages);
  if (subjectReference) {
    body.subject_reference = subjectReference;
  }

  return body;
}

async function downloadImage(url: string): Promise<Uint8Array> {
  const response = await fetch(url);
  if (!response.ok) {
    throw new Error(`Failed to download image from MiniMax: ${response.status}`);
  }
  return new Uint8Array(await response.arrayBuffer());
}

export async function extractImageFromResponse(result: MinimaxResponse): Promise<Uint8Array> {
  const baseResp = result.base_resp;
  if (baseResp && baseResp.status_code !== undefined && baseResp.status_code !== 0) {
    throw new Error(baseResp.status_msg || `MiniMax API returned status_code=${baseResp.status_code}`);
  }

  const base64Image = result.data?.image_base64?.[0];
  if (base64Image) {
    return Uint8Array.from(Buffer.from(base64Image, "base64"));
  }

  const url = result.data?.image_urls?.[0];
  if (url) {
    return downloadImage(url);
  }

  throw new Error("No image data in MiniMax response");
}

export function getDefaultOutputExtension(): ".jpg" {
  return ".jpg";
}

export async function generateImage(
  prompt: string,
  model: string,
  args: CliArgs
): Promise<Uint8Array> {
  const apiKey = getApiKey();
  if (!apiKey) {
    throw new Error("MINIMAX_API_KEY is required. Get one from https://platform.minimaxi.com/");
  }

  const body = await buildRequestBody(prompt, model, args);
  const response = await fetch(buildMinimaxUrl(), {
    method: "POST",
    headers: {
      "Content-Type": "application/json",
      Authorization: `Bearer ${apiKey}`,
    },
    body: JSON.stringify(body),
  });

  if (!response.ok) {
    const err = await response.text();
    throw new Error(`MiniMax API error (${response.status}): ${err}`);
  }

  const result = (await response.json()) as MinimaxResponse;
  return extractImageFromResponse(result);
}
