import type { CliArgs, Quality } from "../types";

type ZaiModelFamily = "glm" | "legacy";

type ZaiRequestBody = {
  model: string;
  prompt: string;
  quality: "hd" | "standard";
  size: string;
};

type ZaiResponse = {
  data?: Array<{ url?: string }>;
};

const DEFAULT_MODEL = "glm-image";
const GLM_MAX_PIXELS = 2 ** 22;
const LEGACY_MAX_PIXELS = 2 ** 21;
const GLM_SIZE_STEP = 32;
const LEGACY_SIZE_STEP = 16;

const GLM_RECOMMENDED_SIZES: Record<string, string> = {
  "1:1": "1280x1280",
  "3:2": "1568x1056",
  "2:3": "1056x1568",
  "4:3": "1472x1088",
  "3:4": "1088x1472",
  "16:9": "1728x960",
  "9:16": "960x1728",
};

const LEGACY_RECOMMENDED_SIZES: Record<string, string> = {
  "1:1": "1024x1024",
  "9:16": "768x1344",
  "3:4": "864x1152",
  "16:9": "1344x768",
  "4:3": "1152x864",
  "2:1": "1440x720",
  "1:2": "720x1440",
};

export function getDefaultModel(): string {
  return process.env.ZAI_IMAGE_MODEL || process.env.BIGMODEL_IMAGE_MODEL || DEFAULT_MODEL;
}

function getApiKey(): string | null {
  return process.env.ZAI_API_KEY || process.env.BIGMODEL_API_KEY || null;
}

export function buildZaiUrl(): string {
  const base = (process.env.ZAI_BASE_URL || process.env.BIGMODEL_BASE_URL || "https://api.z.ai/api/paas/v4")
    .replace(/\/+$/g, "");
  if (base.endsWith("/images/generations")) return base;
  if (base.endsWith("/api/paas/v4")) return `${base}/images/generations`;
  if (base.endsWith("/v4")) return `${base}/images/generations`;
  return `${base}/api/paas/v4/images/generations`;
}

export function getModelFamily(model: string): ZaiModelFamily {
  return model.trim().toLowerCase() === "glm-image" ? "glm" : "legacy";
}

export function parseAspectRatio(ar: string): { width: number; height: number } | null {
  const match = ar.match(/^(\d+(?:\.\d+)?):(\d+(?:\.\d+)?)$/);
  if (!match) return null;
  const width = Number(match[1]);
  const height = Number(match[2]);
  if (!Number.isFinite(width) || !Number.isFinite(height) || width <= 0 || height <= 0) {
    return null;
  }
  return { width, height };
}

export function parseSize(size: string): { width: number; height: number } | null {
  const match = size.trim().match(/^(\d+)\s*[xX*]\s*(\d+)$/);
  if (!match) return null;
  const width = parseInt(match[1]!, 10);
  const height = parseInt(match[2]!, 10);
  if (!Number.isFinite(width) || !Number.isFinite(height) || width <= 0 || height <= 0) {
    return null;
  }
  return { width, height };
}

function formatSize(width: number, height: number): string {
  return `${width}x${height}`;
}

function roundToStep(value: number, step: number): number {
  return Math.max(step, Math.round(value / step) * step);
}

function getRatioValue(ar: string): number | null {
  const parsed = parseAspectRatio(ar);
  if (!parsed) return null;
  return parsed.width / parsed.height;
}

function findClosestRatioKey(ar: string, candidates: string[]): string | null {
  const targetRatio = getRatioValue(ar);
  if (targetRatio == null) return null;

  let bestKey: string | null = null;
  let bestDiff = Infinity;
  for (const candidate of candidates) {
    const candidateRatio = getRatioValue(candidate);
    if (candidateRatio == null) continue;
    const diff = Math.abs(candidateRatio - targetRatio);
    if (diff < bestDiff) {
      bestDiff = diff;
      bestKey = candidate;
    }
  }

  return bestDiff <= 0.05 ? bestKey : null;
}

function getTargetPixels(quality: Quality): number {
  return quality === "normal" ? 1024 * 1024 : 1536 * 1536;
}

function fitToPixelBudget(
  width: number,
  height: number,
  targetPixels: number,
  maxPixels: number,
  step: number,
): { width: number; height: number } {
  let nextWidth = width;
  let nextHeight = height;
  const pixels = nextWidth * nextHeight;

  if (pixels > maxPixels) {
    const scale = Math.sqrt(maxPixels / pixels);
    nextWidth *= scale;
    nextHeight *= scale;
  } else {
    const scale = Math.sqrt(targetPixels / pixels);
    nextWidth *= scale;
    nextHeight *= scale;
  }

  let roundedWidth = roundToStep(nextWidth, step);
  let roundedHeight = roundToStep(nextHeight, step);
  let roundedPixels = roundedWidth * roundedHeight;

  while (roundedPixels > maxPixels && (roundedWidth > step || roundedHeight > step)) {
    if (roundedWidth >= roundedHeight && roundedWidth > step) {
      roundedWidth -= step;
    } else if (roundedHeight > step) {
      roundedHeight -= step;
    } else {
      break;
    }
    roundedPixels = roundedWidth * roundedHeight;
  }

  return { width: roundedWidth, height: roundedHeight };
}

function validateCustomSize(
  size: string,
  family: ZaiModelFamily,
): string {
  const parsed = parseSize(size);
  if (!parsed) {
    throw new Error("Z.AI --size must be in WxH format, for example 1280x1280.");
  }

  const widthStep = family === "glm" ? GLM_SIZE_STEP : LEGACY_SIZE_STEP;
  const minEdge = family === "glm" ? 1024 : 512;
  const maxPixels = family === "glm" ? GLM_MAX_PIXELS : LEGACY_MAX_PIXELS;

  if (parsed.width < minEdge || parsed.width > 2048 || parsed.height < minEdge || parsed.height > 2048) {
    throw new Error(
      family === "glm"
        ? "GLM-image custom size requires width and height between 1024 and 2048."
        : "Z.AI legacy image models require width and height between 512 and 2048."
    );
  }

  if (parsed.width % widthStep !== 0 || parsed.height % widthStep !== 0) {
    throw new Error(
      family === "glm"
        ? "GLM-image custom size requires width and height divisible by 32."
        : "Z.AI legacy image models require width and height divisible by 16."
    );
  }

  if (parsed.width * parsed.height > maxPixels) {
    throw new Error(
      family === "glm"
        ? "GLM-image custom size must not exceed 2^22 total pixels."
        : "Z.AI legacy image size must not exceed 2^21 total pixels."
    );
  }

  return formatSize(parsed.width, parsed.height);
}

export function resolveSizeForModel(
  model: string,
  args: Pick<CliArgs, "size" | "aspectRatio" | "quality">,
): string {
  const family = getModelFamily(model);
  const quality = args.quality === "normal" ? "normal" : "2k";

  if (args.size) {
    return validateCustomSize(args.size, family);
  }

  const recommended = family === "glm" ? GLM_RECOMMENDED_SIZES : LEGACY_RECOMMENDED_SIZES;
  const defaultSize = family === "glm" ? "1280x1280" : "1024x1024";

  if (!args.aspectRatio) return defaultSize;

  const recommendedRatio = findClosestRatioKey(args.aspectRatio, Object.keys(recommended));
  if (recommendedRatio) {
    return recommended[recommendedRatio]!;
  }

  const parsedRatio = parseAspectRatio(args.aspectRatio);
  if (!parsedRatio) return defaultSize;

  const targetPixels = getTargetPixels(quality);
  const maxPixels = family === "glm" ? GLM_MAX_PIXELS : LEGACY_MAX_PIXELS;
  const step = family === "glm" ? GLM_SIZE_STEP : LEGACY_SIZE_STEP;
  const fit = fitToPixelBudget(
    parsedRatio.width,
    parsedRatio.height,
    targetPixels,
    maxPixels,
    step,
  );
  return formatSize(fit.width, fit.height);
}

function getZaiQuality(quality: CliArgs["quality"]): "hd" | "standard" {
  return quality === "normal" ? "standard" : "hd";
}

export function validateArgs(_model: string, args: CliArgs): void {
  if (args.referenceImages.length > 0) {
    throw new Error("Z.AI GLM-image currently supports text-to-image only in baoyu-image-gen. Remove --ref or choose another provider.");
  }

  if (args.n > 1) {
    throw new Error("Z.AI image generation currently returns a single image per request in baoyu-image-gen.");
  }
}

export function buildRequestBody(
  prompt: string,
  model: string,
  args: CliArgs,
): ZaiRequestBody {
  validateArgs(model, args);
  return {
    model,
    prompt,
    quality: getZaiQuality(args.quality),
    size: resolveSizeForModel(model, args),
  };
}

export async function extractImageFromResponse(result: ZaiResponse): Promise<Uint8Array> {
  const url = result.data?.[0]?.url;
  if (!url) {
    throw new Error("No image URL in Z.AI response");
  }

  const imageResponse = await fetch(url);
  if (!imageResponse.ok) {
    throw new Error(`Failed to download image from Z.AI: ${imageResponse.status}`);
  }

  return new Uint8Array(await imageResponse.arrayBuffer());
}

export async function generateImage(
  prompt: string,
  model: string,
  args: CliArgs,
): Promise<Uint8Array> {
  const apiKey = getApiKey();
  if (!apiKey) {
    throw new Error("ZAI_API_KEY is required. Get one from https://docs.z.ai/.");
  }

  const response = await fetch(buildZaiUrl(), {
    method: "POST",
    headers: {
      "Content-Type": "application/json",
      Authorization: `Bearer ${apiKey}`,
    },
    body: JSON.stringify(buildRequestBody(prompt, model, args)),
  });

  if (!response.ok) {
    const err = await response.text();
    throw new Error(`Z.AI API error (${response.status}): ${err}`);
  }

  const result = (await response.json()) as ZaiResponse;
  return extractImageFromResponse(result);
}
