import path from "node:path";
import { readFile } from "node:fs/promises";
import type { CliArgs, Quality } from "../types";

type DashScopeModelFamily = "qwen2" | "qwenFixed" | "wan27" | "legacy";

type DashScopeModelSpec = {
  family: DashScopeModelFamily;
  defaultSize: string;
};

const DEFAULT_MODEL = "qwen-image-2.0-pro";
const MIN_QWEN_2_TOTAL_PIXELS = 512 * 512;
const MAX_QWEN_2_TOTAL_PIXELS = 2048 * 2048;
const SIZE_STEP = 16;
const QWEN_NEGATIVE_PROMPT =
  "低分辨率，低画质，肢体畸形，手指畸形，画面过饱和，蜡像感，人脸无细节，过度光滑，画面具有AI感，构图混乱，文字模糊，扭曲";

const QWEN_2_TARGET_PIXELS: Record<Quality, number> = {
  normal: 1024 * 1024,
  "2k": 1536 * 1536,
};

const MIN_WAN27_TOTAL_PIXELS = 768 * 768;
const MAX_WAN27_PRO_T2I_PIXELS = 4096 * 4096;
const MAX_WAN27_GENERAL_PIXELS = 2048 * 2048;
const WAN27_MAX_REFERENCE_IMAGES = 9;

const WAN27_TARGET_PIXELS: Record<Quality, number> = {
  normal: 1024 * 1024,
  "2k": 2048 * 2048,
};

const QWEN_2_RECOMMENDED: Record<string, Record<Quality, string>> = {
  "1:1": { normal: "1024*1024", "2k": "1536*1536" },
  "2:3": { normal: "768*1152", "2k": "1024*1536" },
  "3:2": { normal: "1152*768", "2k": "1536*1024" },
  "3:4": { normal: "960*1280", "2k": "1080*1440" },
  "4:3": { normal: "1280*960", "2k": "1440*1080" },
  "9:16": { normal: "720*1280", "2k": "1080*1920" },
  "16:9": { normal: "1280*720", "2k": "1920*1080" },
  "21:9": { normal: "1344*576", "2k": "2048*872" },
};

const QWEN_FIXED_SIZES_BY_RATIO: Record<string, string> = {
  "16:9": "1664*928",
  "4:3": "1472*1104",
  "1:1": "1328*1328",
  "3:4": "1104*1472",
  "9:16": "928*1664",
};

const QWEN_FIXED_SIZES = Object.values(QWEN_FIXED_SIZES_BY_RATIO);

const LEGACY_STANDARD_SIZES: [number, number][] = [
  [1024, 1024],
  [1280, 720],
  [720, 1280],
  [1024, 768],
  [768, 1024],
  [1536, 1024],
  [1024, 1536],
  [1536, 864],
  [864, 1536],
];

const LEGACY_STANDARD_SIZES_2K: [number, number][] = [
  [1536, 1536],
  [2048, 1152],
  [1152, 2048],
  [1536, 1024],
  [1024, 1536],
  [1536, 864],
  [864, 1536],
  [2048, 2048],
];

const QWEN_2_SPEC: DashScopeModelSpec = {
  family: "qwen2",
  defaultSize: "1024*1024",
};

const QWEN_FIXED_SPEC: DashScopeModelSpec = {
  family: "qwenFixed",
  defaultSize: QWEN_FIXED_SIZES_BY_RATIO["16:9"],
};

const WAN27_SPEC: DashScopeModelSpec = {
  family: "wan27",
  defaultSize: "2048*2048",
};

const LEGACY_SPEC: DashScopeModelSpec = {
  family: "legacy",
  defaultSize: "1536*1536",
};

const MODEL_SPEC_ALIASES: Record<string, DashScopeModelSpec> = {
  "qwen-image-2.0-pro": QWEN_2_SPEC,
  "qwen-image-2.0-pro-2026-03-03": QWEN_2_SPEC,
  "qwen-image-2.0": QWEN_2_SPEC,
  "qwen-image-2.0-2026-03-03": QWEN_2_SPEC,
  "qwen-image-max": QWEN_FIXED_SPEC,
  "qwen-image-max-2025-12-30": QWEN_FIXED_SPEC,
  "qwen-image-plus": QWEN_FIXED_SPEC,
  "qwen-image-plus-2026-01-09": QWEN_FIXED_SPEC,
  "qwen-image": QWEN_FIXED_SPEC,
  "wan2.7-image-pro": WAN27_SPEC,
  "wan2.7-image": WAN27_SPEC,
};

export function getDefaultModel(): string {
  return process.env.DASHSCOPE_IMAGE_MODEL || DEFAULT_MODEL;
}

function getReferenceImageMime(filePath: string): string {
  const ext = path.extname(filePath).toLowerCase();
  if (ext === ".jpg" || ext === ".jpeg") return "image/jpeg";
  if (ext === ".webp") return "image/webp";
  if (ext === ".bmp") return "image/bmp";
  return "image/png";
}

async function loadReferenceImage(refPath: string): Promise<string> {
  if (/^https?:\/\//i.test(refPath)) {
    return refPath;
  }
  const fullPath = path.resolve(refPath);
  const bytes = await readFile(fullPath);
  return `data:${getReferenceImageMime(fullPath)};base64,${bytes.toString("base64")}`;
}

function getApiKey(): string | null {
  return process.env.DASHSCOPE_API_KEY || null;
}

function getBaseUrl(): string {
  const base = process.env.DASHSCOPE_BASE_URL || "https://dashscope.aliyuncs.com";
  return base.replace(/\/+$/g, "");
}

function getModelSpec(model: string): DashScopeModelSpec {
  return MODEL_SPEC_ALIASES[model.trim().toLowerCase()] || LEGACY_SPEC;
}

export function getModelFamily(model: string): DashScopeModelFamily {
  return getModelSpec(model).family;
}

function normalizeQuality(quality: CliArgs["quality"]): Quality {
  return quality === "normal" ? "normal" : "2k";
}

export function parseAspectRatio(ar: string): { width: number; height: number } | null {
  const match = ar.match(/^(\d+(?:\.\d+)?):(\d+(?:\.\d+)?)$/);
  if (!match) return null;
  const w = parseFloat(match[1]!);
  const h = parseFloat(match[2]!);
  if (w <= 0 || h <= 0) return null;
  return { width: w, height: h };
}

export function normalizeSize(size: string): string {
  return size.replace("x", "*");
}

export function parseSize(size: string): { width: number; height: number } | null {
  const match = normalizeSize(size).match(/^(\d+)\*(\d+)$/);
  if (!match) return null;
  const width = Number(match[1]);
  const height = Number(match[2]);
  if (!Number.isFinite(width) || !Number.isFinite(height) || width <= 0 || height <= 0) {
    return null;
  }
  return { width, height };
}

function formatSize(width: number, height: number): string {
  return `${width}*${height}`;
}

function getRatioValue(ar: string): number | null {
  const parsed = parseAspectRatio(ar);
  if (!parsed) return null;
  return parsed.width / parsed.height;
}

function findKnownRatioKey(ar: string, candidates: string[], tolerance = 0.02): string | null {
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

  return bestDiff <= tolerance ? bestKey : null;
}

function roundToStep(value: number): number {
  return Math.max(SIZE_STEP, Math.round(value / SIZE_STEP) * SIZE_STEP);
}

function floorToStep(value: number): number {
  return Math.max(SIZE_STEP, Math.floor(value / SIZE_STEP) * SIZE_STEP);
}

function fitToPixelBudget(
  width: number,
  height: number,
  minPixels: number,
  maxPixels: number,
): { width: number; height: number } {
  let nextWidth = width;
  let nextHeight = height;
  let pixels = nextWidth * nextHeight;

  if (pixels > maxPixels) {
    const scale = Math.sqrt(maxPixels / pixels);
    nextWidth *= scale;
    nextHeight *= scale;
  } else if (pixels < minPixels) {
    const scale = Math.sqrt(minPixels / pixels);
    nextWidth *= scale;
    nextHeight *= scale;
  }

  let roundedWidth = roundToStep(nextWidth);
  let roundedHeight = roundToStep(nextHeight);
  pixels = roundedWidth * roundedHeight;

  while (pixels > maxPixels && (roundedWidth > SIZE_STEP || roundedHeight > SIZE_STEP)) {
    if (roundedWidth >= roundedHeight && roundedWidth > SIZE_STEP) {
      roundedWidth -= SIZE_STEP;
    } else if (roundedHeight > SIZE_STEP) {
      roundedHeight -= SIZE_STEP;
    } else {
      break;
    }
    pixels = roundedWidth * roundedHeight;
  }

  while (pixels < minPixels) {
    if (roundedWidth <= roundedHeight) {
      roundedWidth += SIZE_STEP;
    } else {
      roundedHeight += SIZE_STEP;
    }
    pixels = roundedWidth * roundedHeight;
  }

  return { width: roundedWidth, height: roundedHeight };
}

function clampWan27DerivedSizeToRatioBounds(
  size: { width: number; height: number },
): { width: number; height: number } {
  let { width, height } = size;
  const ratio = width / height;

  if (ratio > 8) {
    width = floorToStep(height * 8);
  } else if (ratio < 1 / 8) {
    height = floorToStep(width * 8);
  }

  return { width, height };
}

export function getSizeFromAspectRatio(ar: string | null, quality: CliArgs["quality"]): string {
  const normalizedQuality = normalizeQuality(quality);
  const sizes = normalizedQuality === "2k" ? LEGACY_STANDARD_SIZES_2K : LEGACY_STANDARD_SIZES;
  const defaultSize = normalizedQuality === "2k" ? "1536*1536" : "1024*1024";

  if (!ar) return defaultSize;

  const parsed = parseAspectRatio(ar);
  if (!parsed) return defaultSize;

  const targetRatio = parsed.width / parsed.height;
  let best = defaultSize;
  let bestDiff = Infinity;

  for (const [width, height] of sizes) {
    const diff = Math.abs(width / height - targetRatio);
    if (diff < bestDiff) {
      bestDiff = diff;
      best = formatSize(width, height);
    }
  }

  return best;
}

export function getQwen2SizeFromAspectRatio(ar: string | null, quality: CliArgs["quality"]): string {
  const normalizedQuality = normalizeQuality(quality);

  if (!ar) {
    return QWEN_2_RECOMMENDED["1:1"][normalizedQuality];
  }

  const recommendedRatio = findKnownRatioKey(ar, Object.keys(QWEN_2_RECOMMENDED));
  if (recommendedRatio) {
    return QWEN_2_RECOMMENDED[recommendedRatio][normalizedQuality];
  }

  const parsed = parseAspectRatio(ar);
  if (!parsed) {
    return QWEN_2_RECOMMENDED["1:1"][normalizedQuality];
  }

  const targetRatio = parsed.width / parsed.height;
  const targetPixels = QWEN_2_TARGET_PIXELS[normalizedQuality];
  const rawWidth = Math.sqrt(targetPixels * targetRatio);
  const rawHeight = Math.sqrt(targetPixels / targetRatio);
  const fitted = fitToPixelBudget(
    rawWidth,
    rawHeight,
    MIN_QWEN_2_TOTAL_PIXELS,
    MAX_QWEN_2_TOTAL_PIXELS,
  );

  return formatSize(fitted.width, fitted.height);
}

function isWan27ProModel(model: string): boolean {
  return model.trim().toLowerCase() === "wan2.7-image-pro";
}

function getWan27MaxPixels(model: string, hasReferenceImages: boolean): number {
  if (isWan27ProModel(model) && !hasReferenceImages) {
    return MAX_WAN27_PRO_T2I_PIXELS;
  }
  return MAX_WAN27_GENERAL_PIXELS;
}

export function getWan27SizeFromAspectRatio(
  ar: string | null,
  quality: CliArgs["quality"],
  maxPixels: number,
): string {
  const normalizedQuality = normalizeQuality(quality);
  const targetPixels = Math.min(WAN27_TARGET_PIXELS[normalizedQuality], maxPixels);

  if (!ar) {
    const side = roundToStep(Math.sqrt(targetPixels));
    return formatSize(side, side);
  }

  const parsed = parseAspectRatio(ar);
  if (!parsed) {
    const side = roundToStep(Math.sqrt(targetPixels));
    return formatSize(side, side);
  }

  const ratio = parsed.width / parsed.height;
  if (ratio < 1 / 8 || ratio > 8) {
    throw new Error(
      `DashScope wan2.7 image models support aspect ratios in [1:8, 8:1]. Received "${ar}".`
    );
  }

  const rawWidth = Math.sqrt(targetPixels * ratio);
  const rawHeight = Math.sqrt(targetPixels / ratio);
  const fitted = fitToPixelBudget(
    rawWidth,
    rawHeight,
    MIN_WAN27_TOTAL_PIXELS,
    maxPixels,
  );
  const bounded = clampWan27DerivedSizeToRatioBounds(fitted);

  return formatSize(bounded.width, bounded.height);
}

function validateWan27Size(size: string, maxPixels: number, model: string): string {
  const normalized = normalizeSize(size);
  const parsed = validateSizeFormat(normalized);
  const totalPixels = parsed.width * parsed.height;
  if (totalPixels < MIN_WAN27_TOTAL_PIXELS || totalPixels > maxPixels) {
    const limit = maxPixels === MAX_WAN27_PRO_T2I_PIXELS ? "4096*4096" : "2048*2048";
    throw new Error(
      `DashScope ${model} requires total pixels between 768*768 and ${limit} ` +
      `for the current request. Received ${normalized} (${totalPixels} pixels).`
    );
  }
  const ratio = parsed.width / parsed.height;
  if (ratio < 1 / 8 || ratio > 8) {
    throw new Error(
      `DashScope wan2.7 image models support aspect ratios in [1:8, 8:1]. ` +
      `Received ${normalized} (ratio ${ratio.toFixed(3)}).`
    );
  }
  return normalized;
}

function getQwenFixedSizeFromAspectRatio(ar: string | null, quality: CliArgs["quality"]): string {
  if (quality === "normal") {
    console.warn(
      "DashScope qwen-image-max/plus/image models use fixed output sizes; --quality normal does not change the generated resolution."
    );
  }

  if (!ar) return QWEN_FIXED_SPEC.defaultSize;

  const ratioKey = findKnownRatioKey(ar, Object.keys(QWEN_FIXED_SIZES_BY_RATIO));
  if (!ratioKey) {
    throw new Error(
      `DashScope model supports only fixed ratios ${Object.keys(QWEN_FIXED_SIZES_BY_RATIO).join(", ")}. ` +
      `For custom ratios like "${ar}", use --model qwen-image-2.0-pro.`
    );
  }

  return QWEN_FIXED_SIZES_BY_RATIO[ratioKey]!;
}

function validateSizeFormat(size: string): { width: number; height: number } {
  const parsed = parseSize(size);
  if (!parsed) {
    throw new Error(`Invalid DashScope size "${size}". Expected <width>x<height> or <width>*<height>.`);
  }
  return parsed;
}

function validateQwen2Size(size: string): string {
  const normalized = normalizeSize(size);
  const parsed = validateSizeFormat(normalized);
  const totalPixels = parsed.width * parsed.height;
  if (totalPixels < MIN_QWEN_2_TOTAL_PIXELS || totalPixels > MAX_QWEN_2_TOTAL_PIXELS) {
    throw new Error(
      `DashScope qwen-image-2.0* models require total pixels between ${MIN_QWEN_2_TOTAL_PIXELS} ` +
      `and ${MAX_QWEN_2_TOTAL_PIXELS}. Received ${normalized} (${totalPixels} pixels).`
    );
  }
  return normalized;
}

function validateQwenFixedSize(size: string): string {
  const normalized = normalizeSize(size);
  validateSizeFormat(normalized);
  if (!QWEN_FIXED_SIZES.includes(normalized)) {
    throw new Error(
      `DashScope qwen-image-max/plus/image models support only these sizes: ${QWEN_FIXED_SIZES.join(", ")}. ` +
      `Received ${normalized}.`
    );
  }
  return normalized;
}

export function resolveSizeForModel(
  model: string,
  args: Pick<CliArgs, "size" | "aspectRatio" | "quality"> & { referenceImages?: string[] },
): string {
  const spec = getModelSpec(model);
  const referenceCount = args.referenceImages?.length ?? 0;

  if (spec.family === "wan27") {
    const maxPixels = getWan27MaxPixels(model, referenceCount > 0);
    if (args.size) return validateWan27Size(args.size, maxPixels, model);
    return getWan27SizeFromAspectRatio(args.aspectRatio, args.quality, maxPixels);
  }

  if (args.size) {
    if (spec.family === "qwen2") return validateQwen2Size(args.size);
    if (spec.family === "qwenFixed") return validateQwenFixedSize(args.size);
    validateSizeFormat(args.size);
    return normalizeSize(args.size);
  }

  if (spec.family === "qwen2") {
    return getQwen2SizeFromAspectRatio(args.aspectRatio, args.quality);
  }

  if (spec.family === "qwenFixed") {
    return getQwenFixedSizeFromAspectRatio(args.aspectRatio, args.quality);
  }

  return getSizeFromAspectRatio(args.aspectRatio, args.quality);
}

function buildParameters(
  family: DashScopeModelFamily,
  size: string,
): Record<string, unknown> {
  if (family === "wan27") {
    return {
      size,
      n: 1,
      watermark: false,
    };
  }

  const parameters: Record<string, unknown> = {
    prompt_extend: false,
    size,
  };

  if (family === "qwen2" || family === "qwenFixed") {
    parameters.watermark = false;
    parameters.negative_prompt = QWEN_NEGATIVE_PROMPT;
  }

  return parameters;
}

type DashScopeResponse = {
  output?: {
    result_image?: string;
    choices?: Array<{
      message?: {
        content?: Array<{ image?: string }>;
      };
    }>;
  };
};

async function extractImageFromResponse(result: DashScopeResponse): Promise<Uint8Array> {
  let imageData: string | null = null;

  if (result.output?.result_image) {
    imageData = result.output.result_image;
  } else if (result.output?.choices?.[0]?.message?.content) {
    const content = result.output.choices[0].message.content;
    for (const item of content) {
      if (item.image) {
        imageData = item.image;
        break;
      }
    }
  }

  if (!imageData) {
    console.error("Response:", JSON.stringify(result, null, 2));
    throw new Error("No image in response");
  }

  if (imageData.startsWith("http://") || imageData.startsWith("https://")) {
    const imgRes = await fetch(imageData);
    if (!imgRes.ok) throw new Error("Failed to download image");
    const buf = await imgRes.arrayBuffer();
    return new Uint8Array(buf);
  }

  return Uint8Array.from(Buffer.from(imageData, "base64"));
}

export async function generateImage(
  prompt: string,
  model: string,
  args: CliArgs
): Promise<Uint8Array> {
  const apiKey = getApiKey();
  if (!apiKey) throw new Error("DASHSCOPE_API_KEY is required");

  const spec = getModelSpec(model);

  if (args.referenceImages.length > 0 && spec.family !== "wan27") {
    throw new Error(
      "Reference images are not supported with this DashScope model. Use a wan2.7 image model (--model wan2.7-image-pro or wan2.7-image), or switch to --provider google with a Gemini multimodal model."
    );
  }

  if (args.referenceImages.length > WAN27_MAX_REFERENCE_IMAGES) {
    throw new Error(
      `DashScope wan2.7 image models accept at most ${WAN27_MAX_REFERENCE_IMAGES} reference images. Received ${args.referenceImages.length}.`
    );
  }

  if (spec.family === "wan27" && args.n !== 1) {
    throw new Error(
      "DashScope wan2.7 image models in baoyu-image-gen support exactly one output image per request (extra images would be billed but discarded). Remove --n or use --n 1."
    );
  }

  const size = resolveSizeForModel(model, args);
  const url = `${getBaseUrl()}/api/v1/services/aigc/multimodal-generation/generation`;

  const content: Array<Record<string, unknown>> = [];
  if (spec.family === "wan27" && args.referenceImages.length > 0) {
    for (const refPath of args.referenceImages) {
      content.push({ image: await loadReferenceImage(refPath) });
    }
  }
  content.push({ text: prompt });

  const body = {
    model,
    input: {
      messages: [
        {
          role: "user",
          content,
        },
      ],
    },
    parameters: buildParameters(spec.family, size),
  };

  console.log(`Generating image with DashScope (${model})...`, { family: spec.family, size });

  const res = await fetch(url, {
    method: "POST",
    headers: {
      "Content-Type": "application/json",
      Authorization: `Bearer ${apiKey}`,
    },
    body: JSON.stringify(body),
  });

  if (!res.ok) {
    const err = await res.text();
    throw new Error(`DashScope API error (${res.status}): ${err}`);
  }

  const result = await res.json() as DashScopeResponse;
  return extractImageFromResponse(result);
}
