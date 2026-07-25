import path from "node:path";
import { readFile } from "node:fs/promises";
import { execFileSync } from "node:child_process";
import type { CliArgs } from "../types";

const GOOGLE_MULTIMODAL_MODELS = [
  "gemini-3-pro-image",
  "gemini-3.1-flash-image",
  "gemini-3-pro-image-preview",
  "gemini-3-flash-preview",
  "gemini-3.1-flash-image-preview",
];
const GOOGLE_IMAGEN_MODELS = [
  "imagen-3.0-generate-002",
  "imagen-3.0-generate-001",
];

export function getDefaultModel(): string {
  return process.env.GOOGLE_IMAGE_MODEL || "gemini-3-pro-image";
}

export function normalizeGoogleModelId(model: string): string {
  return model.startsWith("models/") ? model.slice("models/".length) : model;
}

export function isGoogleMultimodal(model: string): boolean {
  const normalized = normalizeGoogleModelId(model);
  return GOOGLE_MULTIMODAL_MODELS.some((m) => normalized.includes(m));
}

export function isGoogleImagen(model: string): boolean {
  const normalized = normalizeGoogleModelId(model);
  return GOOGLE_IMAGEN_MODELS.some((m) => normalized.includes(m));
}

function getGoogleApiKey(): string | null {
  return process.env.GOOGLE_API_KEY || process.env.GEMINI_API_KEY || null;
}

export function getGoogleImageSize(args: CliArgs): "1K" | "2K" | "4K" {
  if (args.imageSize) return args.imageSize as "1K" | "2K" | "4K";
  return args.quality === "2k" ? "2K" : "1K";
}

function getGoogleBaseUrl(): string {
  const base =
    process.env.GOOGLE_BASE_URL || "https://generativelanguage.googleapis.com";
  return base.replace(/\/+$/g, "");
}

export function buildGoogleUrl(pathname: string): string {
  const base = getGoogleBaseUrl();
  const cleanedPath = pathname.replace(/^\/+/g, "");
  if (base.endsWith("/v1beta")) return `${base}/${cleanedPath}`;
  return `${base}/v1beta/${cleanedPath}`;
}

function toModelPath(model: string): string {
  const modelId = normalizeGoogleModelId(model);
  return `models/${modelId}`;
}

function getHttpProxy(): string | null {
  return (
    process.env.https_proxy ||
    process.env.HTTPS_PROXY ||
    process.env.http_proxy ||
    process.env.HTTP_PROXY ||
    process.env.ALL_PROXY ||
    null
  );
}

async function postGoogleJsonViaCurl<T>(
  url: string,
  apiKey: string,
  body: unknown,
): Promise<T> {
  const proxy = getHttpProxy();
  const bodyStr = JSON.stringify(body);
  const args = [
    "-s",
    "--connect-timeout",
    "30",
    "--max-time",
    "300",
    ...(proxy ? ["-x", proxy] : []),
    url,
    "-H",
    "Content-Type: application/json",
    "-H",
    `x-goog-api-key: ${apiKey}`,
    "-d",
    "@-",
  ];

  let result = "";
  try {
    result = execFileSync("curl", args, {
      input: bodyStr,
      encoding: "utf8",
      maxBuffer: 100 * 1024 * 1024,
      timeout: 310000,
    });
  } catch (error) {
    const e = error as { message?: string; stderr?: string | Buffer };
    const stderrText =
      typeof e.stderr === "string"
        ? e.stderr
        : e.stderr
          ? e.stderr.toString("utf8")
          : "";
    const details = stderrText.trim() || e.message || "curl request failed";
    throw new Error(`Google API request failed via curl: ${details}`);
  }

  const parsed = JSON.parse(result) as any;
  if (parsed.error) {
    throw new Error(
      `Google API error (${parsed.error.code}): ${parsed.error.message}`,
    );
  }
  return parsed as T;
}

async function postGoogleJsonViaFetch<T>(
  url: string,
  apiKey: string,
  body: unknown,
): Promise<T> {
  const res = await fetch(url, {
    method: "POST",
    headers: {
      "Content-Type": "application/json",
      "x-goog-api-key": apiKey,
    },
    body: JSON.stringify(body),
  });

  if (!res.ok) {
    const err = await res.text();
    throw new Error(`Google API error (${res.status}): ${err}`);
  }

  return (await res.json()) as T;
}

async function postGoogleJson<T>(pathname: string, body: unknown): Promise<T> {
  const apiKey = getGoogleApiKey();
  if (!apiKey) throw new Error("GOOGLE_API_KEY or GEMINI_API_KEY is required");

  const url = buildGoogleUrl(pathname);
  const proxy = getHttpProxy();

  // When an HTTP proxy is detected, use curl instead of fetch.
  // Bun's fetch has a known issue where long-lived connections through
  // HTTP proxies get their sockets closed unexpectedly, causing image
  // generation requests to fail with "socket connection was closed
  // unexpectedly". Using curl as the HTTP client works around this.
  if (proxy) {
    return postGoogleJsonViaCurl<T>(url, apiKey, body);
  }

  return postGoogleJsonViaFetch<T>(url, apiKey, body);
}

export function buildPromptWithAspect(
  prompt: string,
  ar: string | null,
  quality: CliArgs["quality"],
): string {
  let result = prompt;
  if (ar) {
    result += ` Aspect ratio: ${ar}.`;
  }
  if (quality === "2k") {
    result += " High resolution 2048px.";
  }
  return result;
}

export function addAspectRatioToPrompt(prompt: string, ar: string | null): string {
  if (!ar) return prompt;
  return `${prompt} Aspect ratio: ${ar}.`;
}

async function readImageAsBase64(
  p: string,
): Promise<{ data: string; mimeType: string }> {
  const buf = await readFile(p);
  const ext = path.extname(p).toLowerCase();
  let mimeType = "image/png";
  if (ext === ".jpg" || ext === ".jpeg") mimeType = "image/jpeg";
  else if (ext === ".gif") mimeType = "image/gif";
  else if (ext === ".webp") mimeType = "image/webp";
  return { data: buf.toString("base64"), mimeType };
}

export function extractInlineImageData(response: {
  candidates?: Array<{
    content?: { parts?: Array<{ inlineData?: { data?: string } }> };
  }>;
}): string | null {
  for (const candidate of response.candidates || []) {
    for (const part of candidate.content?.parts || []) {
      const data = part.inlineData?.data;
      if (typeof data === "string" && data.length > 0) return data;
    }
  }
  return null;
}

export function extractPredictedImageData(response: {
  predictions?: Array<any>;
  generatedImages?: Array<any>;
}): string | null {
  const candidates = [
    ...(response.predictions || []),
    ...(response.generatedImages || []),
  ];
  for (const candidate of candidates) {
    if (!candidate || typeof candidate !== "object") continue;
    if (typeof candidate.imageBytes === "string") return candidate.imageBytes;
    if (typeof candidate.bytesBase64Encoded === "string")
      return candidate.bytesBase64Encoded;
    if (typeof candidate.data === "string") return candidate.data;
    const image = candidate.image;
    if (image && typeof image === "object") {
      if (typeof image.imageBytes === "string") return image.imageBytes;
      if (typeof image.bytesBase64Encoded === "string")
        return image.bytesBase64Encoded;
      if (typeof image.data === "string") return image.data;
    }
  }
  return null;
}

async function generateWithGemini(
  prompt: string,
  model: string,
  args: CliArgs,
): Promise<Uint8Array> {
  const promptWithAspect = addAspectRatioToPrompt(prompt, args.aspectRatio);
  const parts: Array<{
    text?: string;
    inlineData?: { data: string; mimeType: string };
  }> = [];
  for (const refPath of args.referenceImages) {
    const { data, mimeType } = await readImageAsBase64(refPath);
    parts.push({ inlineData: { data, mimeType } });
  }
  parts.push({ text: promptWithAspect });

  const imageConfig: { imageSize: "1K" | "2K" | "4K" } = {
    imageSize: getGoogleImageSize(args),
  };

  console.log("Generating image with Gemini...", imageConfig);
  const response = await postGoogleJson<{
    candidates?: Array<{
      content?: { parts?: Array<{ inlineData?: { data?: string } }> };
    }>;
  }>(`${toModelPath(model)}:generateContent`, {
    contents: [
      {
        role: "user",
        parts,
      },
    ],
    generationConfig: {
      responseModalities: ["IMAGE"],
      imageConfig,
    },
  });
  console.log("Generation completed.");

  const imageData = extractInlineImageData(response);
  if (imageData) return Uint8Array.from(Buffer.from(imageData, "base64"));

  throw new Error("No image in response");
}

async function generateWithImagen(
  prompt: string,
  model: string,
  args: CliArgs,
): Promise<Uint8Array> {
  const fullPrompt = buildPromptWithAspect(
    prompt,
    args.aspectRatio,
    args.quality,
  );
  const imageSize = getGoogleImageSize(args);
  if (imageSize === "4K") {
    console.error(
      "Warning: Imagen models do not support 4K imageSize, using 2K instead.",
    );
  }

  const parameters: Record<string, unknown> = {
    sampleCount: args.n,
  };
  if (args.aspectRatio) {
    parameters.aspectRatio = args.aspectRatio;
  }
  if (imageSize === "1K" || imageSize === "2K") {
    parameters.imageSize = imageSize;
  } else {
    parameters.imageSize = "2K";
  }

  const response = await postGoogleJson<{
    predictions?: Array<any>;
    generatedImages?: Array<any>;
  }>(`${toModelPath(model)}:predict`, {
    instances: [
      {
        prompt: fullPrompt,
      },
    ],
    parameters,
  });

  const imageData = extractPredictedImageData(response);
  if (imageData) return Uint8Array.from(Buffer.from(imageData, "base64"));

  throw new Error("No image in response");
}

export async function generateImage(
  prompt: string,
  model: string,
  args: CliArgs,
): Promise<Uint8Array> {
  if (isGoogleImagen(model)) {
    if (args.referenceImages.length > 0) {
      throw new Error(
        "Reference images are not supported with Imagen models. Use a Gemini multimodal model such as gemini-3-pro-image, gemini-3.1-flash-image, gemini-3-pro-image-preview, gemini-3-flash-preview, or gemini-3.1-flash-image-preview.",
      );
    }
    return generateWithImagen(prompt, model, args);
  }

  if (!isGoogleMultimodal(model) && args.referenceImages.length > 0) {
    throw new Error(
      "Reference images are only supported with Gemini multimodal models such as gemini-3-pro-image, gemini-3.1-flash-image, gemini-3-pro-image-preview, gemini-3-flash-preview, or gemini-3.1-flash-image-preview.",
    );
  }

  return generateWithGemini(prompt, model, args);
}
