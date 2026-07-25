import type { CliArgs } from "../types";
import * as crypto from "node:crypto";

type JimengSizePreset = "normal" | "2k" | "4k";

export function getDefaultModel(): string {
  return process.env.JIMENG_IMAGE_MODEL || "jimeng_t2i_v40";
}

function getAccessKey(): string | null {
  return process.env.JIMENG_ACCESS_KEY_ID || null;
}

function getSecretKey(): string | null {
  return process.env.JIMENG_SECRET_ACCESS_KEY || null;
}

function getRegion(): string {
  return process.env.JIMENG_REGION || "cn-north-1";
}

function getBaseUrl(): string {
  return process.env.JIMENG_BASE_URL || "https://visual.volcengineapi.com";
}

function resolveEndpoint(query: Record<string, string>): {
  url: string;
  host: string;
  canonicalUri: string;
} {
  let baseUrl: URL;
  try {
    baseUrl = new URL(getBaseUrl());
  } catch {
    throw new Error(`Invalid JIMENG_BASE_URL: ${getBaseUrl()}`);
  }

  baseUrl.search = "";
  for (const [key, value] of Object.entries(query).sort(([a], [b]) => a.localeCompare(b))) {
    baseUrl.searchParams.set(key, value);
  }

  return {
    url: baseUrl.toString(),
    host: baseUrl.host,
    canonicalUri: baseUrl.pathname || "/",
  };
}

/**
 * Volcengine HMAC-SHA256 signature generation
 * Following the official documentation at:
 * https://www.volcengine.com/docs/85621/1817045
 */
function generateSignature(
  method: string,
  query: Record<string, string>,
  headers: Record<string, string>,
  body: string,
  accessKey: string,
  secretKey: string,
  region: string,
  service: string,
  canonicalUri: string
): string {
  // 1. Create canonical request
  // Sort query parameters alphabetically
  const sortedQuery = Object.entries(query)
    .sort(([a], [b]) => a.localeCompare(b))
    .map(([k, v]) => `${encodeURIComponent(k)}=${encodeURIComponent(v)}`)
    .join("&");

  // Sort headers alphabetically and create canonical headers
  const sortedHeaders = Object.entries(headers)
    .sort(([a], [b]) => a.localeCompare(b))
    .map(([k, v]) => `${k.toLowerCase()}:${v.trim()}\n`)
    .join("");

  const signedHeaders = Object.keys(headers)
    .sort()
    .map(k => k.toLowerCase())
    .join(";");

  const hashedPayload = crypto.createHash("sha256").update(body, "utf8").digest("hex");

  const canonicalRequest = [
    method,
    canonicalUri,
    sortedQuery,
    sortedHeaders,
    signedHeaders,
    hashedPayload,
  ].join("\n");

  const hashedCanonicalRequest = crypto
    .createHash("sha256")
    .update(canonicalRequest, "utf8")
    .digest("hex");

  // 2. Create string to sign
  const algorithm = "HMAC-SHA256";
  const timestamp = headers["X-Date"] || headers["x-date"];
  if (!timestamp) {
    throw new Error("Jimeng signature generation requires an X-Date header.");
  }
  const dateStamp = timestamp.slice(0, 8);

  const credentialScope = `${dateStamp}/${region}/${service}/request`;

  const stringToSign = [
    algorithm,
    timestamp,
    credentialScope,
    hashedCanonicalRequest,
  ].join("\n");

  // 3. Calculate signature
  const kDate = crypto
    .createHmac("sha256", secretKey)
    .update(dateStamp)
    .digest();

  const kRegion = crypto.createHmac("sha256", kDate).update(region).digest();
  const kService = crypto.createHmac("sha256", kRegion).update(service).digest();
  const kSigning = crypto.createHmac("sha256", kService).update("request").digest();

  const signature = crypto
    .createHmac("sha256", kSigning)
    .update(stringToSign)
    .digest("hex");

  // 4. Create authorization header
  return `${algorithm} Credential=${accessKey}/${credentialScope}, SignedHeaders=${signedHeaders}, Signature=${signature}`;
}

/**
 * Parse aspect ratio string like "16:9", "1:1", "4:3" into width and height
 */
function parseAspectRatio(ar: string): { width: number; height: number } | null {
  const match = ar.match(/^(\d+(?:\.\d+)?):(\d+(?:\.\d+)?)$/);
  if (!match) return null;
  const w = parseFloat(match[1]!);
  const h = parseFloat(match[2]!);
  if (w <= 0 || h <= 0) return null;
  return { width: w, height: h };
}

/**
 * Supported size presets for different quality levels
 * Based on Volcengine Jimeng documentation
 */
const SIZE_PRESETS: Record<string, Record<string, string>> = {
  normal: {
    "1:1": "1024x1024",
    "4:3": "1360x1020",
    "16:9": "1536x864",
    "3:2": "1440x960",
    "21:9": "1920x824",
  },
  "2k": {
    "1:1": "2048x2048",
    "4:3": "2304x1728",
    "16:9": "2560x1440",
    "3:2": "2496x1664",
    "21:9": "3024x1296",
  },
  "4k": {
    "1:1": "4096x4096",
    "4:3": "4694x3520",
    "16:9": "5404x3040",
    "3:2": "4992x3328",
    "21:9": "6198x2656",
  },
};

function normalizeDimensions(value: string): string | null {
  const match = value.trim().match(/^(\d+)\s*[xX*]\s*(\d+)$/);
  if (!match) return null;
  return `${match[1]}x${match[2]}`;
}

function getClosestPresetSize(ar: string | null, qualityLevel: JimengSizePreset): string {
  const presets = SIZE_PRESETS[qualityLevel];
  const defaultSize = presets["1:1"]!;

  if (!ar) return defaultSize;

  const parsed = parseAspectRatio(ar);
  if (!parsed) return defaultSize;

  const targetRatio = parsed.width / parsed.height;
  let bestMatch = defaultSize;
  let bestDiff = Infinity;

  for (const [ratio, size] of Object.entries(presets)) {
    const [w, h] = ratio.split(":").map(Number);
    const presetRatio = w / h;
    const diff = Math.abs(presetRatio - targetRatio);
    if (diff < bestDiff) {
      bestDiff = diff;
      bestMatch = size;
    }
  }

  return bestMatch;
}

function normalizeImageSizePreset(imageSize: string, ar: string | null): string | null {
  const preset = imageSize.trim().toUpperCase();
  if (preset === "1K") return getClosestPresetSize(ar, "normal");
  if (preset === "2K") return getClosestPresetSize(ar, "2k");
  if (preset === "4K") return getClosestPresetSize(ar, "4k");
  return normalizeDimensions(imageSize);
}

function getImageSize(ar: string | null, quality: CliArgs["quality"], imageSize?: string | null): string {
  if (imageSize) {
    const normalizedSize = normalizeImageSizePreset(imageSize, ar);
    if (normalizedSize) return normalizedSize;
  }

  // Default to 2K quality if not specified
  const qualityLevel: JimengSizePreset = quality === "normal" ? "normal" : "2k";
  return getClosestPresetSize(ar, qualityLevel);
}

/**
 * Step 1: Submit async task to Volcengine Jimeng API
 */
async function submitTask(
  prompt: string,
  model: string,
  size: string,
  accessKey: string,
  secretKey: string,
  region: string
): Promise<string> {
  // Query parameters for submit endpoint
  const query = {
    Action: "CVSync2AsyncSubmitTask",
    Version: "2022-08-31",
  };
  const endpoint = resolveEndpoint(query);

  // Request body - Jimeng API expects width/height as separate integers
  const [width, height] = size.split("x").map(Number);
  const bodyObj = {
    req_key: model,
    prompt,
    // Use separate width and height parameters instead of size string
    width: width,
    height: height,
    // Optional: seed for reproducibility
    // seed: Math.floor(Math.random() * 999999),
  };

  const body = JSON.stringify(bodyObj);

  // Headers
  const timestampHeader = new Date().toISOString().replace(/[:\-]|\.\d{3}/g, "");
  const headers = {
    "Content-Type": "application/json",
    "X-Date": timestampHeader,
    "Host": endpoint.host,
  };

  // Generate signature
  const authorization = generateSignature(
    "POST",
    query,
    headers,
    body,
    accessKey,
    secretKey,
    region,
    "cv",
    endpoint.canonicalUri
  );

  console.error(`Submitting task to Jimeng (${model})...`, { width, height });

  const res = await fetch(endpoint.url, {
    method: "POST",
    headers: {
      ...headers,
      "Authorization": authorization,
    },
    body,
  });

  if (!res.ok) {
    const err = await res.text();
    throw new Error(`Jimeng API submit error (${res.status}): ${err}`);
  }

  const result = (await res.json()) as {
    code?: number;
    message?: string;
    data?: {
      task_id?: string;
    };
  };

  // Volcengine API returns code 10000 for success
  if (result.code !== 10000 || !result.data?.task_id) {
    console.error("Submit response:", JSON.stringify(result, null, 2));
    throw new Error(`Failed to submit task: ${result.message || "Unknown error"}`);
  }

  return result.data.task_id;
}

/**
 * Step 2: Poll for task result
 * Returns image data directly as Uint8Array
 */
async function pollForResult(
  taskId: string,
  model: string,
  accessKey: string,
  secretKey: string,
  region: string
): Promise<Uint8Array> {
  const maxAttempts = 60;
  const pollIntervalMs = 2000;

  for (let attempt = 0; attempt < maxAttempts; attempt++) {
    // Query parameters for result endpoint
    const query = {
      Action: "CVSync2AsyncGetResult",
      Version: "2022-08-31",
    };
    const endpoint = resolveEndpoint(query);

    // Request body - include req_key and task_id
    const bodyObj = {
      req_key: model,
      task_id: taskId,
    };

    const body = JSON.stringify(bodyObj);

    // Headers
    const timestampHeader = new Date().toISOString().replace(/[:\-]|\.\d{3}/g, "");
    const headers = {
      "Content-Type": "application/json",
      "X-Date": timestampHeader,
      "Host": endpoint.host,
    };

    // Generate signature
    const authorization = generateSignature(
      "POST",
      query,
      headers,
      body,
      accessKey,
      secretKey,
      region,
      "cv",
      endpoint.canonicalUri
    );

    const res = await fetch(endpoint.url, {
      method: "POST",
      headers: {
        ...headers,
        "Authorization": authorization,
      },
      body,
    });

    if (!res.ok) {
      const err = await res.text();
      throw new Error(`Jimeng API poll error (${res.status}): ${err}`);
    }

    const result = (await res.json()) as {
      code?: number;
      message?: string;
      data?: {
        status?: string;
        image_urls?: string[];
        binary_data_base64?: string[];
      };
    };

    // Volcengine API returns code 10000 for success
    if (result.code === 10000 && result.data) {
      const { status, image_urls, binary_data_base64 } = result.data;

      // Check for base64 image data (preferred by Jimeng)
      if (binary_data_base64 && binary_data_base64.length > 0) {
        console.error("Image received as base64 data");
        const base64Data = binary_data_base64[0]!;
        // Convert base64 to Uint8Array
        const binaryString = Buffer.from(base64Data, "base64").toString("binary");
        const bytes = new Uint8Array(binaryString.length);
        for (let i = 0; i < binaryString.length; i++) {
          bytes[i] = binaryString.charCodeAt(i);
        }
        return bytes;
      }

      // Fallback to URL format
      if (status === "done" && image_urls && image_urls.length > 0) {
        // Download from URL
        console.error(`Downloading image from ${image_urls[0]}...`);
        const imgRes = await fetch(image_urls[0]!);
        if (!imgRes.ok) {
          throw new Error(`Failed to download image from ${image_urls[0]}`);
        }
        const buffer = await imgRes.arrayBuffer();
        return new Uint8Array(buffer);
      }

      if (status === "in_queue" || status === "generating") {
        console.error(`Task status: ${status} (${attempt + 1}/${maxAttempts})`);
        await new Promise(resolve => setTimeout(resolve, pollIntervalMs));
        continue;
      }

      if (status === "fail") {
        throw new Error(`Jimeng task failed: ${result.message || "Generation failed"}`);
      }
    }

    console.error("Poll response:", JSON.stringify(result, null, 2));
    throw new Error(`Unexpected response during polling: ${result.message || "Unknown error"}`);
  }

  throw new Error("Task timeout: image generation took too long");
}

export async function generateImage(
  prompt: string,
  model: string,
  args: CliArgs
): Promise<Uint8Array> {
  if (args.referenceImages.length > 0) {
    throw new Error(
      "Jimeng does not support reference images. Use --provider google, openai, openrouter, or replicate."
    );
  }

  const accessKey = getAccessKey();
  const secretKey = getSecretKey();
  const region = getRegion();

  if (!accessKey || !secretKey) {
    throw new Error(
      "JIMENG_ACCESS_KEY_ID and JIMENG_SECRET_ACCESS_KEY are required. " +
      "Get your credentials from https://console.volcengine.com/iam/keymanage"
    );
  }

  const size = getImageSize(args.aspectRatio, args.quality, args.imageSize);

  // Step 1: Submit task
  const taskId = await submitTask(prompt, model, size, accessKey, secretKey, region);

  // Step 2: Poll for result (returns image data directly)
  const imageData = await pollForResult(taskId, model, accessKey, secretKey, region);

  console.error("Image generation complete!");
  return imageData;
}
