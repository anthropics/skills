import path from "node:path";
import { readFile } from "node:fs/promises";
import type { CliArgs } from "../types";
import { getOpenAISize, extractImageFromResponse } from "./openai.ts";

type OpenAIImageResponse = { data: Array<{ url?: string; b64_json?: string }> };
type AzureEndpoint = {
  resourceBaseURL: string;
  deployment: string | null;
};

const DEFAULT_AZURE_API_VERSION = "2025-04-01-preview";
const AZURE_EDIT_IMAGE_EXTENSIONS = new Set([".png", ".jpg", ".jpeg"]);

export function parseAzureBaseURL(url: string): AzureEndpoint {
  const parsed = new URL(url);
  const trimmedPath = parsed.pathname.replace(/\/+$/, "");
  const deploymentMatch = trimmedPath.match(/^(.*?)(?:\/openai)?\/deployments\/([^/]+)$/);

  if (deploymentMatch) {
    parsed.pathname = `${deploymentMatch[1] || ""}/openai`;
    return {
      resourceBaseURL: parsed.toString().replace(/\/+$/, ""),
      deployment: decodeURIComponent(deploymentMatch[2]!),
    };
  }

  parsed.pathname = trimmedPath.endsWith("/openai") ? trimmedPath : `${trimmedPath}/openai`;
  return {
    resourceBaseURL: parsed.toString().replace(/\/+$/, ""),
    deployment: null,
  };
}

export function getDefaultModel(): string {
  const explicitDeployment = process.env.AZURE_OPENAI_DEPLOYMENT?.trim();
  if (explicitDeployment) return explicitDeployment;

  const baseURL = process.env.AZURE_OPENAI_BASE_URL;
  if (baseURL) {
    try {
      const { deployment } = parseAzureBaseURL(baseURL);
      if (deployment) return deployment;
    } catch {
      // Ignore invalid URLs here so the required-env check can raise the user-facing error later.
    }
  }

  return process.env.AZURE_OPENAI_IMAGE_MODEL || "gpt-image-2";
}

function getEndpoint(): AzureEndpoint {
  const url = process.env.AZURE_OPENAI_BASE_URL;
  if (!url) {
    throw new Error(
      "AZURE_OPENAI_BASE_URL is required. Set it to your Azure resource or deployment endpoint, e.g.: https://your-resource.openai.azure.com or https://your-resource.openai.azure.com/openai/deployments/your-deployment"
    );
  }
  return parseAzureBaseURL(url);
}

function getApiKey(): string {
  const key = process.env.AZURE_OPENAI_API_KEY;
  if (!key) {
    throw new Error(
      "AZURE_OPENAI_API_KEY is required. Get it from Azure Portal → your OpenAI resource → Keys and Endpoint."
    );
  }
  return key;
}

function getApiVersion(): string {
  return process.env.AZURE_API_VERSION || DEFAULT_AZURE_API_VERSION;
}

function getDeployment(model: string): string {
  const deployment = model.trim();
  if (!deployment) {
    throw new Error(
      "Azure deployment name is required. Use --model <deployment>, AZURE_OPENAI_DEPLOYMENT, AZURE_OPENAI_IMAGE_MODEL, or embed the deployment in AZURE_OPENAI_BASE_URL."
    );
  }
  return deployment;
}

function buildURL(deployment: string, pathSuffix: string): string {
  const { resourceBaseURL } = getEndpoint();
  return `${resourceBaseURL}/deployments/${encodeURIComponent(deployment)}${pathSuffix}?api-version=${getApiVersion()}`;
}

function authHeaders(): Record<string, string> {
  return { "api-key": getApiKey() };
}

function getAzureQuality(quality: CliArgs["quality"]): "medium" | "high" {
  return quality === "2k" ? "high" : "medium";
}

export function validateArgs(_model: string, args: CliArgs): void {
  for (const refPath of args.referenceImages) {
    const ext = path.extname(refPath).toLowerCase();
    if (!AZURE_EDIT_IMAGE_EXTENSIONS.has(ext)) {
      throw new Error(
        `Azure OpenAI reference images must be PNG or JPG/JPEG. Unsupported file: ${refPath}`
      );
    }
  }
}

export async function generateImage(
  prompt: string,
  model: string,
  args: CliArgs
): Promise<Uint8Array> {
  const deployment = getDeployment(model);
  const size = args.size || getOpenAISize(model, args.aspectRatio, args.quality);

  if (args.referenceImages.length > 0) {
    return generateWithAzureEdits(prompt, deployment, size, args.referenceImages, args.quality);
  }

  return generateWithAzureGenerations(prompt, deployment, size, args.quality);
}

async function generateWithAzureGenerations(
  prompt: string,
  deployment: string,
  size: string,
  quality: CliArgs["quality"]
): Promise<Uint8Array> {
  const body: Record<string, any> = {
    prompt,
    size,
    n: 1,
    quality: getAzureQuality(quality),
  };

  const res = await fetch(buildURL(deployment, "/images/generations"), {
    method: "POST",
    headers: {
      "Content-Type": "application/json",
      ...authHeaders(),
    },
    body: JSON.stringify(body),
  });

  if (!res.ok) {
    const err = await res.text();
    throw new Error(`Azure OpenAI API error: ${err}`);
  }

  const result = (await res.json()) as OpenAIImageResponse;
  return extractImageFromResponse(result);
}

async function generateWithAzureEdits(
  prompt: string,
  deployment: string,
  size: string,
  referenceImages: string[],
  quality: CliArgs["quality"]
): Promise<Uint8Array> {
  const form = new FormData();
  form.append("prompt", prompt);
  form.append("size", size);
  form.append("n", "1");
  form.append("quality", getAzureQuality(quality));

  for (const refPath of referenceImages) {
    const bytes = await readFile(refPath);
    const filename = path.basename(refPath);
    const mimeType = path.extname(filename).toLowerCase() === ".png" ? "image/png" : "image/jpeg";
    const blob = new Blob([bytes], { type: mimeType });
    form.append("image[]", blob, filename);
  }

  const res = await fetch(buildURL(deployment, "/images/edits"), {
    method: "POST",
    headers: {
      ...authHeaders(),
    },
    body: form,
  });

  if (!res.ok) {
    const err = await res.text();
    throw new Error(`Azure OpenAI edits API error: ${err}`);
  }

  const result = (await res.json()) as OpenAIImageResponse;
  return extractImageFromResponse(result);
}
