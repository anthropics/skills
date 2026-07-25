export function normalizeUrl(input: string): URL {
  try {
    return new URL(input);
  } catch {
    throw new Error(`Invalid URL: ${input}`);
  }
}

export function sanitizeFilename(input: string): string {
  return input.replace(/[^a-zA-Z0-9._-]+/g, "-").replace(/^-+|-+$/g, "") || "document";
}

