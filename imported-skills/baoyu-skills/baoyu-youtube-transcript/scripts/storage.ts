import { existsSync, mkdirSync, readFileSync, writeFileSync } from "fs";
import { dirname, join, resolve } from "path";

import type { Sentence, Snippet, VideoMeta } from "./types.ts";

export function ensureDir(path: string) {
  const dir = dirname(path);
  if (!existsSync(dir)) mkdirSync(dir, { recursive: true });
}

export function resolveBaseDir(outputDir: string): string {
  return resolve(outputDir || "youtube-transcript");
}

function loadIndex(baseDir: string): Record<string, string> {
  try {
    return JSON.parse(readFileSync(join(baseDir, ".index.json"), "utf-8"));
  } catch {
    return {};
  }
}

function saveIndex(baseDir: string, index: Record<string, string>) {
  const path = join(baseDir, ".index.json");
  ensureDir(path);
  writeFileSync(path, JSON.stringify(index, null, 2));
}

export function lookupVideoDir(videoId: string, baseDir: string): string | null {
  const rel = loadIndex(baseDir)[videoId];
  if (rel) {
    const dir = resolve(baseDir, rel);
    if (existsSync(dir)) return dir;
  }
  return null;
}

export function registerVideoDir(videoId: string, channelSlug: string, titleSlug: string, baseDir: string): string {
  const rel = join(channelSlug, titleSlug);
  const index = loadIndex(baseDir);
  index[videoId] = rel;
  saveIndex(baseDir, index);
  return resolve(baseDir, rel);
}

export function hasCachedData(videoDir: string): boolean {
  return existsSync(join(videoDir, "meta.json")) && existsSync(join(videoDir, "transcript-raw.json"));
}

export function loadMeta(videoDir: string): VideoMeta {
  return JSON.parse(readFileSync(join(videoDir, "meta.json"), "utf-8"));
}

export function loadSnippets(videoDir: string): Snippet[] {
  return JSON.parse(readFileSync(join(videoDir, "transcript-raw.json"), "utf-8"));
}

export function loadSentences(videoDir: string): Sentence[] {
  return JSON.parse(readFileSync(join(videoDir, "transcript-sentences.json"), "utf-8"));
}
