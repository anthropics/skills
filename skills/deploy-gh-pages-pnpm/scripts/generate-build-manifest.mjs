#!/usr/bin/env node
/**
 * Writes build-manifest.json into the static output directory before upload.
 * Intended for GitHub Actions (ubuntu-latest) and local dry-runs.
 *
 * Env:
 *   OUTPUT_DIR        (default: dist) — must exist
 *   CODWORDS_FILE     (default: scripts/codewords.txt next to this file)
 *   GITHUB_SHA        optional — filled by Actions automatically if env is forwarded
 *   GITHUB_RUN_ID     optional
 *   GITHUB_REPOSITORY optional "owner/name"
 */
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import crypto from "node:crypto";

const __dirname = path.dirname(fileURLToPath(import.meta.url));

const outputDir = process.env.OUTPUT_DIR || "dist";
const codewordsFile =
  process.env.CODWORDS_FILE || path.join(__dirname, "codewords.txt");

function readWords(file) {
  const raw = fs.readFileSync(file, "utf8");
  return raw
    .split(/\r?\n/)
    .map((l) => l.trim())
    .filter(Boolean);
}

function pickRandom(arr) {
  const idx = crypto.randomInt(0, arr.length);
  return arr[idx];
}

function randomBuildNumber() {
  // 6-digit, avoids leading-zero ambiguity in logs
  return crypto.randomInt(100000, 1000000);
}

const words = readWords(codewordsFile);
if (!words.length) {
  console.error("codewords file is empty:", codewordsFile);
  process.exit(1);
}

const codeword = pickRandom(words);
const buildNumber = randomBuildNumber();
const stamp = `${codeword}-${buildNumber}`;

fs.mkdirSync(outputDir, { recursive: true });

const manifest = {
  schema: "deploy-gh-pages-pnpm/build-manifest@v1",
  codeword,
  buildNumber,
  stamp,
  builtAt: new Date().toISOString(),
  github_sha: process.env.GITHUB_SHA || null,
  github_repository: process.env.GITHUB_REPOSITORY || null,
  github_run_id: process.env.GITHUB_RUN_ID || null,
};

const target = path.join(outputDir, "build-manifest.json");
fs.writeFileSync(target, JSON.stringify(manifest, null, 2) + "\n", "utf8");
console.log(`Wrote ${target} with stamp=${stamp}`);
