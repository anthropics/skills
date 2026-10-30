#!/usr/bin/env bun
// Validate iOS and Android metadata locally before any push.
// Catches the gotchas Apple's precheck warns about + the Kids Category trap.
//
// Usage: bun validate-metadata.ts

import { readFileSync, existsSync } from "node:fs";

const errors: string[] = [];
const warnings: string[] = [];

const LIMITS_IOS: Record<string, number> = {
  "name.txt": 30,
  "subtitle.txt": 30,
  "promotional_text.txt": 170,
  "keywords.txt": 100,
  "description.txt": 4000,
  "release_notes.txt": 4000,
};

const LIMITS_ANDROID: Record<string, number> = {
  "title.txt": 30,
  "short-description.txt": 80,
  "full-description.txt": 4000,
};

// iOS
const iosDir = "ios/fastlane/metadata";
if (existsSync(iosDir)) {
  console.log("Checking iOS metadata...\n");
  const locales = readFileSync(`${iosDir}`).toString && [];  // listing via fs not needed; use a known list
  for (const locale of (await import("node:fs/promises")).readdir(iosDir).then(es => es.filter(e => e !== "review_information")) as any) {
    const localeDir = `${iosDir}/${locale}`;
    for (const [file, limit] of Object.entries(LIMITS_IOS)) {
      const p = `${localeDir}/${file}`;
      if (!existsSync(p)) {
        warnings.push(`[ios/${locale}] missing ${file}`);
        continue;
      }
      const content = readFileSync(p, "utf8");
      const len = content.length;
      if (len > limit) errors.push(`[ios/${locale}/${file}] ${len} > ${limit} chars`);
      // Kids Category trap
      if (file === "subtitle.txt" && /\b(kids|children)\b/i.test(content)) {
        errors.push(`[ios/${locale}/${file}] contains "kids/children" — Apple rejects under Guideline 2.3.8 unless in Kids Category`);
      }
      if (file === "keywords.txt" && /\b(kids|children)\b/i.test(content)) {
        warnings.push(`[ios/${locale}/${file}] contains "kids/children" — high risk under Guideline 2.3.8`);
      }
    }
  }
  // Top-level copyright check
  if (!existsSync(`${iosDir}/copyright.txt`)) {
    warnings.push("[ios] copyright.txt missing (non-localized, at metadata/copyright.txt root). Precheck will warn.");
  }
}

// Android
const androidGB = "android/app/src/main/play/listings/en-GB";
const androidUS = "android/app/src/main/play/listings/en-US";
const androidDir = existsSync(androidGB) ? androidGB : existsSync(androidUS) ? androidUS : null;
if (androidDir) {
  console.log("Checking Android metadata...\n");
  for (const [file, limit] of Object.entries(LIMITS_ANDROID)) {
    const p = `${androidDir}/${file}`;
    if (!existsSync(p)) {
      warnings.push(`[android] missing ${file}`);
      continue;
    }
    const content = readFileSync(p, "utf8");
    const len = content.length;
    if (len > limit) errors.push(`[android/${file}] ${len} > ${limit} chars`);
  }
  if (existsSync(androidGB) && existsSync(androidUS)) {
    warnings.push("[android] both en-GB and en-US listings exist — keep both in sync");
  }
}

// Phone number format check
if (existsSync("ios/.env.review")) {
  const env = readFileSync("ios/.env.review", "utf8");
  const phone = env.match(/ASC_REVIEW_PHONE=(.+)/)?.[1]?.trim();
  if (phone && !phone.startsWith("+")) {
    errors.push(`[reviewer] phone "${phone}" missing country code. Apple rejects without leading + and country code.`);
  }
  if (phone && /\s/.test(phone)) {
    warnings.push(`[reviewer] phone "${phone}" contains spaces — works but cleaner without`);
  }
}

console.log("");
if (errors.length === 0 && warnings.length === 0) {
  console.log("✓ All checks passed.");
  process.exit(0);
}
for (const w of warnings) console.log(`⚠  ${w}`);
for (const e of errors) console.log(`✗  ${e}`);
console.log("");
if (errors.length > 0) {
  console.log(`${errors.length} error(s) — fix before pushing.`);
  process.exit(1);
}
console.log(`${warnings.length} warning(s) — review but not blocking.`);
