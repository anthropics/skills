#!/usr/bin/env bun
// Print reviewer creds in copy-paste-friendly format for Play Console
// "App access → Add new instructions" (which has no API).
// Single source of truth: ios/.env.review.
//
// Usage: bun print-reviewer-creds.ts

import { readFileSync, existsSync } from "node:fs";
import { resolve } from "node:path";

const path = resolve("ios/.env.review");
if (!existsSync(path)) {
  console.error(`Not found: ${path}`);
  console.error("Run: bun create-app-review-user.ts first.");
  process.exit(1);
}

const env: Record<string, string> = {};
for (const line of readFileSync(path, "utf8").split("\n")) {
  const m = line.match(/^([A-Z_]+)=(.*)$/);
  if (!m) continue;
  let v = m[2];
  if (v.startsWith('"') && v.endsWith('"')) v = v.slice(1, -1);
  env[m[1]] = v;
}

const user = env.ASC_REVIEW_DEMO_USER ?? "";
const pass = env.ASC_REVIEW_DEMO_PASSWORD ?? "";
const notes = env.ASC_REVIEW_NOTES ?? "";

console.log("\n═══ Play Console → App access → Add new instructions ═══\n");
console.log(`Instruction name:   App reviewer login`);
console.log(`Username:           ${user}`);
console.log(`Password:           ${pass}`);
console.log(`Other instructions: ${notes}\n`);

console.log("═══ App Store Connect → App Review Information (reference only) ═══");
console.log("Auto-pushed by `fastlane metadata`. To verify, run check-ios-state.ts.\n");
console.log(`First name:     ${env.ASC_REVIEW_FIRST_NAME ?? ""}`);
console.log(`Last name:      ${env.ASC_REVIEW_LAST_NAME ?? ""}`);
console.log(`Phone:          ${env.ASC_REVIEW_PHONE ?? ""}`);
console.log(`Email:          ${env.ASC_REVIEW_EMAIL ?? ""}`);
console.log(`Demo user:      ${user}`);
console.log(`Demo password:  ${pass}`);
console.log(`Notes:          ${notes}\n`);
