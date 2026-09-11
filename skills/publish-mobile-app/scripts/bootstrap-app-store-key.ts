#!/usr/bin/env bun
// Assembles ios/app-store-connect-key.json from an Apple .p8 file + key/issuer IDs.
// Self-contained JSON works without keeping the .p8 around — but the script also
// moves the .p8 to ~/.appstoreconnect/private_keys/ (standard fastlane location)
// if it's still in ~/Downloads.
//
// Usage:
//   ASC_KEY_ID=ABC123XYZ \
//   ASC_ISSUER_ID=abcd1234-5678-90ab-cdef-1234567890ab \
//   ASC_KEY_PATH=~/Downloads/AuthKey_ABC123XYZ.p8 \
//   bun bootstrap-app-store-key.ts

import { readFileSync, writeFileSync, existsSync, mkdirSync, copyFileSync, unlinkSync } from "node:fs";
import { homedir } from "node:os";
import { resolve, dirname } from "node:path";

const keyId = process.env.ASC_KEY_ID;
const issuerId = process.env.ASC_ISSUER_ID;
const rawPath = process.env.ASC_KEY_PATH;

if (!keyId || !issuerId || !rawPath) {
  console.error("Missing required env vars.");
  console.error("  ASC_KEY_ID    – 10-char Key ID from App Store Connect");
  console.error("  ASC_ISSUER_ID – UUID Issuer ID");
  console.error("  ASC_KEY_PATH  – path to AuthKey_<KEY_ID>.p8");
  console.error("");
  console.error("Get all three at: App Store Connect → Users and Access → Integrations → App Store Connect API");
  process.exit(1);
}

const expand = (p: string) => p.startsWith("~/") ? resolve(homedir(), p.slice(2)) : resolve(p);
const keyPath = expand(rawPath);

if (!existsSync(keyPath)) {
  console.error(`.p8 file not found at ${keyPath}`);
  process.exit(1);
}

const pem = readFileSync(keyPath, "utf8").trim();
if (!pem.startsWith("-----BEGIN PRIVATE KEY-----")) {
  console.error(`File at ${keyPath} does not look like a PEM private key.`);
  process.exit(1);
}

// Find iOS dir — works for Capacitor, Flutter, Expo prebuild
const iosDir = ["ios", "ios/App"].find((p) => existsSync(p)) ?? "ios";
mkdirSync(iosDir, { recursive: true });

const out = { key_id: keyId, issuer_id: issuerId, key: pem };
const outPath = resolve(iosDir, "app-store-connect-key.json");
writeFileSync(outPath, JSON.stringify(out, null, 2) + "\n", { mode: 0o600 });
console.log(`✓ Wrote ${outPath} (mode 600)`);

// Move .p8 to canonical fastlane location if it's still in Downloads
const stdLocation = resolve(homedir(), `.appstoreconnect/private_keys/AuthKey_${keyId}.p8`);
if (keyPath.includes("/Downloads/") && !existsSync(stdLocation)) {
  mkdirSync(dirname(stdLocation), { recursive: true });
  copyFileSync(keyPath, stdLocation);
  if (readFileSync(stdLocation, "utf8") === readFileSync(keyPath, "utf8")) {
    unlinkSync(keyPath);
    console.log(`✓ Moved .p8 to ${stdLocation} (verified identical, removed from Downloads)`);
  }
}

console.log("");
console.log("Add to .gitignore if not already there:");
console.log("  ios/app-store-connect-key.json");
console.log("  *.p8");
console.log("");
console.log("Now you can run: fastlane metadata (or your wrapper script)");
