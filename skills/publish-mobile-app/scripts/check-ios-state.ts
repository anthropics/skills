#!/usr/bin/env bun
// Query App Store Connect API to verify what is actually live on the listing.
// Use after every metadata/screenshot push — fastlane's "Successfully uploaded"
// log can be misleading (e.g. iPad screenshots routed to the wrong slot).
//
// Run from project root: bun check-ios-state.ts

import { readFileSync, existsSync } from "node:fs";
import { createSign } from "node:crypto";

const keyPath = ["ios/app-store-connect-key.json", "ios/App/app-store-connect-key.json"].find(existsSync);
if (!keyPath) {
  console.error("ios/app-store-connect-key.json not found. Run bootstrap-app-store-key.ts first.");
  process.exit(1);
}

const key = JSON.parse(readFileSync(keyPath, "utf8"));
const header = Buffer.from(JSON.stringify({ alg: "ES256", kid: key.key_id, typ: "JWT" })).toString("base64url");
const payload = Buffer.from(JSON.stringify({
  iss: key.issuer_id,
  iat: Math.floor(Date.now() / 1000),
  exp: Math.floor(Date.now() / 1000) + 600,
  aud: "appstoreconnect-v1",
})).toString("base64url");
const sig = createSign("SHA256").update(`${header}.${payload}`).sign({ key: key.key, dsaEncoding: "ieee-p1363" }).toString("base64url");
const auth = { Authorization: `Bearer ${header}.${payload}.${sig}` };

// Find bundle id from common locations
const bundleId = process.env.BUNDLE_ID
  ?? (existsSync("ios/fastlane/Appfile") && readFileSync("ios/fastlane/Appfile", "utf8").match(/app_identifier\("([^"]+)"\)/)?.[1])
  ?? (existsSync("app.json") && JSON.parse(readFileSync("app.json", "utf8")).expo?.ios?.bundleIdentifier);
if (!bundleId) {
  console.error("Could not auto-detect bundle ID. Set BUNDLE_ID=com.example.app or add to ios/fastlane/Appfile");
  process.exit(1);
}

const apps = await fetch(`https://api.appstoreconnect.apple.com/v1/apps?filter[bundleId]=${bundleId}`, { headers: auth }).then(r => r.json()) as any;
if (!apps.data?.[0]) {
  console.error(`No app found for bundle id ${bundleId}`);
  process.exit(1);
}
const appId = apps.data[0].id;
console.log(`App: ${apps.data[0].attributes.name} (${appId}, bundle ${bundleId})\n`);

// Versions
const versions = await fetch(`https://api.appstoreconnect.apple.com/v1/apps/${appId}/appStoreVersions?limit=3`, { headers: auth }).then(r => r.json()) as any;
console.log("Versions:");
for (const v of versions.data ?? []) {
  console.log(`  v${v.attributes.versionString.padEnd(8)}  state=${v.attributes.appStoreState}  id=${v.id}`);
}
const versionId = versions.data?.[0]?.id;
if (!versionId) process.exit(0);

// Stable metadata (name, subtitle) lives on appInfoLocalizations
const ai = await fetch(`https://api.appstoreconnect.apple.com/v1/apps/${appId}/appInfos`, { headers: auth }).then(r => r.json()) as any;
const editableInfo = ai.data?.find((i: any) => ["PREPARE_FOR_SUBMISSION","WAITING_FOR_REVIEW","DEVELOPER_REJECTED","REJECTED","METADATA_REJECTED"].includes(i.attributes.state)) ?? ai.data?.[0];
if (editableInfo) {
  const ail = await fetch(`https://api.appstoreconnect.apple.com/v1/appInfos/${editableInfo.id}/appInfoLocalizations`, { headers: auth }).then(r => r.json()) as any;
  console.log(`\nStable metadata (appInfo ${editableInfo.id}, state=${editableInfo.attributes.state}):`);
  for (const l of ail.data ?? []) {
    console.log(`  [${l.attributes.locale}]  name="${l.attributes.name}"  subtitle="${l.attributes.subtitle ?? "(empty)"}"`);
  }
}

// Per-version metadata lives on appStoreVersionLocalizations
const locs = await fetch(`https://api.appstoreconnect.apple.com/v1/appStoreVersions/${versionId}/appStoreVersionLocalizations`, { headers: auth }).then(r => r.json()) as any;
console.log(`\nVersion metadata (version ${versions.data[0].attributes.versionString}):`);
for (const loc of locs.data ?? []) {
  const a = loc.attributes;
  console.log(`  [${a.locale}]`);
  console.log(`    description:        ${(a.description ?? "(empty)").slice(0, 80)}...`);
  console.log(`    promotional_text:   ${(a.promotionalText ?? "(empty)").slice(0, 80)}`);
  console.log(`    keywords:           ${a.keywords ?? "(empty)"}`);
  console.log(`    whats_new:          ${(a.whatsNew ?? "(empty)").slice(0, 80)}`);

  const sets = await fetch(`https://api.appstoreconnect.apple.com/v1/appStoreVersionLocalizations/${loc.id}/appScreenshotSets`, { headers: auth }).then(r => r.json()) as any;
  console.log(`    screenshot sets:`);
  for (const set of sets.data ?? []) {
    const shots = await fetch(`https://api.appstoreconnect.apple.com/v1/appScreenshotSets/${set.id}/appScreenshots`, { headers: auth }).then(r => r.json()) as any;
    const states = shots.data.map((s: any) => s.attributes.assetDeliveryState?.state ?? "?").join(",");
    console.log(`      ${set.attributes.screenshotDisplayType.padEnd(35)} count=${shots.data.length}  states=[${states}]`);
  }
}
