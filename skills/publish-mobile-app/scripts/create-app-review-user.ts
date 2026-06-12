#!/usr/bin/env bun
// Idempotently provision (or rotate password for) the App Store / Play Store
// reviewer user. Auto-detects Supabase (uses admin API). For other auth
// providers, prints instructions to do manually.
//
// Usage:
//   bun create-app-review-user.ts
//   REVIEWER_EMAIL=apple-review@yourdomain.com bun create-app-review-user.ts

import { randomBytes } from "node:crypto";
import { readFileSync, existsSync, writeFileSync } from "node:fs";
import { resolve } from "node:path";

const password = randomBytes(18).toString("base64url"); // 24 url-safe chars
const EMAIL = process.env.REVIEWER_EMAIL ?? "appstore-reviewer@" + (
  process.env.DOMAIN ?? "example.com"
);

// Auto-detect Supabase config from .env
const env: Record<string, string> = {};
if (existsSync(".env")) {
  for (const line of readFileSync(".env", "utf8").split("\n")) {
    const m = line.match(/^([A-Z_]+)=(.*)$/);
    if (m) env[m[1]] = m[2].replace(/^["']|["']$/g, "");
  }
}

const SUPABASE_URL = process.env.SUPABASE_URL ?? env.SUPABASE_URL;
// Supabase renamed service-role key naming over time
const SUPABASE_SECRET = process.env.SUPABASE_SECRET_KEY ?? env.SUPABASE_SECRET_KEY
  ?? process.env.SUPABASE_SERVICE_ROLE_KEY ?? env.SUPABASE_SERVICE_ROLE_KEY;

if (!SUPABASE_URL || !SUPABASE_SECRET) {
  console.log("Supabase config not detected. Manual setup needed:\n");
  console.log("1. Create a user in your auth provider with these credentials:");
  console.log(`   Email:    ${EMAIL}`);
  console.log(`   Password: ${password}`);
  console.log("");
  console.log("2. Pre-confirm email (reviewer can't access an inbox to verify)");
  console.log("");
  console.log("3. Seed any necessary onboarding data (credits, sample content, etc.)");
  console.log("   so reviewer doesn't hit an empty state");
  console.log("");
  console.log("4. Save the password to ios/.env.review (see below)");
  printEnvFile(EMAIL, password);
  process.exit(0);
}

const headers = {
  apikey: SUPABASE_SECRET,
  Authorization: `Bearer ${SUPABASE_SECRET}`,
  "Content-Type": "application/json",
};

const findUrl = new URL(`${SUPABASE_URL}/auth/v1/admin/users`);
findUrl.searchParams.set("email", EMAIL);
const findRes = await fetch(findUrl, { headers });
if (!findRes.ok) {
  console.error(`Supabase list-users failed: ${findRes.status} ${await findRes.text()}`);
  process.exit(1);
}
const existing = ((await findRes.json()) as any).users?.find(
  (u: any) => u.email?.toLowerCase() === EMAIL.toLowerCase()
);

let userId: string;
if (existing) {
  const res = await fetch(`${SUPABASE_URL}/auth/v1/admin/users/${existing.id}`, {
    method: "PUT",
    headers,
    body: JSON.stringify({ password, email_confirm: true }),
  });
  if (!res.ok) {
    console.error(`Password rotation failed: ${res.status} ${await res.text()}`);
    process.exit(1);
  }
  userId = existing.id;
  console.log(`✓ Rotated password for existing reviewer (${EMAIL})`);
} else {
  const res = await fetch(`${SUPABASE_URL}/auth/v1/admin/users`, {
    method: "POST",
    headers,
    body: JSON.stringify({
      email: EMAIL,
      password,
      email_confirm: true,
      user_metadata: { full_name: "App Store Reviewer", purpose: "store-review-only" },
    }),
  });
  if (!res.ok) {
    console.error(`User creation failed: ${res.status} ${await res.text()}`);
    process.exit(1);
  }
  userId = ((await res.json()) as any).id;
  console.log(`✓ Created reviewer user ${EMAIL}`);
}

console.log(`Supabase user id: ${userId}`);
printEnvFile(EMAIL, password);

function printEnvFile(email: string, pass: string) {
  console.log("");
  console.log("Save these credentials to ios/.env.review (already gitignored if you ran setup):");
  console.log("");
  const envPath = resolve("ios/.env.review");
  const sample = `# App Store / Play Store reviewer credentials. Loaded by ios:metadata.
# Rotate by re-running create-app-review-user.ts.

ASC_REVIEW_FIRST_NAME=Your
ASC_REVIEW_LAST_NAME=Name
ASC_REVIEW_EMAIL=your-email@example.com
# Required by App Store Connect. Format: +<country code><number>, no spaces.
ASC_REVIEW_PHONE=+10000000000
ASC_REVIEW_DEMO_USER=${email}
ASC_REVIEW_DEMO_PASSWORD=${pass}
ASC_REVIEW_NOTES="Brief reviewer instructions — how to test, what to expect. Mention any AI-generated content + safety filters. Avoid claims that imply the app is exclusively for children unless you're in the Kids Category."
`;
  if (existsSync(envPath)) {
    console.log(`File ${envPath} already exists. Update ASC_REVIEW_DEMO_PASSWORD to:`);
    console.log(`  ${pass}`);
  } else {
    writeFileSync(envPath, sample, { mode: 0o600 });
    console.log(`✓ Wrote template to ${envPath} (mode 600). Edit phone/notes before running ios:metadata.`);
  }
}
