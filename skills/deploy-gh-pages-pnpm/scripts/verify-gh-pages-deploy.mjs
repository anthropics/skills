#!/usr/bin/env node
/**
 * Poll GitHub Actions + the live GitHub Pages URL until:
 *  - a successful run exists for expectSha (optionally a specific workflow file)
 *  - build-manifest.json is reachable and its github_sha matches expectSha
 *  - GitHub annotations contain zero "failure" and zero "warning" (by default)
 *
 * Usage:
 *   node scripts/verify-gh-pages-deploy.mjs \
 *     --url https://<owner>.github.io/<repo> \
 *     --expect-sha <full_or_short_sha> \
 *     [--workflow pages.yml] \
 *     [--timeout-seconds 900] \
 *     [--allow-warnings]
 *
 * Requires `gh` in PATH and `gh auth status` to succeed for API calls.
 */
import { execFileSync } from "node:child_process";

function parseArgs(argv) {
  const out = {
    url: "",
    expectSha: "",
    workflow: "",
    timeoutSeconds: 900,
    allowWarnings: false,
  };
  for (let i = 2; i < argv.length; i++) {
    const a = argv[i];
    const next = argv[i + 1];
    if (a === "--url") out.url = next && (i++, next);
    else if (a === "--expect-sha") out.expectSha = next && (i++, next);
    else if (a === "--workflow") out.workflow = next && (i++, next);
    else if (a === "--timeout-seconds")
      out.timeoutSeconds = Number(next && (i++, next));
    else if (a === "--allow-warnings") out.allowWarnings = true;
  }
  if (!out.url || !out.expectSha) {
    console.error(
      "Missing required args.\n\n" +
        "Example:\n" +
        "  node scripts/verify-gh-pages-deploy.mjs \\\n" +
        "    --url https://<owner>.github.io/<repo>/ \\\n" +
        "    --expect-sha <commit_sha> \\\n" +
        "    [--workflow pages.yml] \\\n" +
        "    [--timeout-seconds 900] \\\n" +
        "    [--allow-warnings]\n",
    );
    process.exit(2);
  }
  return out;
}

function ghJson(args) {
  const out = execFileSync("gh", args, { encoding: "utf8" });
  return JSON.parse(out);
}

function normalizeSha(sha) {
  return sha.trim().toLowerCase();
}

function shaMatches(a, b) {
  const na = normalizeSha(a);
  const nb = normalizeSha(b);
  return na === nb || na.startsWith(nb) || nb.startsWith(na);
}

function manifestUrlFromPagesBase(pagesBaseUrl) {
  const base = new URL(pagesBaseUrl);
  if (!base.pathname.endsWith("/")) base.pathname += "/";
  return new URL("build-manifest.json", base).href;
}

async function fetchText(url) {
  const res = await fetch(url, { redirect: "follow" });
  if (!res.ok) throw new Error(`GET ${url} -> ${res.status}`);
  return await res.text();
}

function sleep(ms) {
  return new Promise((r) => setTimeout(r, ms));
}

const args = parseArgs(process.argv);
const deadline = Date.now() + args.timeoutSeconds * 1000;
const manifestUrl = manifestUrlFromPagesBase(args.url);

// owner/repo from gh
const repoJson = ghJson(["repo", "view", "--json", "nameWithOwner"]);
const ownerRepo = repoJson.nameWithOwner;

function listRunsForSha() {
  const wfArgs = args.workflow
    ? ["--workflow", args.workflow]
    : [];
  const runs = ghJson([
    "run",
    "list",
    "--repo",
    ownerRepo,
    "--limit",
    "20",
    "--json",
    "databaseId,headSha,conclusion,status,name,workflowName,event",
    ...wfArgs,
  ]);
  return runs.filter((r) => shaMatches(r.headSha, args.expectSha));
}

function annotationsForRun(runId) {
  return ghJson([
    "api",
    `repos/${ownerRepo}/actions/runs/${runId}/annotations`,
    "--paginate",
  ]);
}

async function main() {
  process.stdout.write(
    `Verifying deploy for ${ownerRepo}\n  Pages base: ${args.url}\n  Manifest: ${manifestUrl}\n  Expect SHA: ${args.expectSha}\n`,
  );

  while (Date.now() < deadline) {
    const runs = listRunsForSha();
    const success = runs.find((r) => r.conclusion === "success");
    if (!success) {
      process.stdout.write(
        `. waiting for successful Actions run for SHA (seen ${runs.length} matching runs)\n`,
      );
      await sleep(5000);
      continue;
    }

    const anns = annotationsForRun(success.databaseId);
    const failures = anns.filter((a) => a.level === "failure");
    const warnings = anns.filter((a) => a.level === "warning");
    if (failures.length) {
      console.error("\nGitHub Actions annotations include failures:\n");
      console.error(JSON.stringify(failures, null, 2));
      process.exit(3);
    }
    if (!args.allowWarnings && warnings.length) {
      console.error("\nGitHub Actions annotations include warnings:\n");
      console.error(JSON.stringify(warnings, null, 2));
      process.exit(4);
    }

    let manifest;
    try {
      const raw = await fetchText(manifestUrl);
      manifest = JSON.parse(raw);
    } catch (e) {
      process.stdout.write(
        `\nManifest fetch not OK yet (${String(e.message || e)}); retrying…\n`,
      );
      await sleep(5000);
      continue;
    }

    if (!manifest?.github_sha || !shaMatches(manifest.github_sha, args.expectSha)) {
      console.error("\nManifest github_sha mismatch:", manifest?.github_sha);
      process.exit(5);
    }

    if (!manifest?.stamp || !manifest?.codeword || !manifest?.buildNumber) {
      console.error("\nManifest missing stamp fields:", manifest);
      process.exit(6);
    }

    console.log("\nOK");
    console.log(
      JSON.stringify(
        {
          runId: success.databaseId,
          workflow: success.workflowName,
          stamp: manifest.stamp,
          codeword: manifest.codeword,
          buildNumber: manifest.buildNumber,
          manifestUrl,
        },
        null,
        2,
      ),
    );
    return;
  }

  console.error("\nTimed out waiting for successful deploy + manifest alignment.");
  process.exit(7);
}

await main();
