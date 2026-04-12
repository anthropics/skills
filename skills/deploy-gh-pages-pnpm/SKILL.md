---
name: deploy-gh-pages-pnpm
description: >-
  Deploys static sites to GitHub Pages using GitHub Actions with pnpm, stamps
  each deployment with a randomized codeword plus numeric build id in
  build-manifest.json, and verifies success by watching Actions runs, GitHub
  annotations, and the live site until errors and warnings are cleared. Use
  when the user asks for GitHub Pages publishing, pnpm CI deploys, Actions +
  Pages setup, deploy verification, or fixing Pages pipeline failures and noisy
  warnings.
---

# Deploy GitHub Pages (pnpm + Actions + verify loop)

## Preconditions I verify first

- `gh auth status` succeeds for the repo host (scopes should include `repo` and `workflow` when reading runs and annotations).
- Remote is GitHub and **Pages** is configured to **GitHub Actions** (not legacy branch uploads unless the user explicitly chose that).
- The project can emit a **static directory** (`dist`, `out`, exported `.next`, etc.). Pure SSR servers are out of scope—stop and negotiate a different host.
- **pnpm** is the package manager for CI: `pnpm-lock.yaml` should exist; use `pnpm install --frozen-lockfile` in Actions.

If any hard prerequisite is missing, I stop with a crisp blocker instead of half-configuring Pages.

## Assets I copy into the target repo

Copy (or recreate) these files from the skill pack next to the repository root:

- `scripts/generate-build-manifest.mjs`
- `scripts/codewords.txt`
- `scripts/verify-gh-pages-deploy.mjs`

Keep paths stable so the workflow below can call them as `node scripts/generate-build-manifest.mjs`.

## Build stamp (unique codeword + number every push)

After `pnpm run build` and **before** `actions/upload-pages-artifact`:

1. Set `OUTPUT_DIR` to the real output folder (must already exist).
2. Optionally set `CODWORDS_FILE` if the word list is not at `scripts/codewords.txt`.
3. Run `node scripts/generate-build-manifest.mjs`.

This writes `build-manifest.json` into the static root with:

- `codeword` — random line from `codewords.txt`
- `buildNumber` — cryptographically strong 6-digit integer
- `stamp` — `codeword-buildNumber` (human grep-friendly)
- `github_sha`, `github_run_id`, `github_repository` when the GitHub Actions env vars are visible to the step

Every push that rebuilds therefore produces a **fresh stamp** that I can compare against the live site.

## Workflow skeleton

Author `.github/workflows/pages.yml` using the **official** `actions/configure-pages` / `actions/upload-pages-artifact` / `actions/deploy-pages` flow with **pnpm** setup. A full, copy-ready YAML lives in [reference.md](reference.md)—prefer adapting that template over improvising permissions.

Minimum permission block:

```yaml
permissions:
  contents: read
  pages: write
  id-token: write
```

## Push → watch → verify (mandatory loop)

After I commit workflow + scripts:

1. `git push` to the branch that triggers Pages (usually `main`).
2. `gh run watch --exit-status` on the new run **or** poll with `gh run list --workflow <file> --limit 5`.
3. When the run is green, run the bundled verifier from the repo root (Node 20+):

```bash
node scripts/verify-gh-pages-deploy.mjs \
  --url "https://<owner>.github.io/<repo>/" \
  --expect-sha "$(git rev-parse HEAD)" \
  --workflow pages.yml
```

Flags:

- `--timeout-seconds` — default 900.
- `--allow-warnings` — only if the user explicitly relaxes the policy; default behavior must stay **warning-free**.

The verifier cross-checks:

- newest **successful** Actions run for that SHA (optionally filtered by workflow file)
- GitHub **annotations** for the run (fail if any `failure`; fail if any `warning` unless overridden)
- HTTP `build-manifest.json` matches the same SHA and contains a fresh `stamp`

If anything fails, I treat the deploy as **not done** even if the badge is green.

## “Warning-free” definition (strict but honest)

I enforce **three** layers; a deploy is not accepted until all applicable layers are clean:

1. **Process exit codes** — `pnpm run build`, `pnpm test`, `pnpm run lint`, etc. must exit 0.
2. **Tooling rules** — when ESLint exists, run with `--max-warnings 0` (wire this in `package.json` scripts). When `tsc` exists, ensure `noEmitOnError` behavior is on for CI typechecks.
3. **GitHub annotations** — surfaced by `verify-gh-pages-deploy.mjs`. If a tool only writes warnings to logs without annotations, I also scan the **job log** for obvious warning patterns (`WARN`, `Warning:`) and fix them; if ambiguity remains, I tighten the script or formatter so warnings become failing exits.

If the repo truly has **no** `lint` script, I do **not** silently treat that as “warning-free by default”: I either add a minimal ESLint (with `--max-warnings 0`) + script, or I obtain an explicit user waiver for skipping static analysis—documented in the handoff.

I do **not** treat generic third-party deprecation **notices** as automatically blocking unless they surface as annotations or non-zero exits—when they do, I still clear them.

## Failure classes → what I change

| Signal | Likely fix |
| --- | --- |
| `permissions` denied for `id-token` / `pages` | Patch workflow permissions; ensure org policy allows GitHub Pages OIDC. |
| `pnpm install` fails | Lockfile drift → regenerate locally with pnpm, commit `pnpm-lock.yaml`, re-run frozen install. |
| Build cannot find `base` assets on `/repo/` subpath | Set bundler `base` / `assetPrefix` / `homepage` equivalent to `/repo/`. |
| Artifact empty / wrong path | Align `OUTPUT_DIR` with the bundler output; confirm manifest step runs **after** build creates the folder. |
| Manifest 404 on site | Confirm file lands under artifact root; confirm Pages URL includes trailing slash when using the verify script; bust CDN cache by waiting and retrying. |
| Annotations show warnings | Fix source, or change tooling config so warnings fail CI, per user policy. |

## SPA / framework reminders

- **Vite:** `base: '/repo/'` for project pages.
- **Astro static:** set `site` + `base` appropriately.
- **React Router / client routers:** configure basename to `/repo`.

If unsure, I read the project’s config files (`vite.config.*`, `astro.config.*`, `next.config.*`) instead of guessing.

## Operating discipline (consultant stance)

- I keep the user’s repository **free of secrets** in logs; prefer `GITHUB_TOKEN` + `deploy-pages`.
- I never declare victory from **Actions alone**—I always align HEAD SHA with `build-manifest.json` on the public URL the user cares about.
- If the user wants me to keep monitoring across multiple pushes, I repeat the loop for the newest SHA each time.

## Progressive disclosure

- Long YAML, edge cases, and CLI snippets: [reference.md](reference.md)
- Executable helpers: `scripts/`
