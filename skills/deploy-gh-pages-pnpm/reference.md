# Reference: GitHub Pages + Actions (pnpm) templates

This file holds **copy-ready** material that would bloat `SKILL.md`. Keep `SKILL.md` as the control plane; open this when generating YAML or debugging edge cases.

## Permissions model (recommended)

GitHub’s modern Pages deployment expects:

- `contents: read` for checkout
- `pages: write` to publish
- `id-token: write` for OIDC exchange inside `actions/deploy-pages`

Repository Settings → **Pages** → **Build and deployment** → Source: **GitHub Actions**.

## Example workflow: `.github/workflows/pages.yml`

> Adjust `OUTPUT_DIR`, install filters, and build script names to the repo. This template assumes a static `pnpm run build` emits `dist/`.

```yaml
name: Deploy GitHub Pages

on:
  push:
    branches: ["main"]
  workflow_dispatch:

permissions:
  contents: read
  pages: write
  id-token: write

concurrency:
  group: pages
  cancel-in-progress: true

jobs:
  build:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - uses: pnpm/action-setup@v4
        with:
          version: 9

      - uses: actions/setup-node@v4
        with:
          node-version: 20
          cache: pnpm

      - name: Install
        run: pnpm install --frozen-lockfile

      - name: Lint (fail on warnings)
        run: pnpm run --if-present lint

      - name: Typecheck
        run: pnpm run --if-present typecheck

      - name: Build
        run: pnpm run build

      - name: Setup Pages
        uses: actions/configure-pages@v5

      - name: Stamp build manifest (codeword + number)
        env:
          GITHUB_SHA: ${{ github.sha }}
          GITHUB_RUN_ID: ${{ github.run_id }}
          GITHUB_REPOSITORY: ${{ github.repository }}
          OUTPUT_DIR: dist
          CODWORDS_FILE: scripts/codewords.txt
        run: node scripts/generate-build-manifest.mjs

      - name: Upload artifact
        uses: actions/upload-pages-artifact@v3
        with:
          path: dist

  deploy:
    needs: build
    runs-on: ubuntu-latest
    environment:
      name: github-pages
      url: ${{ steps.deployment.outputs.page_url }}
    steps:
      - id: deployment
        uses: actions/deploy-pages@v4
```

### Notes

- **Vite / Astro / static Next export:** keep `OUTPUT_DIR` aligned with the tool (`dist`, `out`, `.next` static export directory, etc.).
- **SPA base path:** if the site is served from `https://owner.github.io/repo/`, configure the bundler `base` to `/repo/` so asset URLs resolve; the manifest still lives at `.../repo/build-manifest.json` relative to host root, which matches `https://owner.github.io/repo/` as the Pages base URL passed to the verify script.
- **Custom domain:** use the custom origin as `--url` for verification instead of `github.io`.

## pnpm lockfile policy

Prefer `--frozen-lockfile` in CI. If the repo legitimately has no `pnpm-lock.yaml` yet, run `pnpm install` locally once, commit the lockfile, then enable frozen installs.

## Legacy alternative (not default)

`peaceiris/actions-gh-pages` can push to `gh-pages` branch with a PAT. Avoid introducing PATs when `deploy-pages` OIDC flow is available.

## Useful `gh` queries

```bash
gh run list --workflow pages.yml --limit 10 --json databaseId,headSha,conclusion,status,url
gh run watch <run-id> --exit-status
gh run view <run-id> --log
gh api repos/<owner>/<repo>/actions/runs/<run-id>/annotations --paginate
```

## Live site checks

```bash
curl -fsSL "https://<owner>.github.io/<repo>/build-manifest.json" | jq .
```

If `jq` is unavailable, use Node: `node -e "fetch(process.argv[1]).then(r=>r.text()).then(console.log)" 'URL'`.
