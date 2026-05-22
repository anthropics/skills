---
name: "nf-core-utils-release"
description: "Use when the user asks to release, cut, publish, ship, or verify an nf-core/nf-core-utils plugin release. This skill covers the full release path: confirming PR/CI state, preparing a clean worktree, configuring the Nextflow Plugin Registry token safely via the user's global Gradle config, running the Gradle/Make release, creating the matching GitHub release, and verifying GitHub releases against the Nextflow Plugin Registry. Use it even if the user only says 'cut a release' or 'is it on the registry?' while working in nf-core-utils."
---

# nf-core-utils release

## Purpose

Release `nf-core/nf-core-utils` safely to both:

1. the Nextflow Plugin Registry, and
2. GitHub Releases.

The release flow is intentionally conservative because it touches public artifacts and secrets. Prefer clean worktrees, explicit verification, and redacted output.

## Before releasing

1. Confirm the target repository and branch.
   - Expected repo: `nf-core/nf-core-utils`.
   - Expected release branch: `main`, usually after merging a PR.
   - If currently in a side worktree or feature branch, do not assume it is safe to release from there.
2. Check PR/CI state when a PR is involved.
   - `gh pr view <pr> --json state,mergeStateStatus,statusCheckRollup,mergedAt,mergeCommit,url`
   - Release only after the PR is merged and required checks are green, unless the user explicitly instructs otherwise.
3. Check the version in `build.gradle`.
   - `grep -n "^version" build.gradle`
   - Confirm it is the intended version and newer than the latest released version.
4. Check the changelog.
   - Ensure `CHANGELOG.md` has an entry for the version being released.
5. Verify the local GitHub CLI context.
   - `gh auth status`
   - `gh repo view --json nameWithOwner,url`

## Secret handling

The Nextflow Gradle plugin reads the registry token from `npr.apiKey` or `NPR_API_KEY`, not from the older README example `pluginRegistry.accessToken`.

If the user provides the 1Password reference:

```text
op://Employee/Nextflow Plugin Registry Token/credential
```

read it with `op read` and write it only to the user's global Gradle properties file using the bundled helper:

```bash
TOKEN="$(op read 'op://Employee/Nextflow Plugin Registry Token/credential')"
python "<path-to-skill>/scripts/configure_registry_token.py" "$TOKEN"
unset TOKEN
grep -E 'github_|npr\.apiKey|pluginRegistry' ~/.gradle/gradle.properties | sed 's/=.*/=<redacted>/'
```

Important:
- Do not write tokens into the repository.
- Do not print the token.
- Redact `~/.gradle/gradle.properties` output.
- If the user asks where the token went, answer clearly: `~/.gradle/gradle.properties`, not the codebase.

## Recommended release workflow

Use a clean temporary worktree at `origin/main` so local untracked files in the user's normal checkout cannot interfere.

```bash
git fetch origin main --tags
rm -rf /tmp/nf-core-utils-release
git worktree add /tmp/nf-core-utils-release origin/main
cd /tmp/nf-core-utils-release
```

Verify the checkout:

```bash
git status --short
git log --oneline -3
grep -n "^version" build.gradle
```

Build before publishing:

```bash
./gradlew assemble --no-daemon
```

Release to the Nextflow Plugin Registry:

```bash
make release
```

A successful registry release includes output like:

```text
Plugin 'nf-core-utils' version X.Y.Z has been successfully released to Nextflow Registry [https://registry.nextflow.io/api]!
```

If release fails with `HTTP 401`:
- Check that `~/.gradle/gradle.properties` contains `npr.apiKey=<redacted>`.
- If only `pluginRegistry.accessToken` is present, add `npr.apiKey`; the Gradle plugin expects `npr.apiKey` or `NPR_API_KEY`.
- Re-run `make release` from the clean worktree.

## Create the GitHub release

The Nextflow registry release may not create a GitHub release/tag. Check first:

```bash
gh release list --limit 10
git tag --list | sort -V | tail -20
```

If the target version is not present on GitHub, create it from the released commit on `main`. Use changelog notes when available.

```bash
VERSION="0.5.0"  # replace with build.gradle version
TARGET_SHA="$(git rev-parse HEAD)"
python "<path-to-skill>/scripts/extract_release_notes.py" "$VERSION" > "/tmp/release-${VERSION}-notes.md"
gh release create "$VERSION" --target "$TARGET_SHA" --title "$VERSION" --notes-file "/tmp/release-${VERSION}-notes.md"
```

If a release already exists, do not overwrite it unless the user explicitly asks.

## Verify all release surfaces

Check GitHub releases:

```bash
gh release list --limit 20
```

Check the Nextflow Plugin Registry:

```bash
python3 - <<'PY'
import json, urllib.request
with urllib.request.urlopen('https://registry.nextflow.io/api/v1/plugins/nf-core-utils') as response:
    data = json.load(response)
for r in data['plugin']['releases']:
    print(r['version'], r.get('status'), r.get('date'))
PY
```

Compare GitHub and registry versions:

```bash
python "<path-to-skill>/scripts/compare_release_surfaces.py"
```

Known historical state after releasing `0.5.0`:
- GitHub releases: `0.1.0`, `0.2.0`, `0.3.0`, `0.3.1`, `0.4.0`, `0.5.0`
- Registry releases: `0.2.0`, `0.3.0`, `0.3.1`, `0.4.0`, `0.5.0`
- `0.1.0` exists on GitHub but not in the registry.

Treat this historical note as a clue, not a source of truth: always query current GitHub and registry state.

## Bundled scripts

- `scripts/configure_registry_token.py` — updates `~/.gradle/gradle.properties` with `npr.apiKey` and a compatibility `pluginRegistry.accessToken`, printing only redacted confirmation.
- `scripts/extract_release_notes.py` — extracts a version section from `CHANGELOG.md` for GitHub release notes.
- `scripts/compare_release_surfaces.py` — compares GitHub Releases with the Nextflow Plugin Registry and reports missing versions in either direction.

## Final response checklist

When done, tell the user:

- the version released,
- whether the Nextflow Plugin Registry release succeeded,
- the GitHub release URL,
- the target commit SHA,
- any known mismatch between GitHub releases and registry releases,
- where credentials were written, if credentials were touched (`~/.gradle/gradle.properties`, redacted).

Keep the final answer concise and avoid exposing secrets.
