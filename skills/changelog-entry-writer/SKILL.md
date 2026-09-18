---
name: changelog-entry-writer
description: Turns a diff, commit list, or PR description into a well-formatted changelog entry following the Keep a Changelog convention. Use this whenever the user asks to update a CHANGELOG.md, write release notes, summarize what changed for a version bump, or prepare a changelog entry from a diff or set of commits — even if they just say "add this to the changelog" or "what should go in the release notes."
---

# Changelog Entry Writer

Changelogs are read by people who did not write the code and are deciding whether a change affects them. The job here is not to summarize the diff — it's to translate implementation detail into the consequence a reader cares about. A entry like "refactored the auth middleware" tells a user nothing; "fixed a bug where sessions expired early on Safari" tells them exactly what to check.

## Workflow

1. **Find the existing changelog.** Look for `CHANGELOG.md` at the project root. If one exists, read it to match its established format, heading style, and tone — consistency with what's already there matters more than any external convention. If none exists, default to [Keep a Changelog](https://keepachangelog.com/): an `## [Unreleased]` section at the top, grouped by category.

2. **Gather the actual change.** Use whatever the user provided — a diff, a PR description, a range of commits (`git log`), or their own description. If it's ambiguous which commits or files are in scope, ask rather than guessing at the range.

3. **Classify each change** into the Keep a Changelog categories:
   - `Added` for new features
   - `Changed` for changes in existing functionality
   - `Deprecated` for soon-to-be-removed features
   - `Removed` for now-removed features
   - `Fixed` for bug fixes
   - `Security` for vulnerability fixes

   A single diff often contains changes in more than one category — split them rather than forcing everything under one heading.

4. **Write from the reader's perspective, not the diff's.** Each entry should be one line, in the imperative or past tense (match whatever the existing file uses), describing the user-visible effect:
   - Bad: "Updated `parseConfig()` to handle the `retries` field"
   - Good: "Added support for configuring request retry count via `retries` in the config file"
   - Bad: "Fixed null check in `SessionManager`"
   - Good: "Fixed a crash when signing in with an expired session token"

   If a change is purely internal (refactor, test coverage, tooling) with no user-visible effect, say so plainly and ask whether it belongs in the changelog at all — most changelogs intentionally omit these.

5. **Insert the entries** under the right category in `[Unreleased]` (or the version the user specifies), creating that category heading if it doesn't already exist. Preserve the file's existing entries and ordering — don't reformat unrelated sections.

## Example

**Input:** a diff adding a `--timeout` CLI flag, plus a fix for a crash when the input file is empty.

**Output:**
```markdown
## [Unreleased]

### Added
- `--timeout` flag to override the default request timeout

### Fixed
- Crash when running the CLI against an empty input file
```

## Guidelines

- Keep each entry to one line. If a change needs more than a sentence to explain, that's a sign it should be two entries or that the summary is trying to do too much.
- Don't invent user impact that isn't there — if you can't tell what a change does from the diff alone, ask rather than speculate.
- Preserve version numbers, dates, and links to issues/PRs already present in the file; add a link to the relevant PR or issue for the new entry if the user provides one.
- Never rewrite past releases' entries unless the user explicitly asks for a changelog cleanup.
