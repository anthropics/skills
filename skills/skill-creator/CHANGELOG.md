# Changelog

All notable changes to the `skill-creator` skill in this fork are documented in this file.

The format is based on [Keep a Changelog 1.1.0](https://keepachangelog.com/en/1.1.0/),
and the skill version follows [Semantic Versioning 2.0.0](https://semver.org/spec/v2.0.0.html).

Upstream reference: <https://github.com/anthropics/skills/tree/main/skills/skill-creator>.
This fork's improvements are tracked here independently of upstream merges.

## [Unreleased]

_Nothing pending._

---

## [1.1.0] — 2026-05-21

First labeled release of the Cadtastic fork. Brings the skill into full alignment with the [Agent Skills specification](https://agentskills.io/specification), restructures the SKILL.md to fit the recommended token budget, adds a bundled frontmatter validator script, and introduces a scoped spec-drift workflow.

### Added

- **`scripts/validate_frontmatter.py`** — bundled validator that checks every frontmatter field constraint (`name`, `description`, `compatibility`, `metadata`, `allowed-tools`) in one pass. Uses PEP 723 inline metadata so `uv run` resolves PyYAML automatically. Designed per the agentskills.io agentic-use guidance: `--help`, `--format json`, meaningful exit codes (`0`/`1`/`2`), helpful error messages that embed the actual installer rejection string.
- **`references/spec-check.md`** — gated spec-drift workflow describing *when* to verify against the live agentskills.io documentation (before packaging, on validation failure, on user request — never on every invocation), *how* to compare deltas, and *what to do* on findings. Includes fallback behavior when network is unavailable.
- **`references/spec-source-map.md`** — topic→URL routing table for scoped spec-drift fetches. Forward map (concern → exact page to fetch) for targeted checks, reverse map (URL → coverage area) for periodic full audits. Replaces "fetch the whole spec page" with "fetch the smallest page that covers your concern."
- **`references/running-evals.md`** — full eval procedure (spawn, time, grade, aggregate, view) moved out of `SKILL.md` to fit the progressive-disclosure pattern the spec recommends.
- **`references/description-optimization.md`** — full description-optimization workflow moved out of `SKILL.md` for the same reason.
- **`references/environments.md`** — combined Claude.ai + Cowork environment-specific adaptations into a single reference, replacing the two inline sections in the upstream `SKILL.md`.
- **Frontmatter validation section** in `SKILL.md` — single consolidated subsection that points at the bundled validator, replacing two separate inline `python -c` validators previously embedded in the `name` and `description` field sections.
- **`metadata` frontmatter block** in `SKILL.md` declaring `version`, `fork`, and `upstream` keys per the Agent Skills spec.
- **`license: Apache-2.0`** in `SKILL.md` frontmatter (matches the `LICENSE.txt` bundled in this skill since the upstream copy).

### Changed

- **`SKILL.md` substantially restructured.** Reduced from ~8,490 tokens to ~3,655 tokens (57% reduction), now comfortably under the spec's recommended <5,000-token budget. Heavy procedural content moved to `references/` per progressive disclosure; the main body now focuses on the workflow, the frontmatter rules, and pointers to the references for deep dives.
- **Frontmatter constraints now fully documented in `SKILL.md`.** Upstream version mentioned only `name`, `description`, and `compatibility` with sparse detail; this version documents every spec-defined frontmatter field (`name`, `description`, `license`, `compatibility`, `metadata`, `allowed-tools`) with full constraints.
  - `name`: 1–64 chars, lowercase ASCII + hyphens only, no leading/trailing hyphens, no consecutive hyphens, **must match parent directory name** (the silent install-rejection trap).
  - `description`: 1–1024 chars (hard limit; installer rejects with `field 'description' in SKILL.md must be at most 1024 characters`).
  - `compatibility`: 1–500 chars.
  - `metadata`: optional mapping, keep keys unique to avoid conflicts.
  - `allowed-tools`: optional, space-separated, experimental.
- **File-reference-depth guidance** added — keep file references one level deep from `SKILL.md`, per the spec.
- **Validation pointer** added — references both the bundled `scripts/validate_frontmatter.py` and the upstream `skills-ref` validator from <https://github.com/agentskills/agentskills/tree/main/skills-ref>.

### Removed

- **Three inline `python -c` one-liners** removed from `SKILL.md` and `references/description-optimization.md`. These violated the spec's [bundle-vs-inline guidance](https://agentskills.io/skill-creation/using-scripts) (*"Move complex commands into scripts"*) and burned tokens on every skill invocation. Replaced by single references to `scripts/validate_frontmatter.py`.
- **Verbose preamble and chatty rationale paragraphs** trimmed throughout `SKILL.md`. Substantive guidance preserved; conversational filler reduced.

### Fixed

- **The 1024-character `description` limit** is now documented prominently in `SKILL.md`. Upstream version did not mention the limit at all, causing silent install rejections when authors wrote "pushy" descriptions per the upstream guidance and exceeded the budget. (A companion PR is open at <https://github.com/anthropics/skills> to fix this upstream as well.)
- **The parent-directory match requirement on the `name` field** is now documented. Upstream version did not mention this constraint; renaming a skill's directory without updating the `name:` field would cause silent install rejections.

### Spec compliance status (1.1.0)

Verified against [agentskills.io specification](https://agentskills.io/specification) at the time of this release:

| Concern | Status |
|---|---|
| Frontmatter fields documented | All six fields, with full constraints |
| `SKILL.md` body within token budget | ~3,655 tokens (recommended <5,000) |
| Bundled scripts use PEP 723 inline metadata | `scripts/validate_frontmatter.py` does |
| Scripts follow agentic-use design guidance | `--help`, structured output, meaningful exit codes, no interactive prompts |
| File references one level deep from `SKILL.md` | All references in `references/` (depth 1) |
| Spec-drift check defined | `references/spec-check.md` + `references/spec-source-map.md` |
| Upstream validator recommended | `skills-ref validate ./skill-directory` |

Run `uv run scripts/validate_frontmatter.py` from the skill directory to verify these constraints on your local copy.

---

## [1.0.0] — 2026-05-20

Initial fork from `anthropics/skills` at `main`. No skill-level changes in this commit; this entry is provided as the baseline so future diffs can be tracked against a labeled version.

Upstream snapshot:
- `SKILL.md` ~487 lines / ~8,490 tokens
- No bundled frontmatter validator
- Frontmatter rules documented partially (no character limits, no name constraints beyond "Skill identifier")
- Test-running, description-optimization, and environment-specific content all inline in `SKILL.md`

---

## Versioning notes

This fork uses semantic versioning **for the `skill-creator` skill itself**, independent of upstream `anthropics/skills` (which doesn't version its skills).

- **MAJOR** — breaking changes to the SKILL.md structure that an existing skill author's workflow would need to adapt to.
- **MINOR** — new bundled scripts, new reference files, expanded frontmatter coverage, restructures that don't break existing workflows.
- **PATCH** — corrections, typo fixes, link updates, prose polish.

When upstream lands a meaningful change, this changelog will note "merged from upstream" with the upstream commit reference and a summary of what changed.
