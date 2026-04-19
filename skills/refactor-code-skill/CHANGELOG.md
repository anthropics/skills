# Changelog

All notable changes to this skill are documented here.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

<!--
Add entries here as you make changes. When you release, move everything from
Unreleased into a new `## [X.Y.Z] — YYYY-MM-DD` block.

Categories (in this order, omit empty ones):
  ### Added       — new features, new skills, new references
  ### Changed     — changes to existing behavior
  ### Deprecated  — soon-to-be removed features
  ### Removed     — removed features
  ### Fixed       — bug fixes
  ### Security    — security-relevant changes

Version bump rules:
  MAJOR (X.0.0) — breaking changes to skill output or install interface
  MINOR (1.X.0) — new capability, new language support, new reference catalog
  PATCH (1.0.X) — wording tweaks, typo fixes, doc-only changes, improved
                  triggering without behavior change

Remember to update the `version` field in BOTH
  .claude-plugin/marketplace.json   (the plugin entry's version)
  plugins/refactor-code/.claude-plugin/plugin.json
so they stay in sync. The plugin.json version wins silently when they drift.
-->

## [1.0.0] — 2026-04-19

### Added

- Initial release of the `refactor-code` skill.
- `SKILL.md` with workflow, output contract, quick-reference tables mapping smells to refactorings and patterns, SOLID cross-cutting guidance, anti-patterns, and worked examples.
- `references/code-smells.md` — Martin Fowler's 22 code smells organized into the five families (Bloaters, Object-Orientation Abusers, Change Preventers, Dispensables, Couplers) with diagnostic cues.
- `references/refactoring-techniques.md` — the full Fowler catalog organized into six technique families (Composing Methods, Moving Features, Organizing Data, Simplifying Conditionals, Simplifying Method Calls, Dealing with Generalization).
- `references/design-patterns.md` — the 23 Gang of Four design patterns with intent, applicability cues, and language-specific notes.
- `references/linting-by-language.md` — cross-check rules for JS/TS, Python, Go, C/C++, Java, C#, Ruby, PHP, and Rust, covering the key linters (ESLint, ruff, clang-tidy, golangci-lint, etc.) without requiring execution.
- `evals/evals.json` plus three input samples covering Strategy-pattern extraction, nested-conditional refactoring with dataclasses, and React component decomposition.
- Claude Code plugin marketplace structure (`.claude-plugin/marketplace.json` + `plugins/refactor-code/.claude-plugin/plugin.json`) for one-command install via `/plugin install`.
- Cross-platform install documentation in the README for Claude.ai, ChatGPT, Codex CLI, Gemini CLI, Cursor, the Vercel `skills` CLI, and Ollama-via-agent-framework.
- MIT LICENSE.
- GitHub Actions workflow and `scripts/validate.py` for automated manifest and skill validation on every push and PR.

[Unreleased]: https://github.com/scarlett-danger/refactor-code-skill/compare/v1.0.0...HEAD
[1.0.0]: https://github.com/scarlett-danger/refactor-code-skill/releases/tag/v1.0.0
