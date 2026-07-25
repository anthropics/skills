---
name: markdown-html-orchestrator
description: Use when a user wants to convert any markdown file in their Claude project into a single-file, lightly-interactive HTML — long-form documents (specs, plans, RFCs, reports, explainers), code reviews with diffs and severity-tagged annotations, or slide decks. Triggers on "convert this markdown to HTML", "make this an HTML file", "turn this into an interactive document", "render this report as HTML", "PR writeup as HTML", "slides from this markdown". Forks context to route to one of three converter sub-skills (md-document, md-review, md-slides) based on a deterministic doctype classifier, after the user has run the design-system onboarding once. Refuses if input is under 100 lines (per Shihipar — markdown still wins below the threshold) or design-system isn't onboarded. Distinct from Anthropic's official Playground plugin (which is interactive prompt-tuning controls with sliders/knobs/prompt-copy-back) and from marketing/landing/ (which is a landing-page generator).
context: fork
version: 2.10.3
author: Alireza Rezvani
license: MIT
tags: [markdown, html, converter, orchestrator, documentation, code-review, slides, design-system]
compatible_tools: [claude-code, codex-cli, cursor, antigravity, opencode, gemini-cli]
---

# Markdown → HTML — Domain Orchestrator

Thariq Shihipar's argument (Claude Code HTML output essay, Medium 2026): **markdown collapses past 100 lines for agent-generated artifacts.** Long specs, code reviews, and architecture explainers lose density, hierarchy, and lightweight interaction the moment they exceed a screen of text. HTML restores all three — single-file, browser-native, shareable.

This orchestrator forks context, classifies the input markdown deterministically, routes to the right converter sub-skill, and returns a digest with the output path. Heavy intake (full markdown bodies, diffs, slide decks) stays in the forked context.

**Domain status (complete):** all five skills are live — orchestrator + `design-system` (onboarding + shared brand tokens) + the three converter sub-skills (`md-document`, `md-review`, `md-slides`). Always route conversions to the shipped converter's scripts; never hand-render HTML inline.

## When to invoke

| Symptom | Sub-skill |
|---|---|
| "Convert this RFC / spec / report / explainer to HTML" — long-form doc | `md-document` |
| "Turn this PR writeup / code review into HTML" — markdown with diff blocks | `md-review` |
| "Make a slide deck from this markdown" — `---` boundaries or H1 cadence | `md-slides` |

## Pre-flight gates (hard refusals)

1. **Below the 100-line threshold.** Markdown wins below 100 lines (Shihipar). The classifier prints `below_min_lines: true` and `route_explainer.py` refuses. Tell the user to keep their input as markdown.
2. **Design-system not onboarded.** If `~/.config/markdown-html/design-system.json` doesn't exist (or its `setup_completed_at` is null), refuse. Point the user at `python3 markdown-html/skills/design-system/scripts/onboard.py` (or `--defaults` for a zero-touch run).
3. **Unwritable save location.** `output_path_resolver.py` refuses if the configured `default_output_dir` (or `--out` override) isn't writable.

## Routing logic (deterministic)

Two-signal threshold pattern lifted from `research-ops/skills/research-ops-skills/SKILL.md`. Filename hint = 2 points; each content signal = 1 point. Silent-route allowed when winner ≥ 3 AND (runner-up = 0 OR winner ≥ 2× runner-up). Below threshold → one clarifying question with a recommended answer.

### Signal table

| Signal class | Filename hints | Content signals | Sub-skill |
|---|---|---|---|
| DOCUMENT | `report.md`, `*-doc.md`, `spec.md`, `rfc-*.md`, `*-analysis.md`, `*-explainer.md` | `## Table of Contents` (2), `^# `, `^## `, markdown table rows, `> [!NOTE]/[!TIP]/[!IMPORTANT]` callouts | `md-document` |
| REVIEW | `review.md`, `*-pr-*.md`, `*.diff.md`, `code-review*.md` | ` ```diff ` (2), `^[-+]{3} ` (2), `^@@` (2), `> [!BLOCKER]/[!MAJOR]/[!MINOR]/[!NIT]` (2), `LGTM`/`nit:`/`blocker:` | `md-review` |
| SLIDES | `deck.md`, `slides.md`, `*-talk.md`, `presentation*.md` | `^---$` ≥ 3 (2 + per-boundary), `<!-- notes:` (2), H1 count ≥ 5 with median gap ≤ 12 lines (2) | `md-slides` |

The pipeline:

```bash
python3 markdown-html/skills/markdown-html-orchestrator/scripts/doctype_classifier.py \
    --input <path>.md --output json \
  | python3 markdown-html/skills/markdown-html-orchestrator/scripts/route_explainer.py
```

`route_explainer.py` checks the design-system status, applies the < 100-line refusal, and prints one of: `ROUTE_SILENTLY -> md-<type>`, `ASK_USER one question: ...`, or `REFUSE — fix the issues above`.

## Workflow

### Step 1 — Confirm onboarding

If the user has never run onboarding, surface the one-time setup:

```bash
python3 markdown-html/skills/design-system/scripts/onboard.py
```

Ten questions, 1-2 minutes. Captures brand primary + accent + heading/body Google Fonts + design style (editorial/technical/minimal/playful) + default output dir + syntax theme + TOC behavior + optional logo/company. Stored at `~/.config/markdown-html/design-system.json`. Re-runnable with `--scope project` for per-repo overrides.

### Step 2 — Classify the input

Run `doctype_classifier.py` on the markdown. Inspect the verdict.

### Step 3 — Route or ask

Pipe the classification into `route_explainer.py`. If it says `ROUTE_SILENTLY`, forward the original markdown + the design-system config into the named sub-skill's renderer in the forked context. If it says `ASK_USER`, ask ONE question with the recommended answer.

### Step 4 — Resolve the output path

```bash
python3 markdown-html/skills/markdown-html-orchestrator/scripts/output_path_resolver.py \
    --input <path>.md --doctype <document|review|slides>
```

Collision handling defaults to `-2 / -3 / ...` suffix; `--on-collision timestamp` for stamped names.

### Step 5 — Hand off to the sub-skill

The routed converter sub-skill's renderer (`md-document/scripts/`, `md-review/scripts/`, or `md-slides/scripts/`) takes the input markdown, the design-system config, and the resolved output path, and writes a single self-contained HTML file. The orchestrator returns a ≤ 100-word digest: input lines, output path, design style applied, top 3 features used (TOC, search, code-copy, etc.), and one forcing question for the user. Never render HTML by hand — the converter scripts own the rendering.

## Forcing-question library (Matt Pocock grill-with-docs pattern)

Walk these one at a time, with a recommended answer per question, citing the canon. Lift this list into `/cs:grill-markdown-html` for plan-stage interrogation.

1. **What decision does this HTML drive — is the reader skimming, deciding, or presenting?**
   Recommended: name it first; density follows from purpose. Canon: Shihipar — "match output format to consumption context"; Tufte — *Visual Display of Quantitative Information*, ch. 1.
2. **Is the input markdown ≥ 100 lines?**
   Recommended: yes — below that, keep it as markdown. Canon: Shihipar — markdown still wins under 100 lines.
3. **Is the design-system onboarded?**
   Recommended: yes, globally (`~/.config/markdown-html/design-system.json`). Canon: research-ops onboarding pattern (`research-ops/CLAUDE.md` §8); WCAG 2.2 §1.4.3 (text contrast 4.5:1).
4. **Where does the output save, and will it overwrite anything?**
   Recommended: the configured `default_output_dir` with `--on-collision suffix`. Canon: Matt Pocock `handoff` skill — never silently overwrite a working artifact.
5. **Document type confidence — silent-route or one question?**
   Recommended: silent-route only when the classifier's verdict is one of `document/review/slides` AND `silent_route_allowed: true`. Otherwise ask. Canon: research-ops two-signal threshold (`research-ops/skills/research-ops-skills/SKILL.md` §"Routing logic").

Never run a sub-skill before the lane is locked.

## Assumptions

1. User has a markdown file ≥ 100 lines they want to convert.
2. User has run onboarding once (`~/.config/markdown-html/design-system.json` exists with `setup_completed_at` populated).
3. Single-file HTML output is acceptable (no multi-file site, no embedded server, no build step).
4. Externals limited to Google Fonts CSS + Prism.js CDN (jsdelivr / cdnjs).

## Non-goals

- Not a landing-page generator (use `marketing/landing/`).
- Not an interactive prompt-tuning playground (use Anthropic's official `playground` plugin).
- Not a static-site generator (no multi-file output, no site index).
- Not a PDF generator (slides use `@media print`; user prints from browser).
- Not a watch / live-reload pipeline (conversion is one-shot).

## Distinct from

- **Anthropic Playground plugin** (`/playground`) — builds interactive controls (sliders, knobs, drag-drop) for prompt tuning, with a copy-prompt-back loop. This plugin converts existing markdown documents to HTML. Different tools for different jobs.
- **`marketing/landing/`** — generates landing pages from scratch (Phase-0 intake → 3 sections → branded TSX/HTML). This plugin converts an existing markdown file you already have.
- **`engineering/handoff/` + `productivity/handoff/`** — preserve session continuity between Claude conversations. Different artifact type (handoff brief vs. document conversion).

## Output artifacts

| Sub-skill | Artifact | Status |
|---|---|---|
| `md-document` | `doc-<slug>.html` (single file, sticky TOC, collapsibles, search, code-copy, scrollspy) | ✓ live |
| `md-review` | `review-<slug>.html` (2-col diff + severity margin notes + jump-nav) | ✓ live |
| `md-slides` | `deck-<slug>.html` (arrow-key nav + presenter mode + print-to-PDF) | ✓ live |

## Anti-patterns (do not)

- ❌ Convert markdown < 100 lines — markdown still wins. Refuse and tell the user.
- ❌ Run the orchestrator before the design-system is onboarded. The output looks broken without tokens.
- ❌ Silently chain two sub-skills (e.g., "convert doc AND make slides from it"). Pick one, finish, ask before chaining.
- ❌ Use external JS frameworks (React/Vue/Svelte). Vanilla JS + IntersectionObserver only. Prism.js CDN is the single exception.
- ❌ Multi-file output (extracted CSS, asset directories). Single file or nothing — that's the whole point.
- ❌ Overwrite an existing output file by default. The path resolver suffixes `-2`, `-3`, …; `--on-collision overwrite` is opt-in only.

## References

- Spec: Thariq Shihipar — "Claude Code HTML output" (Medium, 2026)
- Forking pattern: `research-ops/skills/research-ops-skills/SKILL.md` (`context: fork`, two-signal routing)
- Customization pattern: `research-ops/skills/clinical-research/scripts/` (`onboard.py`, `config_loader.py`)
- Brand palette math: `marketing/landing/skills/landing/scripts/brand_palette_validator.py` (WCAG + HSL derive)
- Information-density canon: Tufte; Shihipar's `thariqs.github.io/html-effectiveness/` gallery; Wattenberger interactive essays; Maggie Appleton digital gardens
