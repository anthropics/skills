---
name: design-system
description: Captures the user's brand identity once via a 10-question onboarding wizard (primary/accent HEX + heading + body Google Fonts + design style editorial/technical/minimal/playful + default output directory + syntax theme + TOC behavior + optional logo/company), validates body-text and link contrast against WCAG 2.2 AA, derives 12 CSS custom properties in HSL space, and stores the result for every markdown-html converter to consume. Use before any markdown-html conversion. Triggers on first-run onboarding ("set up the brand", "configure markdown-html", "run onboarding"), on explicit reset ("reset the design system", "re-onboard"), and is checked by every converter via config_loader.py before rendering. Refuses to save if body-text contrast fails AA 4.5:1 or the output dir isn't writable. Precedence: project (./.markdown-html/) > global (~/.config/markdown-html/) > built-in defaults; MARKDOWN_HTML_NO_CONFIG=1 bypasses.
version: 2.10.0
author: Alireza Rezvani
license: MIT
tags: [design-system, brand-palette, wcag, onboarding, customization, markdown-html, css-variables, typography]
compatible_tools: [claude-code, codex-cli, cursor, antigravity, opencode, gemini-cli]
---

# Design System — Onboarding + Shared Brand Tokens

The design-system skill is the **shared brand owner** for the markdown-html plugin. Run its onboarding once. Every converter (`md-document`, `md-review`, `md-slides`) reads the resulting config via `config_loader.py` and applies the same 12 CSS custom properties to its output. Without this, conversions render with placeholder defaults — technically functional but unbranded.

This skill ships exactly three Python tools:

1. **`onboard.py`** — interactive (or `--defaults` / `--set` / `--show` / `--reset`) wizard.
2. **`config_loader.py`** — importable customization loader with project > global > defaults precedence and `MARKDOWN_HTML_NO_CONFIG=1` bypass.
3. **`brand_palette_validator.py`** — WCAG-AA contrast checker + HSL palette deriver.

All three are stdlib-only and contain no LLM calls (deterministic per Path-B discipline).

## When to invoke

| Symptom | Action |
|---|---|
| User says "convert this markdown to HTML" for the first time in this workspace | Run `python3 markdown-html/skills/design-system/scripts/onboard.py` |
| `~/.config/markdown-html/design-system.json` doesn't exist OR `setup_completed_at` is null | Refuse conversion, surface onboarding |
| User wants per-repo brand override | `python3 .../onboard.py --scope project` |
| User wants to change a single field non-interactively | `python3 .../onboard.py --set brand.primary=#FF6B35` |
| User wants to reset and re-onboard | `python3 .../onboard.py --reset` then re-run |
| User wants zero-touch defaults (CI, ephemeral session) | `python3 .../onboard.py --defaults` |
| Headless / containerized run that should ignore saved config | `MARKDOWN_HTML_NO_CONFIG=1 ...` |

## Onboarding question set (10 questions)

| # | Key | Choices / Validator | Default |
|---|---|---|---|
| 1 | `default_output_dir` | path; `os.access(parent, os.W_OK)` | `./markdown-html-out/` |
| 2 | `brand.primary` | HEX `^#?[0-9a-fA-F]{6}$` | `#0A1628` |
| 3 | `brand.accent` | HEX or blank (auto-derive) | derive from primary |
| 4 | `typography.heading_font` | Google Font name (12 safe defaults) | `Inter` |
| 5 | `typography.body_font` | Google Font name | `Inter` |
| 6 | `design_style` | `editorial / technical / minimal / playful` | `technical` |
| 7 | `code_theme` | `light / dark / auto` | `auto` |
| 8 | `toc.behavior` | `sticky-sidebar / collapsible-top / inline / none` | `sticky-sidebar` |
| 9 | `company_name` | string (may be empty) | `""` |
| 10 | `logo_url` | URL or empty (base64-embedded at render) | `""` |

## Hard rules

1. **WCAG AA body-text contrast must pass.** `brand_palette_validator.validate()` runs after every change. Body text on bg must reach 4.5:1; link on bg must reach 4.5:1. If either fails, `onboard.py` refuses to save (exit code 4) and tells the user to pick a darker primary, blank `brand.bg`/`brand.text` to let derivation pick a safe pair, or override `brand.text` directly. Canon: WCAG 2.2 §1.4.3.
2. **Output directory must be writable.** `onboard.py` walks up the path to find an existing ancestor and checks `os.W_OK`. Empty or unwritable path → exit code 3. The orchestrator's `output_path_resolver.py` honors the same rule per-conversion.
3. **Customization must change behavior, not sit as decoration.** Every consumer (md-document, md-review, md-slides) must read the config and render differently when the user changes `design_style`, `brand.primary`, `code_theme`, or `toc.behavior`. Decorative-only fields fail the design discipline.
4. **Precedence is fixed.** Project > global > defaults. The deep-merge preserves nested keys (e.g. you can override `brand.primary` in a project config without losing `typography.heading_font` from global).
5. **Bypass env exists for a reason.** `MARKDOWN_HTML_NO_CONFIG=1` is for headless CI, ephemeral test containers, and the autoresearch-style evaluator loops. Never set it silently for an interactive user.

## Derived 12-token palette

Once the user's brand is captured, `brand_palette_validator.derive_palette()` produces 12 CSS custom properties stored under `derived_palette` in the same config file. Every converter inlines these into its `<style>` block.

| Token | Purpose | Derivation |
|---|---|---|
| `--md-bg` | Document background | Primary if dark, near-neutral if vibrant |
| `--md-surface` | Card / callout / blockquote background | Bg ± 4-6% luminance |
| `--md-border` | Hairline dividers, table borders | Bg ± 8-12% luminance |
| `--md-text` | Body text | Off-white on dark bg, near-black on light bg |
| `--md-text-muted` | Captions, metadata, footers | `rgba(text, 0.68)` |
| `--md-accent` | Primary CTA, callout headers, link emphasis | Primary if vibrant, hue-shifted lighter if dark |
| `--md-accent-soft` | Accent backgrounds, hover states | `rgba(accent, 0.14)` |
| `--md-code-bg` | Inline code, fenced block bg | Bg ± 4-5% luminance |
| `--md-link` | Hyperlinks | Iteratively walked to reach 4.5:1 contrast on bg |
| `--md-link-hover` | Hover state | Link ± 6-8% luminance |
| `--md-success` | OK / approved / passed | Green anchored, luminance-matched |
| `--md-warn` | Caution / nit / TODO | Amber anchored, luminance-matched |

## Forcing-question library (Matt Pocock grill-with-docs pattern)

One question per turn, recommended answer, canon citation.

1. **What's your brand primary color?** Recommended: a HEX you already use in your product or docs — not a stock blue. Canon: Aarron Walter, *Designing for Emotion* (color carries brand affect).
2. **Should accent be derived or set?** Recommended: derive on first run (hue-shift + lighten produces a coherent companion); set explicitly only if your brand kit specifies one. Canon: Adobe Spectrum, *Color Foundations*.
3. **Editorial, technical, minimal, or playful?** Recommended: `technical` for engineering specs/reports, `editorial` for long-read narratives, `minimal` for sparse reference docs, `playful` for marketing/landing content. Canon: Ellen Lupton, *Thinking with Type* (style serves the rhetorical purpose).
4. **Sticky-sidebar TOC, or inline?** Recommended: `sticky-sidebar` for documents over 800 words, `inline` for short reads. Canon: Nielsen-Norman, *Table of Contents Best Practices* (2023).
5. **Save to global or per-project?** Recommended: global by default (consistent across your work); use `--scope project` only when this repo has a different brand. Canon: research-ops onboarding pattern, `research-ops/CLAUDE.md` §8.

## Customization in use (worked example)

```bash
# First-run onboarding (interactive, walks all 10 questions)
python3 markdown-html/skills/design-system/scripts/onboard.py

# Zero-touch defaults for CI / first-test
python3 .../onboard.py --defaults

# Change just the primary color and design style
python3 .../onboard.py --set brand.primary=#FF6B35 --set design_style=editorial

# Per-repo override
python3 .../onboard.py --scope project --set design_style=minimal

# Reset and re-onboard
python3 .../onboard.py --reset
python3 .../onboard.py

# Inspect the effective config (project > global > defaults)
python3 .../config_loader.py --show
python3 .../config_loader.py --status

# Bypass saved config (returns DEFAULTS only)
MARKDOWN_HTML_NO_CONFIG=1 python3 .../config_loader.py --show

# Spot-check WCAG contrast before committing to a brand
python3 .../brand_palette_validator.py --primary "#FF6B35" --accent "#00D4AA"
```

## Assumptions

1. User has at least one brand HEX they want consistent across their HTML conversions.
2. User accepts a 1-2 minute one-time setup.
3. User is OK with Google Fonts as the typography source (CDN, no local font hosting).
4. WCAG 2.2 AA is the accessibility floor (4.5:1 body, 3:1 large/UI). AAA (7:1) is out of scope.

## Non-goals

- Not a full design-token system (Style Dictionary, Theo). Twelve tokens, not a hundred.
- Not a custom-font hosting solution. Google Fonts only.
- Not a dark/light mode switcher in the converters. `code_theme: auto` handles the prefers-color-scheme case for syntax highlighting; layout palette is single-mode per onboarding.
- Not an accessibility audit suite (use axe-core / pa11y for that). We enforce contrast only.
- Does not transform existing CSS — the derived palette is injected into freshly generated HTML.

## Distinct from

- **`marketing/landing/skills/landing/scripts/brand_palette_validator.py`** — that script's `derive_palette()` produces 8 tokens shaped for hero-page rendering (`--navy`, `--teal`, `--card-bg`, `--card-border`). This script produces 12 tokens shaped for document rendering (sticky surface, hairline border, code bg, link, link-hover, success, warn). Same WCAG + HSL math, different token taxonomy.
- **`research-ops/skills/clinical-research/scripts/onboard.py`** — same pattern (interactive + `--defaults`/`--set`/`--show`/`--reset`/`--scope`), different question set (clinical alpha/power/dropout vs. brand palette/typography/layout).

## Output artifact

`~/.config/markdown-html/design-system.json` (global) or `./.markdown-html/design-system.json` (project). JSON schema lives at `assets/design_system_schema.json`.

## Anti-patterns (do not)

- ❌ Skip onboarding and run a converter with placeholder defaults — output looks unbranded.
- ❌ Pick a vibrant brand primary as `brand.bg` directly (low text contrast). Use it as accent instead.
- ❌ Set `MARKDOWN_HTML_NO_CONFIG=1` silently for an interactive user — they'll wonder why their tokens disappeared.
- ❌ Encode brand semantics in `derived_palette` outside the 12-token taxonomy. Add a new token only with a deliberate name + purpose + derivation rule.

## References

- WCAG 2.2 — §1.4.3 (contrast), §1.4.4 (resize), §1.4.11 (non-text contrast)
- Aarron Walter — *Designing for Emotion* (A Book Apart)
- Ellen Lupton — *Thinking with Type*
- Adobe Spectrum — *Color Foundations*
- Nielsen-Norman — *Table of Contents Best Practices* (2023)
- research-ops onboarding pattern: `research-ops/CLAUDE.md` §8
- Brand palette math source: `marketing/landing/skills/landing/scripts/brand_palette_validator.py`
