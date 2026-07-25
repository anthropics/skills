---
name: md-document
description: Converts long-form markdown (specs, RFCs, reports, plans, explainers) into a single-file, lightly-interactive HTML document with sticky TOC, scrollspy, search filter, code-copy buttons, and design-system-driven brand tokens. Triggers when the markdown-html-orchestrator classifies an input as DOCUMENT, or when invoked directly via /cs:md-document. Reads the design-system config via config_loader.py and inlines the user's 12 derived CSS custom properties; refuses to render if onboarding hasn't run. Single-file output — Google Fonts + Prism.js CDN are the only externals; no framework runtime, no build step. Use after orchestrator routing or after design-system onboarding is confirmed.
version: 2.10.1
author: Alireza Rezvani
license: MIT
tags: [markdown, html, documentation, single-file, toc, scrollspy, search, code-copy, design-system]
compatible_tools: [claude-code, codex-cli, cursor, antigravity, opencode, gemini-cli]
---

# md-document — Long-form Markdown to HTML

The general-purpose converter — handles the 90% case Shihipar describes (specs, plans, RFCs, reports, explainers). Three stdlib tools pipeline together:

```
markdown_parser.py  →  html_renderer.py  →  interactivity_injector.py
   (md → JSON AST)    (AST + tokens → HTML)    (HTML + JS behavior)
```

Output is one `.html` file with sticky TOC, search filter, scrollspy, code-copy buttons, and the user's 12 derived brand tokens. Externals limited to Google Fonts CSS + Prism.js CDN.

## When to invoke

| Symptom | Action |
|---|---|
| `markdown-html-orchestrator` routes input as DOCUMENT | Invoke this skill |
| User runs `/cs:md-document <path>.md` directly | Invoke this skill |
| User says "convert this spec/report/RFC/plan to HTML" | Invoke this skill |
| Input is a code review (has ` ```diff ` blocks) | Route to `md-review` instead |
| Input is a slide deck (clear `---` boundaries) | Route to `md-slides` instead |
| Input is < 100 lines | Refuse (Shihipar threshold — markdown still wins) |
| Design-system not onboarded | Refuse, surface `/cs:design-system` |

## Pipeline

```bash
# 1. Parse markdown → JSON AST
python3 markdown-html/skills/md-document/scripts/markdown_parser.py \
    --input <path>.md --output sections.json

# 2. Render AST + design-system config → single-file HTML
python3 markdown-html/skills/md-document/scripts/html_renderer.py \
    --sections sections.json --output document.html

# 3. Inject lightweight JS (search, copycode, smoothscroll, scrollspy)
python3 markdown-html/skills/md-document/scripts/interactivity_injector.py \
    --file document.html \
    --features search,copycode,smoothscroll,scrollspy
```

Or all-in-one (sample render):

```bash
python3 markdown-html/skills/md-document/scripts/html_renderer.py --sample \
  | python3 markdown-html/skills/md-document/scripts/interactivity_injector.py \
      --file /dev/stdin --output document.html
```

## What gets rendered

CommonMark subset sufficient for agent-generated artifacts:
- Headings H1-H6 (every H2+ gets an anchor id and TOC entry)
- Paragraphs with inline **bold** / *italic* / `code` / [links](url) / ![images](url)
- Fenced code blocks (` ```python `) with Prism.js highlighting on demand
- GFM tables with per-column alignment
- GFM callouts (`> [!NOTE]`, `> [!TIP]`, `> [!IMPORTANT]`, `> [!WARNING]`, `> [!CAUTION]`)
- Blockquotes, ordered + unordered lists (single-level), horizontal rules

Out of scope: nested lists, HTML inlines, footnotes, definition lists, task list checkboxes (rendered as plain text), reference-style links.

## Hard rules

1. **Refuses input < 100 lines.** Markdown wins below the threshold (Shihipar).
2. **Refuses without onboarding.** `config_loader.setup_completed()` must return `True`. Otherwise surface `/cs:design-system`.
3. **Single-file output.** All CSS + JS inline. Only externals are `fonts.googleapis.com` and `cdn.jsdelivr.net` (Prism). Anything else is a regression.
4. **Customization must change behavior.** `design_style=editorial` produces 720px-wide layout with 1.75 line-height; `playful` rounds the callouts and adds shadow; `technical` is dense with 0.875rem code. Smoke-tested.
5. **WCAG-compliant tokens.** Inherits the design-system's WCAG AA palette — body text ≥ 4.5:1 contrast, links iteratively walked to 4.5:1.
6. **Idempotent injection.** Re-injecting interactivity is a no-op (marker check). Re-rendering with a different design_style works cleanly.

## Forcing-question library (Matt Pocock grill discipline)

1. **What's the document for — skim, decide, or deep-read?** Recommended: name it; density follows. Canon: Shihipar; Tufte *Envisioning Information*.
2. **Sticky-sidebar TOC or collapsible-top?** Recommended: sticky-sidebar for > 800 words / 4+ H2s; collapsible-top for shorter mobile-first docs. Canon: NN/g *TOC Best Practices* (2023).
3. **All four interactive features, or a subset?** Recommended: all four — none of them cost more than ~1 KB. Canon: Wattenberger *Why React isn't great for actually building websites*.
4. **Code theme — light, dark, or auto?** Recommended: auto (follows OS `prefers-color-scheme`). Canon: WCAG 2.2 §1.4.3.
5. **Does the document have a clear H1 title?** Recommended: yes — H1 becomes the page `<title>` and is excluded from the TOC.

## Distinct from

- **`md-review`** — that converter renders diff blocks + severity-tagged margin annotations. This one renders prose + tables + code + callouts.
- **`md-slides`** — that converter splits on `---` boundaries into slides. This one renders one continuous document.
- **`marketing/landing/`** — that generates landing pages from scratch (no markdown input). This converts existing markdown.

## Output artifact

`{default_output_dir}/doc-{slug}.html` (path resolved by orchestrator's `output_path_resolver.py`; collision suffix `-2`, `-3`, … by default).

## References

- Shihipar — *Claude Code HTML output* (Medium, 2026)
- Tufte — *Envisioning Information* (1990), ch. 2 "Micro/Macro Readings"
- NN/g — *Table of Contents Best Practices* (2023)
- WCAG 2.2 — §1.4.3 contrast, §2.4.5 multiple ways
- Wattenberger — *Why React isn't great for actually building websites*
- See `references/` for full citations
