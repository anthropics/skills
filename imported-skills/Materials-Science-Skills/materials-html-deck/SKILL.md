---
name: materials-html-deck
version: "3.0.0"
stability: beta
description: Use when generating browser-native HTML academic decks from materials science papers, notes, figures, data, or slide outlines.
---

# Materials HTML Deck

Generate high-fidelity HTML academic decks for materials research. The deck is
the source, preview, and delivery artifact: `index.html`, independent
`slides/*.html`, shared style tokens, screenshots, QA reports, speaker notes,
and an asset manifest.

## When to use

- Turn a paper, reading notes, data package, or JSON outline into a group
  meeting, journal-club, seminar, thesis, or project-report HTML academic deck.
- Build figure-centered materials slides with captions, source labels, evidence
  boundaries, and speaker notes.
- Produce browser-native decks where visual quality matters more than Office
  editability.

## When not to use

- If you only need a static scientific figure, use `materials-figure`.
- If you need manuscript prose, use `materials-writing`.
- If the user needs an Office or document export, treat that as a separate
  workflow outside this skill.

## Architecture

- **Static layer** under `static/` holds principles, toolchain policy, workflow,
  output rules, paper-type arcs, and task instructions.
- **Dynamic layer** detects `deck_type`, `paper_type`, `task`,
  `output_format`, `verification_level`, `academic_style`, `source_type`,
  `domain`, `material_family`, and `template`, then loads only the fragments
  needed for the current job.
- **Tool layer** under `scripts/` generates independent 1920x1080 HTML slides,
  an iframe-based `index.html`, shared CSS tokens, screenshots, QA reports, and
  an asset manifest.

## Protocol

1. Read [manifest.yaml](manifest.yaml), then load every `always_load` file.
2. Apply profile-first routing from `.materials/profile.yaml`.
3. Detect axes and load matching fragments.
4. Choose the path:
   - **Fast path**: user provides a JSON outline; run `scripts/build_deck.mjs`
     to generate the retained HTML deck and strict Playwright QA.
   - **Full path**: user provides a paper, text, notes, or data package;
     extract source material, classify paper type, plan the story, select and
     crop figures, write slide-by-slide content, then use the same HTML build
     path.
5. Select one curated `academic_style`: `assertion-evidence`,
   `dense-research`, `diagrammatic-minimalism`, `diagram-driven-isotype`,
   `two-font-consulting`, or `bento-grid`. Use `assertion-evidence` unless the
   content clearly calls for another style.
6. Run strict Playwright verification on every slide. If Playwright is missing,
   generation must fail with install instructions.
7. Deliver the HTML deck directory plus screenshots, speaker notes, QA report,
   and asset manifest.

## Evidence contract

- Keep every claim tied to a figure, table, test, or source paper.
- One main message per slide.
- Use Chinese slide titles by default, English only when explicitly requested.
- Do not crop away data labels, axes, legends, or scale bars.
- Separate measured results from inferred mechanisms.
- Do not fabricate numbers, figure details, or unsupported implications.
- Run at least one self-review pass before delivery.

## Toolchain notes

- `scripts/build_deck.mjs` is the default generator. It writes the HTML deck and
  invokes `scripts/verify_deck_html.mjs`.
- `scripts/verify_deck_html.mjs` checks page errors, console errors, missing
  local media, hidden/blank slides, and screenshot creation for every slide.
- `scripts/extract_figures.py` remains available for paper figure extraction
  before deck construction.
- The deck architecture and style grammar are influenced by attributed
  `huashu-design` references, but the public skill package does not require or
  ship a local vendored checkout.
