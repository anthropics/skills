---
name: md-slides
description: Converts a markdown deck (slides separated by `---` HR boundaries or by `# ` H1 headings, with optional `<!-- notes: ... -->` presenter notes blocks) into a single-file HTML presentation with arrow-key / space / PgDn / PgUp / Home / End / P / Esc keyboard navigation, presenter mode (split view with current slide + speaker notes + clock + next-slide preview), URL-hash deep linking, and `@media print` page-per-slide for PDF export. Triggers when the markdown-html-orchestrator classifies an input as SLIDES, or when invoked directly via /cs:md-slides. Reuses md-document's markdown parser for slide-body rendering and reads design-system tokens via config_loader.py. Refuses if input has no clear slide boundaries, produces a 1-slide deck, or `--strict-notes` is on with < 50% notes coverage. Use after orchestrator routing.
version: 2.10.3
author: Alireza Rezvani
license: MIT
tags: [markdown, html, slides, deck, presenter-mode, keyboard-nav, print-to-pdf, single-file, design-system]
compatible_tools: [claude-code, codex-cli, cursor, antigravity, opencode, gemini-cli]
---

# md-slides — Markdown deck → single-file HTML presentation

The slide-deck converter. Reads a markdown deck (HR or H1 boundaries, optional presenter notes), emits a single-file HTML presentation that runs in any browser with keyboard navigation, presenter mode, and print-to-PDF.

Three stdlib tools pipeline together:

```
slide_splitter.py  →  presenter_notes_parser.py  →  deck_html_renderer.py
   (md → ordered      (extract <!-- notes:         (slides + design-system
    slides with       --> blocks, attach            tokens → single-file
    titles)           per slide)                    HTML with keyboard nav)
```

## When to invoke

| Symptom | Action |
|---|---|
| `markdown-html-orchestrator` routes input as SLIDES | Invoke this skill |
| User runs `/cs:md-slides <path>.md` directly | Invoke this skill |
| Input has 3+ `---` HR lines OR 5+ H1 headings with short bodies | Invoke this skill |
| Input is a long-form spec | Route to `md-document` instead |
| Input is a code review | Route to `md-review` instead |
| Input has no clear slide boundaries | Refuse, route to `md-document` |
| Input would produce 1 slide | Refuse (it's a poster) |

## Pipeline

```bash
# 1. Split slides on --- or H1 (auto-detect by default)
python3 markdown-html/skills/md-slides/scripts/slide_splitter.py \
    --input <path>.md --output /tmp/slides.json

# 2. Extract <!-- notes: ... --> blocks from each slide
python3 markdown-html/skills/md-slides/scripts/presenter_notes_parser.py \
    --slides /tmp/slides.json --output /tmp/deck.json

# 3. Render single-file HTML deck
python3 markdown-html/skills/md-slides/scripts/deck_html_renderer.py \
    --slides /tmp/deck.json --title "My Talk" --output deck.html
```

## What ships in the HTML

- **All slides as `<section class="slide">`** — one visible at a time, controlled by JS
- **Keyboard nav** — `→` / `Space` / `PgDn` advance; `←` / `PgUp` previous; `Home`/`End` jump; `P` presenter mode; `Esc` exits presenter
- **URL-hash deep linking** — `#3` jumps to slide 3; browser back/forward walks slides; share `deck.html#5` to send someone directly there
- **Progress bar** — 3px at top showing position through the deck
- **Slide counter** — bottom-right ("3 / 12")
- **Presenter mode** (P key) — splits the window: current slide on left (60% width), panel on right with clock + speaker notes + next-slide preview
- **Print stylesheet** — `Cmd+P` produces a PDF with one slide per page
- **`@media (prefers-reduced-motion: reduce)`** honored
- **12 brand CSS custom properties** from design-system; design_style affects layout density
- **Reuses md-document's markdown parser** — slide bodies render with consistent paragraph/list/code/table/callout handling

## Hard rules

1. **Refuses input with no clear slide boundaries.** Auto mode needs ≥ 3 HR lines or ≥ 5 H1 headings. Otherwise exit 6 — route to md-document.
2. **Refuses 1-slide decks.** That's a poster, not a deck. Exit 5.
3. **Refuses input < 100 lines.** Same Shihipar threshold as all converters.
4. **Refuses without onboarding.** Same gate as every converter.
5. **`--strict-notes` refuses < 50% notes coverage.** A deck where most slides have no notes isn't set up for presenter mode. Exit 7.
6. **Soft-warns slides > 40 source lines.** Signal-to-noise; renders anyway but surfaces the count.
7. **Single-file output.** All CSS + JS inline. Only external is Google Fonts CSS. Prism.js is opt-in via `--syntax`.
8. **No JS framework runtime.** Vanilla JS + keyboard event handlers, no React/Vue/Svelte.

## Forcing-question library (Matt Pocock grill discipline)

1. **Is this actually a deck, or a long document?** Recommended: if you can't draw clear slide boundaries, it's not a deck. Canon: Tufte *Cognitive Style of PowerPoint*.
2. **HR (`---`) or H1 boundaries?** Recommended: HR for typical decks; H1 for outline-driven decks. Canon: Marp / reveal.js / pandoc convergence.
3. **Will it be presented live or distributed for self-paced reading?** Recommended: live → need presenter notes; self-paced → notes optional. Canon: Weinschenk *100 Things Every Presenter Needs to Know*.
4. **Is there any slide over 40 source lines?** Recommended: split it. Canon: NN/g — audience attention drops past ~6 bullets / 200 words.
5. **Is `--syntax` needed?** Recommended: only for decks with substantial code blocks. Default off. Canon: single-file shareability discipline.

## Distinct from

- **`md-document`** — that's one continuous document. This is N discrete slides.
- **`md-review`** — that renders diff hunks + annotations. This renders prose slides.
- **`marketing/landing/`** — that's a landing page, not a deck.
- **Keynote / PowerPoint** — those are graphic-design tools. This is for markdown-authored decks projected from a browser.

## Output artifact

`{default_output_dir}/deck-{slug}.html` (path resolved by orchestrator's `output_path_resolver.py`; collision suffix `-2`, `-3`, … by default).

## References

- Shihipar — *Claude Code HTML output* (Medium, 2026), Tier 3 use case "Slide Decks"
- Reynolds — *Presentation Zen* (less is more discipline)
- Atkinson — *Beyond Bullet Points* (the bullet-heavy failure mode)
- Tufte — *The Cognitive Style of PowerPoint* (the polemic)
- reveal.js / Big / Marp — convergent markdown-to-deck conventions
- See `references/` for full citations (presentation_ux, keyboard_nav_patterns, single_file_deck_conventions)
