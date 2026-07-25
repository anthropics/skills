# Information Density Patterns for Long-form Documents

**Why this exists:** The `md-document` converter renders long-form markdown (specs, RFCs, reports, explainers) — typically 100-2000 lines of prose, code, tables, and callouts. Past 100 lines the linear flow loses orientation. This document codifies the patterns that restore it.

## The four density patterns

### 1. Hierarchy made visible

Linear markdown shows hierarchy through indented `#` characters. HTML shows hierarchy through typography scale, color, weight, spacing, and surface. The renderer uses a modular type scale (`typography.scale_ratio`, default 1.25 = major third) so each heading level is visibly proportional. H2 sections get a hairline `border-bottom` for visual chunking. Callouts get a 4px accent border that signals "stop and read."

### 2. Lateral navigation

Linear reading is one channel — top to bottom. The renderer adds:
- **Sticky-sidebar TOC** (default) — always visible, jumps to any H2/H3 in one click.
- **Scrollspy** — the current section's TOC entry gets `aria-current="location"` as the reader scrolls, so they always know where they are.
- **Anchored headings** — every H2-H6 gets an `id` derived from the heading text, so deep links work without further effort.
- **Smooth scroll** — TOC clicks animate, not jump, so the reader keeps spatial context.

### 3. Lateral structure

Side-by-side comparison is impossible in linear markdown. HTML provides:
- **Tables** — rendered with `<table>`, semantic `<thead>/<tbody>`, per-column alignment from the GFM delimiter row.
- **Collapsible sections** — `<details>` blocks for content the reader can skip on first pass. (TOC variant `collapsible-top` uses this for the TOC itself.)
- **Callouts** — `<aside class="callout">` for NOTE/TIP/IMPORTANT/WARNING/CAUTION. Distinct from paragraphs because they interrupt flow with intent.

### 4. Lateral interaction

Lightweight, no-framework:
- **Search filter** — `<input type="search">` filters H2 sections by heading + body text. Vanilla JS, no debouncing needed because typical documents have under 30 H2 sections.
- **Code-copy buttons** — appear on hover over `<pre>`, copy the entire `<code>` text. `navigator.clipboard` with `document.execCommand` fallback.
- **Smooth scroll** — already covered above.

## What's deliberately excluded

- **Slider/knob controls** — that's Anthropic's official Playground plugin's lane.
- **Real-time collaboration** — documents are read artifacts, not edit surfaces.
- **Multi-page navigation** — single-file is the discipline (see `single_file_html_discipline.md`).
- **Dark mode toggle** — the user picked `code_theme` once; switching mid-document violates the shipped-as-onboarded contract. (`code_theme: auto` does follow `prefers-color-scheme` for syntax highlighting.)

## Sources

### 1. Thariq Shihipar — "Claude Code HTML output" (Medium, 2026)
The spec. Five advantages mapped here: density, clarity, shareability, two-way interaction, context ingestion. The four-pattern taxonomy above is the implementation answer.

### 2. Edward Tufte — *Envisioning Information* (Graphics Press, 1990)
Ch. 2, "Micro/Macro Readings" — argues that effective information design lets the reader move between overview (TOC) and detail (paragraph) without losing context. The scrollspy + sticky TOC implements this micro/macro discipline for documents.

### 3. Amelia Wattenberger — *Why React isn't great for actually building websites* (wattenberger.com, 2022) + interactive essay archive
Argues that documents are not apps; framework runtimes are overhead. Validates the vanilla-JS + IntersectionObserver implementation choice.

### 4. Jakob Nielsen / NN/g — *How Users Read on the Web* (1997, updated 2024)
Establishes the F-shaped reading pattern: users scan headings + first sentences. The sticky-sidebar TOC + bold heading typography + H2 hairline border-bottom optimize for this pattern.

### 5. Maggie Appleton — *Digital Gardens* (maggieappleton.com, 2020)
The single-page-document-with-lightweight-interactivity pattern at scale. Her own gardens use exactly the techniques this converter emits.

### 6. Bartosz Ciechanowski — interactive essay archive (ciechanow.ski, 2017-present)
The upper bound of what vanilla-JS + inline SVG can produce in a single HTML file. Demonstrates that "lightweight" doesn't mean "low-quality."

### 7. Bret Victor — "Up and Down the Ladder of Abstraction" (worrydream.com, 2011)
Argues for letting the reader move fluidly between concrete and abstract. The TOC (abstract) + section detail (concrete) + scrollspy (the link between them) is the documents-shaped implementation.

## Applied to `md-document`

The converter emits exactly these patterns. `markdown_parser.py` extracts the structure; `html_renderer.py` renders it with the design-system tokens; `interactivity_injector.py` adds the four interactive behaviors. None of these need a JS framework or a build step.
