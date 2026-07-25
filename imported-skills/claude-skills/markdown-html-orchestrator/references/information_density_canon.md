# Information Density Canon

**Why this exists:** Thariq Shihipar's central claim is empirical: markdown collapses past ~100 lines because it lacks the visual machinery to manage density. This document anchors that claim in a longer tradition — from Edward Tufte's *Visual Display* to Maggie Appleton's digital gardens — so the orchestrator can defend the 100-line threshold against pushback ("why not 50?", "why not 200?") with cited evidence rather than vibes.

## Core claim

A reader skimming linear markdown loses orientation after roughly 5-7 screens. HTML restores orientation through:
1. **Hierarchy made visible** — typography scale, color, weight, indent, surface
2. **Lateral navigation** — TOC, scrollspy, anchored sections
3. **Lateral structure** — tables, grids, side-by-side comparisons
4. **Lateral interaction** — collapsibles, search, code-copy, hover state

Markdown collapses each of these into the same channel: indented text. HTML opens each into its own channel.

## Sources

### 1. Thariq Shihipar — "Claude Code HTML output" (Medium, 2026)
The spec for this plugin. Key claims used here:
- Threshold ≈ 100 lines: "I stopped reading markdown files past 100 lines. My threshold was about the same. Yours probably is too."
- Three forces converged: agent outputs got longer, editing relationship changed (LLM edits, not human), information became spatial.
- Five advantages: density, clarity, shareability, two-way interaction, context ingestion.
- Examples gallery: `thariqs.github.io/html-effectiveness/` (20 self-contained HTML files across 9 categories).

### 2. Edward Tufte — *The Visual Display of Quantitative Information* (Graphics Press, 1983/2001)
Foundational text on data-ink ratio and small multiples. Specifically:
- Ch. 1, "Graphical Excellence" — graphics should reveal the data; markdown's linear structure conceals comparison.
- Ch. 4, "Data-Ink and Graphical Redesign" — every visual element should earn its place. HTML's collapsibles and tabs are data-ink positive (they reveal more per pixel than the same content laid out linearly).

### 3. Bret Victor — "Up and Down the Ladder of Abstraction" (2011, worrydream.com)
Argues that interactive controls let a reader move fluidly between concrete examples and abstract rules. The "lightweight interactivity" tier of this plugin (search, collapsibles, hover tooltips) is the documents-equivalent: it lets a reader move between TOC abstraction and section detail without losing place.

### 4. Maggie Appleton — *A Brief History & Ethos of the Digital Garden* (2020, maggieappleton.com)
Establishes the "garden" pattern: persistent, interlinked, editable knowledge artifacts rendered as HTML. Reinforces single-file HTML as the right artifact shape for long-form thinking (vs. blog posts as linear sequences). Many of her gardens use the exact patterns this plugin generates: sticky TOC, collapsibles, callouts.

### 5. Amelia Wattenberger — "Why React isn't great for actually building websites" + interactive essay archive (wattenberger.com)
Demonstrates lightweight interactivity in essays without frameworks — IntersectionObserver, vanilla scroll handling, inline SVG. The exact technical patterns md-document uses.

### 6. Bartosz Ciechanowski — *Internal Combustion Engine* and other essays (ciechanow.ski)
The high-water mark of single-page interactive explainers. Each essay is a single HTML file with inline SVG animation and controls. Validates the single-file-HTML-as-artifact thesis at the upper bound.

### 7. GitHub READMEs-as-landing-pages (2021-present)
Empirically, READMEs that exceed ~200 lines either (a) get split into a `docs/` folder or (b) get an HTML-rendered version (e.g., GitBook, Docusaurus, mdBook). The market has already voted on the 100-200-line threshold.

## Practical takeaway for the orchestrator

When `doctype_classifier.below_min_lines` is true, refuse the conversion and quote Shihipar. The threshold is empirically defended and stylistically consistent with the wider canon of information-design discipline.
