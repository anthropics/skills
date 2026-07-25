# Presentation UX

**Why this exists:** The `md-slides` converter doesn't try to be Keynote or PowerPoint — those tools optimize for elaborate visual production. It optimizes for the case Shihipar's essay sketches: a deck written in markdown, exported to a single .html file, projected from a browser. This document records the UX choices behind that scope.

## What this skill is for

- A talk you wrote in markdown (intent, not graphic design)
- A board meeting deck assembled from a Notion doc you exported
- A workshop walkthrough where the speaker drives the pace
- A training session that needs presenter notes
- A meeting recap distributed as a printable PDF

## What it isn't for

- Marketing decks with elaborate motion graphics — use Figma / Keynote
- Pitch decks meant to dazzle — same
- Slides you'll edit visually after generation — they're generated artifacts, regenerate from the markdown
- Live-collaborative editing — single-author, single-snapshot

## Signal-to-noise discipline

The single biggest failure mode of agent-generated decks is **too much per slide**. A slide with 40+ source lines of markdown becomes 40+ visible lines of text — the audience reads instead of listening; the speaker becomes redundant.

`slide_splitter.py` warns on any slide whose source markdown exceeds 40 lines (configurable via `MAX_SLIDE_LINES`). It doesn't refuse — sometimes a long quote or code block legitimately needs the space — but it surfaces the count so the author can decide.

Default suggested decomposition: each idea = one slide. If a slide has 5+ bullet points or 200+ words of body text, it should probably split.

## What the renderer enforces visually

- **22px base font, 1.45 line-height** — projector-readable from the back row
- **3rem H1, 2.5rem H2** — slide titles are the visual anchor
- **8vw side padding, 4vh top/bottom** — generous margins so text doesn't crash the edges of the projection
- **One slide visible at a time** — no infinite scroll; the slide is the unit of attention
- **No transitions / animations by default** — `prefers-reduced-motion: reduce` honored; no fly-ins or fades to distract
- **Progress bar at top** — 3px high; tells the audience how far through they are

## The presenter-notes contract

`<!-- notes: ... -->` blocks attached to slides serve three audiences:

1. **The speaker** during the talk (visible in presenter view)
2. **The audience** if the deck is distributed afterward (notes stay accessible via the data attribute, can be extracted programmatically)
3. **The author** when revisiting the deck months later (notes preserve intent that the slide alone doesn't)

`--strict-notes` enforces ≥ 50% coverage when presenter mode is in use — a deck where most slides have no notes isn't really set up for presenter mode.

## Sources

### 1. Cliff Atkinson — *Beyond Bullet Points* (Microsoft Press, 2011, 4th ed.)
The case that bullet-heavy slides suppress audience attention. We don't enforce a bullet-cap, but the > 40-line warning targets the same failure pattern.

### 2. Garr Reynolds — *Presentation Zen* (New Riders, 2019, 2nd ed.)
The "less is more" discipline: high signal-to-noise per slide. Reynolds argues for one idea per slide; our default 40-line warning approximates this for markdown-authored decks (a single idea written in markdown rarely exceeds 40 lines).

### 3. Edward Tufte — *The Cognitive Style of PowerPoint* (Graphics Press, 2003)
The polemic against slide-as-document. Tufte's argument is that slides flatten hierarchical information; our split into clear slide units + the optional handout-via-print mode (each slide one page) honors his core complaint by keeping the slide and the handout cleanly separable.

### 4. Jakob Nielsen / NN/g — *PowerPoint Usability* (2011, updated 2024)
Empirical: audience attention drops sharply when a slide exceeds about 6 bullet points or about 200 words. The 40-source-line warning is a markdown-aware proxy for these thresholds.

### 5. Susan Weinschenk — *100 Things Every Presenter Needs to Know About People* (New Riders, 2012)
Specifically on the cognitive cost of reading-while-listening — the audience can't do both well. Our presenter-notes pattern lets the speaker put the depth in notes and keep the slide visually minimal.

### 6. Marp / reveal.js / pandoc-Beamer — markdown-to-slides conventions
The `---` HR boundary and `<!-- notes: ... -->` syntax we accept come from the convergent convention these tools have shipped for a decade. We're compatible by reading the same markup, not innovating new syntax.

### 7. Tom MacWright — *Big* (github.com/tmcw/big, MIT)
A single-HTML-file presentation tool that emphasizes ridiculously-large text (the slide title fills the viewport). We're less aggressive — we render markdown bodies — but we share the discipline of "one slide = one viewport, no scroll."

## Applied to `md-slides`

The renderer ships projector-readable defaults, one-slide-per-viewport layout, presenter-notes contract, soft-warn on > 40 lines per slide, and the print stylesheet for PDF export. No graphics tooling, no motion, no live collaboration — those are out of scope.
