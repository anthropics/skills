# Single-File Deck Conventions

**Why this exists:** The orchestrator's single-file discipline document establishes the rule for the whole domain. This document records the md-slides-specific decisions — what's different about decks vs documents, and what the single-file constraint means specifically for presentation artifacts.

## The contract

One `.html` file, projected from any browser. Externals limited to:
- **`fonts.googleapis.com`** — Google Fonts CSS for typography
- **`cdn.jsdelivr.net`** — Prism.js, ONLY when `--syntax` is explicitly passed (opt-in; off by default)

Why Prism is opt-in for decks (vs always-on for md-document):
- Most decks have few/short code blocks; the Prism payload is overhead for a typography-heavy artifact
- A speaker projecting a deck doesn't need pixel-perfect syntax fidelity; the audience reads from a distance
- Print-to-PDF benefits from absence of CDN dependencies (the print artifact is the artifact, not a server)

## Why single-file specifically matters for decks

1. **Projector-friendly**: the speaker opens one file from their laptop. No server, no `npm start`, no build artifact directory.
2. **Conference WiFi-tolerant**: even if WiFi fails mid-talk, the deck keeps working. Google Fonts is cached after first paint; Prism (when enabled) gracefully degrades to plain `<pre>`.
3. **PDF-exportable**: the same `.html` file becomes a PDF via the browser's print dialog (`Cmd+P` / `Ctrl+P`). The `@media print` stylesheet makes each slide one page.
4. **Email-attachable**: a 15-30 KB single-file deck attaches to email and renders inline in modern clients.
5. **Reproducible**: the deck-as-artifact is deterministic. Re-running the renderer on the same markdown produces the same HTML (no timestamps, no random IDs).

## What we deliberately don't externalize

- **CSS** — fully inline. Base CSS + design-system tokens + style overrides = ~6-7 KB.
- **JavaScript** — fully inline. Vanilla JS + IntersectionObserver-free navigation = ~3 KB.
- **Slide content** — every `<section>` is in the HTML. No lazy-loading, no fetch.
- **Speaker notes** — stored in the `data-notes` attribute of each `<section>`. Travels with the slide.
- **Images** — currently passed through as URLs; users wanting full single-file portability for image-heavy decks can pre-process to base64 (out of scope for v2.10.3).

## Why no transitions / animations

Three reasons:
1. **Speaker pacing** — transitions add latency between key press and visible response. For a brisk talk, that latency adds up.
2. **Recording-friendly** — many talks get screen-recorded. A snap transition is easier to edit than a fade.
3. **`prefers-reduced-motion`** — about 35% of users have motion-sensitivity preferences enabled (per WCAG WG estimates). A motion-free deck works for everyone by default.

If a deck genuinely needs motion, the user can add a `<style>` override block to the rendered HTML (it's a `.html` file — fully editable).

## Print-to-PDF discipline

```css
@media print {
    html, body { height: auto; overflow: visible; }
    .chrome, .progress, .presenter-panel { display: none !important; }
    .slide {
        display: flex !important;     /* override "only active is visible" */
        position: relative;            /* break out of absolute positioning */
        height: 100vh;                 /* one slide = one page */
        page-break-after: always;
        break-after: page;
    }
    .slide:last-child { page-break-after: auto; }
}
```

The result: `Cmd+P` from the deck produces a PDF where each slide is one A4/Letter page. No PDF generation pipeline needed; the browser does it.

## Sources

### 1. Tom MacWright — *Big* (github.com/tmcw/big, MIT)
The single-file deck tool that proved the model works. Used at speaking engagements by the JavaScript community for over a decade.

### 2. reveal.js — Single-file export (revealjs.com/installation/#full-setup)
reveal.js can produce a single-file output but typically ships multi-file. We adopt the single-file end of the spectrum exclusively.

### 3. Slides.com — HTML export
Slides.com's "export to HTML" produces a single-file artifact. Validates the user demand for the format independent of any one tool.

### 4. Marp — *Marp CLI HTML output* (marp.app)
Markdown-to-deck tool. Outputs single-file HTML by default. Our `---` boundary + `<!-- notes: -->` syntax is read-compatible with Marp's input.

### 5. Pandoc — `--standalone` flag (pandoc.org)
The pattern of "compile to single self-contained HTML." We honor the same constraint.

### 6. MDN — `@media print` (developer.mozilla.org/en-US/docs/Web/CSS/@media/print)
The browser-native primitive that makes "deck as printable PDF" work without any PDF library.

### 7. WCAG 2.2 §2.3.3 *Animation from Interactions* and `prefers-reduced-motion`
The accessibility-driven case for motion-free defaults. Our deck respects this preference automatically.

## Applied to `md-slides`

`deck_html_renderer.py` emits the single-file shape: inline CSS + inline JS + all `<section>` elements with `data-notes` attributes. The only external is Google Fonts CSS; Prism is opt-in via `--syntax`. Print-to-PDF works out of the box.
