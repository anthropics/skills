# Single-File HTML Discipline (md-document edition)

**Why this exists:** The orchestrator's single-file discipline document (`markdown-html-orchestrator/references/single_file_html_discipline.md`) establishes the rule. This document records how `md-document` specifically honors it — and what trade-offs the implementation makes.

## The contract

Every md-document output is one `.html` file. The only external HTTP requests it triggers are:

1. **`fonts.googleapis.com`** — Google Fonts CSS for the user's chosen heading + body families.
2. **`cdn.jsdelivr.net`** — Prism.js core + autoloader for syntax highlighting.

Both have graceful fallbacks:
- Google Fonts blocked → system font stack (Georgia/serif fallback for serif families; system-ui/sans-serif fallback for sans families; ui-monospace fallback for mono).
- Prism CDN blocked → `<pre><code>` renders as plain monospaced text (no colors, but still legible).

No other CDN. No web fonts hosted elsewhere. No analytics. No tracking pixels. No CMS framework runtime.

## Why these two externals?

### Google Fonts CSS (not woff files)

We link the Google Fonts CSS endpoint (`fonts.googleapis.com/css2?family=...&display=swap`). The CSS file is < 1 KB; the woff2 font files are lazy-loaded by the browser when they're actually needed for rendering. `display=swap` ensures system fonts show during the loading window, preventing FOIT (Flash of Invisible Text).

Alternative: base64-embed the woff2 files directly in the HTML. We rejected this because:
- A single Inter family at 4 weights is ~280 KB base64-encoded
- Most readers already have it cached from another site
- The CSS-link approach lets Google serve a smaller, browser-specific subset

### Prism.js (not highlight.js or shiki)

| Library | Core size | Why we chose Prism |
|---|---|---|
| Prism.js | ~2 KB core + per-language | Smallest core; autoloader fetches languages on demand |
| highlight.js | ~25 KB | More languages out-of-the-box but bigger initial payload |
| shiki | ~150 KB | VS-Code-fidelity output; oversized for documents |

Prism's autoloader pattern means a Python-heavy spec only fetches the Python language file, not the whole package. The result: most documents add ~5-10 KB of JS for syntax highlighting.

## What `md-document` does NOT externalize

- **CSS** — All styles inline in `<style>` block. The full BASE_CSS + style-overrides + palette is ~6 KB.
- **JavaScript** — Search/copy/scrollspy code is ~3 KB inline. No external bundle.
- **Images** — Logo (if supplied as local path) is base64-embedded. Inline SVG remains inline.
- **Icons** — Callout indicators use plain text characters (`i`, `*`, `!`) rather than icon fonts. Trade-off: less visual richness, no extra CDN entry.

## Footprint by document size

Empirically (from the smoke tests):

| Input markdown | Output HTML (no JS) | Output HTML (with JS) |
|---|---|---|
| ~150 lines (sample spec) | ~11 KB | ~15 KB |
| ~470 lines (markdown-html/CLAUDE.md) | ~17 KB | ~23 KB |

For a typical 100-500-line spec, the user gets a ~15-25 KB artifact they can email, drop in Slack, or upload to any static host. By contrast, a comparable Notion / Confluence / GitBook export would be 200 KB+ of CSS chrome + analytics scripts.

## Anti-patterns

- ❌ `<link rel="stylesheet" href="./style.css">` — separate file = shareability broken.
- ❌ `<script src="./app.js">` — same problem.
- ❌ `cdn.tailwindcss.com` — 200 KB of unused atomic CSS.
- ❌ `<link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/some-icons">` — adds a third external; we don't need it.
- ❌ Service worker registration — single-file artifacts aren't apps.

## Sources

### 1. Thariq Shihipar — "Claude Code HTML output" (Medium, 2026)
"Every playground is a single HTML file with all CSS and JavaScript inlined."

### 2. marketing/landing/skills/landing/SKILL.md
Established the single-file rule in this repo. md-document inherits the discipline.

### 3. Tom MacWright — "Big" (github.com/tmcw/big, MIT)
A single-file presentation tool — full slide deck with keyboard nav in one file. Demonstrates the upper bound.

### 4. Google Fonts API documentation (developers.google.com/fonts/docs/css2)
The `display=swap` parameter behavior and CSS-vs-direct-woff trade-off.

### 5. Prism.js documentation (prismjs.com/extending.html#autoloader)
The autoloader pattern — fetch only the language plugins the document actually uses.

### 6. MDN — "Performance: Reducing HTTP Requests" (developer.mozilla.org)
Articulates why a single file beats N files even on fast networks.

### 7. Anil Dash — "The Web We Lost" (dashes.com, 2012)
The portability argument: a single self-contained HTML file is the most platform-independent web artifact possible.

## Applied to `md-document`

The renderer emits the canonical shape: `<!DOCTYPE html><html><head>...inline-style/font-link/prism-link...</head><body>...rendered-blocks...<inline-script></body></html>`. Anything that tries to externalize CSS, JS, images, or fonts beyond the two permitted endpoints is a regression.
