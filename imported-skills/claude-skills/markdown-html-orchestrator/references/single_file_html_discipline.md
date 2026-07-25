# Single-File HTML Discipline

**Why this exists:** Multi-file HTML output (separate CSS, JS, images, asset folders) breaks the central value proposition: shareability. The recipient can't drop the file into Slack, attach it to an email, or upload it to a static host with one drag. This document codifies the single-file constraint and names the few permitted exceptions.

## The constraint

Every converter (md-document, md-review, md-slides) MUST produce one `.html` file containing all CSS and all JavaScript inline. The only externals permitted are:

1. **Google Fonts CSS** — pulled from `fonts.googleapis.com` via `<link rel="stylesheet">`. Falls back to system stack if blocked.
2. **Prism.js** — pulled from `cdn.jsdelivr.net` or `cdnjs.cloudflare.com` for syntax highlighting. Falls back to plain `<pre>` if blocked.

No other CDN. No build step. No bundler. No framework runtime.

## Why

### Shareability
A single .html file uploads to S3, Vercel, Netlify, or any static host in one operation. It also opens in a recipient's browser without a server, which means it works in:
- Slack DM previews
- Email attachments (Gmail / Outlook web)
- Local `file://` URLs
- GitHub `raw.githubusercontent.com` links
- USB sticks given to a non-technical reviewer

Multi-file output breaks every one of those flows. The marketing/landing/ skill made the same choice for the same reason.

### Portability
Single-file HTML survives copying, archiving, and email-attachment workflows. It's the closest thing to PDF that the web has, with the advantage of being editable and searchable.

### No build-step regret
The moment you require a build step, you require: a Node version, a package.json, a node_modules folder, a transpiler, a watcher, a runtime, and a deployment story. None of that survives "send this to a teammate."

## Permitted CDN externals — discipline

```html
<!-- Google Fonts (CSS only — woff files lazy-loaded by browser) -->
<link rel="preconnect" href="https://fonts.googleapis.com" crossorigin>
<link rel="stylesheet"
      href="https://fonts.googleapis.com/css2?family=Inter:wght@400;600&display=swap">

<!-- Prism.js core + theme + autoloader (gracefully degrades without it) -->
<link rel="stylesheet"
      href="https://cdn.jsdelivr.net/npm/prismjs@1.29.0/themes/prism-tomorrow.min.css">
<script defer
        src="https://cdn.jsdelivr.net/npm/prismjs@1.29.0/components/prism-core.min.js"></script>
<script defer
        src="https://cdn.jsdelivr.net/npm/prismjs@1.29.0/plugins/autoloader/prism-autoloader.min.js"></script>
```

Both fall back gracefully: if the CDN is blocked, fonts default to the system stack and code blocks render as plain `<pre>`. The page is still readable, still searchable, still copy-pasteable.

## Anti-patterns

- ❌ External CSS file (`<link rel="stylesheet" href="./style.css">`) — recipient gets a broken page.
- ❌ External JS file (`<script src="./app.js">`) — same problem.
- ❌ External image references for hero/logo (`<img src="./logo.png">`) — base64-embed instead.
- ❌ React/Vue/Svelte/Alpine runtime — vanilla JS only.
- ❌ Tailwind via CDN (`cdn.tailwindcss.com`) — 200 KB of unused CSS; just inline what you use.
- ❌ Web Components requiring a custom-element registry from CDN — same problem.

## Sources

### 1. Thariq Shihipar — "Claude Code HTML output" (Medium, 2026)
"Every playground is a single HTML file with all CSS and JavaScript inlined. No external dependencies. No build step. Open it in any browser." (Playground plugin section — same discipline applies to converted documents.)

### 2. marketing/landing/skills/landing/SKILL.md §"Single-File HTML Discipline"
Established the rule for this repo. Marketing landing pages were the first artifact type to require single-file output; this plugin inherits the discipline directly.

### 3. Tom MacWright — "Big" (github.com/tmcw/big, MIT)
A presentation tool that compiles to a single HTML file. Demonstrates the upper bound of what's possible with the constraint (full slide deck, presenter mode, navigation, in one file).

### 4. Mozilla MDN — *Performance: Reducing HTTP Requests*
Single-file output minimizes round trips. Even on fast networks, a single 200 KB HTML file beats one HTML + three CSS + five JS + four image requests.

### 5. The Web We Lost — Anil Dash (2012, dashes.com)
Argues for portable, host-anywhere web artifacts as a counter to platform lock-in. Single-file HTML is the most portable web artifact possible — no platform, no JS framework, no server.

### 6. Prism.js documentation (prismjs.com)
Lightweight syntax highlighter (~2 KB core + per-language plugins on demand) designed for CDN delivery. The right tradeoff for "single-file with one allowed external."

### 7. Google Fonts API documentation (developers.google.com/fonts/docs/css2)
The `display=swap` parameter ensures system-font fallback while web fonts load, preventing FOUT/FOIT on slow connections. Required parameter for every Google Fonts link the converters emit.

## Applied to markdown-html

`md-document/scripts/html_renderer.py`, `md-review/scripts/review_html_renderer.py`, and `md-slides/scripts/deck_html_renderer.py` all emit single-file output with exactly the two permitted externals. Anything else is a regression.
