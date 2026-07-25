#!/usr/bin/env python3
"""deck_html_renderer.py - Render parsed slides into a single-file HTML deck.

Stdlib-only. Reads slide JSON (from slide_splitter + presenter_notes_parser)
plus the design-system config, emits one .html file with:

  - All slides as <section class="slide" id="slide-N"> elements
  - One slide visible at a time (driven by URL hash + JS)
  - Keyboard nav: ← / → / Space / PgDn / PgUp / Home / End
  - Presenter mode toggle (P key): split view with current + notes + clock + next-slide preview
  - @media print { section { display: block; page-break-after: always; } } → PDF export
  - 12 design-system tokens applied; design_style affects layout density
  - Reuses md-document's markdown_parser to render slide-body content (paragraphs,
    lists, code, tables, callouts) consistently with md-document

Vanilla JS only — no frameworks. Total payload ~3-4 KB inline.

Single-file output: all CSS + JS inline. Only external is Google Fonts CSS.
No Prism (slide code blocks are short; we color them with the design-system
code background but don't fetch the Prism CDN by default — pass --syntax to
enable Prism for code-heavy decks).

NO LLM CALLS. Pure templating.

Usage:
    python deck_html_renderer.py --slides slides.json --output deck.html
    python deck_html_renderer.py --sample --output /tmp/sample.html
    python deck_html_renderer.py --slides slides.json --syntax --output deck.html
"""

from __future__ import annotations

import argparse
import base64
import html
import json
import os
import sys
from pathlib import Path
from typing import Any

# Bridge to design-system config
_DESIGN_SYSTEM_SCRIPTS = (
    Path(__file__).resolve().parent.parent.parent / "design-system" / "scripts"
)
sys.path.insert(0, str(_DESIGN_SYSTEM_SCRIPTS))
try:
    import config_loader as _cfg
except ImportError:
    _cfg = None

# Reuse md-document's markdown parser for slide-body rendering
_MD_DOCUMENT_SCRIPTS = (
    Path(__file__).resolve().parent.parent.parent / "md-document" / "scripts"
)
sys.path.insert(0, str(_MD_DOCUMENT_SCRIPTS))
try:
    import markdown_parser as _mp
except ImportError:
    _mp = None


CALLOUT_ICONS: dict[str, str] = {
    "NOTE": "i", "TIP": "*", "IMPORTANT": "!", "WARNING": "!", "CAUTION": "!",
}


def _palette_to_css(palette: dict[str, str]) -> str:
    if not palette:
        palette = {
            "--md-bg": "#0E1E38", "--md-surface": "#142B50", "--md-border": "#1A3868",
            "--md-text": "#F7F7F2", "--md-text-muted": "rgba(247, 247, 242, 0.68)",
            "--md-accent": "#00D4AA", "--md-accent-soft": "rgba(0, 212, 170, 0.14)",
            "--md-code-bg": "#122648",
            "--md-link": "#00D4AA", "--md-link-hover": "#08FECE",
            "--md-success": "#10A85C", "--md-warn": "#C87C10",
        }
    return "\n".join(f"    {k}: {v};" for k, v in palette.items())


def _font_url(heading: str, body: str) -> str:
    families = sorted({heading, body})
    parts = "&".join(f"family={f.replace(' ', '+')}:wght@400;600;700" for f in families)
    return f"https://fonts.googleapis.com/css2?{parts}&display=swap"


def _font_stack(name: str) -> str:
    fallback = ("Georgia, serif" if name in
                ("Playfair Display", "Merriweather", "Lora", "Source Serif 4")
                else "system-ui, -apple-system, sans-serif")
    return f"'{name}', {fallback}"


def _render_block(block: dict[str, Any]) -> str:
    """Render one parsed-markdown block to slide HTML."""
    t = block["type"]
    if t == "heading":
        # Inside a slide, demote: H1 already handled as slide title; H2 stays H2; etc.
        level = max(2, block["level"])
        text = _mp.render_inline_html(block["text"]) if _mp else html.escape(block["text"])
        return f'<h{level}>{text}</h{level}>'
    if t == "paragraph":
        text = _mp.render_inline_html(block["text"]) if _mp else html.escape(block["text"])
        return f'<p>{text}</p>'
    if t == "hr":
        return '<hr>'
    if t == "code":
        lang = block.get("language") or "text"
        body = html.escape(block["body"])
        return f'<pre><code class="language-{html.escape(lang)}">{body}</code></pre>'
    if t == "list":
        tag = "ol" if block.get("ordered") else "ul"
        items = "".join(
            f"<li>{_mp.render_inline_html(item) if _mp else html.escape(item)}</li>"
            for item in block["items"]
        )
        return f"<{tag}>{items}</{tag}>"
    if t == "table":
        headers = block["headers"]
        aligns = block.get("aligns") or ["left"] * len(headers)
        rows = block["rows"]
        thead = "<thead><tr>" + "".join(
            f'<th class="align-{a}">{_mp.render_inline_html(h) if _mp else html.escape(h)}</th>'
            for h, a in zip(headers, aligns)
        ) + "</tr></thead>"
        tbody = "<tbody>" + "".join(
            "<tr>" + "".join(
                f'<td class="align-{aligns[i] if i < len(aligns) else "left"}">'
                f'{_mp.render_inline_html(cell) if _mp else html.escape(cell)}</td>'
                for i, cell in enumerate(row)
            ) + "</tr>"
            for row in rows
        ) + "</tbody>"
        return f"<table>{thead}{tbody}</table>"
    if t == "callout":
        kind = (block.get("kind") or "NOTE").upper()
        icon = CALLOUT_ICONS.get(kind, "i")
        body = "<br>".join(
            _mp.render_inline_html(ln) if _mp else html.escape(ln)
            for ln in (block.get("body_lines") or []) if ln
        )
        klass = kind.lower()
        return (
            f'<aside class="callout callout-{klass}" role="note">'
            f'<div class="callout-label"><span class="callout-icon" aria-hidden="true">{icon}</span>'
            f'{html.escape(kind)}</div>'
            f'<div class="callout-body">{body}</div>'
            f'</aside>'
        )
    if t == "blockquote":
        body = "<br>".join(
            _mp.render_inline_html(ln) if _mp else html.escape(ln)
            for ln in block.get("body_lines") or [] if ln
        )
        return f"<blockquote>{body}</blockquote>"
    return ""


def _render_slide_body(body_markdown: str) -> str:
    """Parse a slide's markdown body and render it as HTML blocks."""
    if not body_markdown.strip():
        return ""
    if _mp is None:
        return f'<pre>{html.escape(body_markdown)}</pre>'
    parsed = _mp.parse_markdown(body_markdown)
    return "\n".join(_render_block(b) for b in parsed["blocks"])


# ----- CSS template -----------------------------------------------------------

BASE_CSS = """
:root {
__PALETTE__
    --md-font-heading: __HEADING_FONT__;
    --md-font-body: __BODY_FONT__;
    --md-font-mono: 'JetBrains Mono', ui-monospace, SFMono-Regular, Menlo, monospace;
}

* { box-sizing: border-box; }
html, body { margin: 0; padding: 0; height: 100%; overflow: hidden; }
body {
    background: var(--md-bg);
    color: var(--md-text);
    font-family: var(--md-font-body);
    font-size: 22px;
    line-height: 1.45;
}

/* Slide layout — each slide is a viewport-sized panel */
.deck { width: 100vw; height: 100vh; position: relative; }
.slide {
    position: absolute;
    inset: 0;
    display: none;
    flex-direction: column;
    justify-content: center;
    padding: 4vh 8vw;
    overflow: auto;
}
.slide.active { display: flex; }
.slide h1, .slide h2, .slide h3 {
    font-family: var(--md-font-heading);
    margin: 0 0 0.6em;
    line-height: 1.15;
    font-weight: 700;
}
.slide h1 { font-size: 3rem; }
.slide h2 { font-size: 2.5rem; }
.slide h3 { font-size: 1.875rem; }
.slide p { margin: 0.5em 0 1em; font-size: 1.25rem; }
.slide ul, .slide ol { padding-left: 1.5em; font-size: 1.25rem; }
.slide li { margin: 0.4em 0; }
.slide a { color: var(--md-link); }
.slide code {
    background: var(--md-code-bg);
    padding: 0.1em 0.3em;
    border-radius: 4px;
    font-family: var(--md-font-mono);
    font-size: 0.9em;
}
.slide pre {
    background: var(--md-code-bg);
    border: 1px solid var(--md-border);
    border-radius: 8px;
    padding: 1rem 1.25rem;
    font-family: var(--md-font-mono);
    font-size: 1rem;
    overflow: auto;
    margin: 0.75em 0;
}
.slide pre code { background: transparent; padding: 0; }
.slide table {
    width: 100%;
    border-collapse: collapse;
    margin: 1em 0;
    font-size: 1.125rem;
}
.slide th, .slide td { border: 1px solid var(--md-border); padding: 0.5em 0.75em; text-align: left; }
.slide th { background: var(--md-surface); font-weight: 600; }
.slide td.align-center, .slide th.align-center { text-align: center; }
.slide td.align-right, .slide th.align-right { text-align: right; }
.slide blockquote {
    border-left: 4px solid var(--md-accent);
    margin: 1em 0;
    padding: 0.4em 1em;
    color: var(--md-text-muted);
    font-style: italic;
    font-size: 1.25rem;
}
.slide hr { border: 0; border-top: 1px solid var(--md-border); margin: 1.5em 0; }

.slide .callout {
    border-left: 4px solid var(--md-accent);
    background: var(--md-accent-soft);
    padding: 0.75em 1em;
    margin: 1em 0;
    border-radius: 0 8px 8px 0;
}
.slide .callout-label {
    font-family: var(--md-font-heading);
    font-weight: 700;
    font-size: 0.875rem;
    letter-spacing: 0.05em;
    text-transform: uppercase;
    color: var(--md-accent);
    margin-bottom: 0.25em;
    display: flex;
    gap: 0.5em;
    align-items: center;
}
.slide .callout-note { border-left-color: var(--md-link); }
.slide .callout-tip { border-left-color: var(--md-success); }
.slide .callout-warning { border-left-color: var(--md-warn); }
.slide .callout-caution { border-left-color: var(--md-warn); }

/* Chrome (slide counter + hint) */
.chrome {
    position: fixed;
    bottom: 1rem;
    right: 1.25rem;
    font-family: var(--md-font-mono);
    font-size: 0.875rem;
    color: var(--md-text-muted);
    user-select: none;
}
.chrome a { color: var(--md-text-muted); margin-right: 0.5rem; }
.chrome a:hover { color: var(--md-accent); }

/* Progress bar */
.progress {
    position: fixed;
    top: 0; left: 0;
    height: 3px;
    background: var(--md-accent);
    transition: width 0.2s ease;
    z-index: 100;
}

/* Presenter mode (P key toggles body class) */
body.presenter .deck { width: 60vw; }
body.presenter .presenter-panel { display: flex; }
.presenter-panel {
    display: none;
    position: fixed;
    top: 0; right: 0;
    width: 40vw;
    height: 100vh;
    background: var(--md-surface);
    border-left: 1px solid var(--md-border);
    flex-direction: column;
    padding: 1.5rem 1.5rem;
    font-size: 1rem;
    overflow: auto;
}
.presenter-panel h3 {
    font-family: var(--md-font-heading);
    font-size: 0.875rem;
    text-transform: uppercase;
    letter-spacing: 0.05em;
    color: var(--md-text-muted);
    margin: 0 0 0.5rem;
    border-bottom: 1px solid var(--md-border);
    padding-bottom: 0.4rem;
}
.presenter-panel .clock { font-family: var(--md-font-mono); font-size: 1.5rem; margin-bottom: 1rem; }
.presenter-panel .notes { flex: 1; line-height: 1.5; color: var(--md-text); margin-bottom: 1rem; white-space: pre-wrap; }
.presenter-panel .next-preview {
    background: var(--md-bg);
    border: 1px solid var(--md-border);
    border-radius: 8px;
    padding: 0.75rem 1rem;
    font-size: 0.875rem;
    max-height: 25vh;
    overflow: hidden;
    opacity: 0.7;
}
.presenter-panel .next-preview h4 {
    font-family: var(--md-font-heading);
    margin: 0 0 0.3em;
    font-size: 1rem;
    color: var(--md-accent);
}

/* Print: all slides visible, one per page */
@media print {
    html, body { height: auto; overflow: visible; }
    .chrome, .progress, .presenter-panel { display: none !important; }
    .deck, body.presenter .deck { width: 100%; height: auto; }
    .slide {
        display: flex !important;
        position: relative;
        height: 100vh;
        page-break-after: always;
        break-after: page;
    }
    .slide:last-child { page-break-after: auto; }
}

@media (prefers-reduced-motion: reduce) {
    * { animation: none !important; transition: none !important; }
}
"""

# Inline vanilla-JS payload
JS_PAYLOAD = r"""
(function () {
    "use strict";
    var slides = document.querySelectorAll(".slide");
    var total = slides.length;
    var current = 0;
    var presenter = false;

    function show(idx) {
        idx = Math.max(0, Math.min(total - 1, idx));
        slides.forEach(function (s, i) {
            s.classList.toggle("active", i === idx);
        });
        current = idx;
        document.getElementById("counter").textContent = (current + 1) + " / " + total;
        var prog = document.getElementById("progress");
        if (prog) prog.style.width = (100 * (current + 1) / total) + "%";
        if (location.hash !== "#" + (current + 1)) {
            history.replaceState(null, "", "#" + (current + 1));
        }
        updatePresenterPanel();
    }

    function next() { show(current + 1); }
    function prev() { show(current - 1); }
    function first() { show(0); }
    function last() { show(total - 1); }

    function togglePresenter() {
        presenter = !presenter;
        document.body.classList.toggle("presenter", presenter);
        updatePresenterPanel();
    }

    function updatePresenterPanel() {
        var panel = document.querySelector(".presenter-panel");
        if (!panel) return;
        var notes = slides[current].getAttribute("data-notes") || "(no notes for this slide)";
        panel.querySelector(".notes").textContent = notes;
        var preview = panel.querySelector(".next-preview");
        if (current + 1 < total) {
            var nextSlide = slides[current + 1];
            var title = nextSlide.querySelector("h1, h2") ;
            preview.innerHTML = "<h4>Up next (#" + (current + 2) + ")</h4>" +
                (title ? title.outerHTML : "<em>(no title)</em>");
            preview.style.display = "block";
        } else {
            preview.innerHTML = "<h4>End of deck</h4>";
        }
    }

    function tickClock() {
        var now = new Date();
        var hh = String(now.getHours()).padStart(2, "0");
        var mm = String(now.getMinutes()).padStart(2, "0");
        var ss = String(now.getSeconds()).padStart(2, "0");
        var el = document.querySelector(".presenter-panel .clock");
        if (el) el.textContent = hh + ":" + mm + ":" + ss;
    }

    document.addEventListener("keydown", function (e) {
        if (e.metaKey || e.ctrlKey || e.altKey) return;
        switch (e.key) {
            case "ArrowRight":
            case "PageDown":
            case " ":
                e.preventDefault(); next(); break;
            case "ArrowLeft":
            case "PageUp":
                e.preventDefault(); prev(); break;
            case "Home": e.preventDefault(); first(); break;
            case "End":  e.preventDefault(); last();  break;
            case "p":
            case "P":
                e.preventDefault(); togglePresenter(); break;
            case "Escape":
                if (presenter) { e.preventDefault(); togglePresenter(); }
                break;
        }
    });

    // Mount the initial slide (respect URL hash, otherwise slide 1)
    var initial = 0;
    if (location.hash) {
        var n = parseInt(location.hash.slice(1), 10);
        if (!isNaN(n) && n >= 1 && n <= total) initial = n - 1;
    }
    show(initial);
    setInterval(tickClock, 1000);
    tickClock();
})();
"""


def render(deck_payload: dict[str, Any], config: dict[str, Any],
           title: str = "Deck", enable_syntax: bool = False) -> str:
    palette = config.get("derived_palette") or {}
    typo = config.get("typography") or {}
    heading_font = typo.get("heading_font", "Inter")
    body_font = typo.get("body_font", "Inter")
    style = config.get("design_style", "technical")
    company_name = config.get("company_name", "")

    css = (BASE_CSS
           .replace("__PALETTE__", _palette_to_css(palette))
           .replace("__HEADING_FONT__", _font_stack(heading_font))
           .replace("__BODY_FONT__", _font_stack(body_font)))

    slides = deck_payload.get("slides", [])
    slide_html_parts: list[str] = []
    for s in slides:
        title_html = (f'<h1>{html.escape(s["title"])}</h1>' if s.get("title") else "")
        body_html = _render_slide_body(s.get("body_markdown", ""))
        notes_attr = html.escape(s.get("notes") or "", quote=True)
        slide_html_parts.append(
            f'<section class="slide" id="slide-{s["slide_number"]}" '
            f'data-notes="{notes_attr}">'
            f'{title_html}{body_html}</section>'
        )
    slides_html = "\n".join(slide_html_parts)

    prism_links = ""
    if enable_syntax:
        prism_links = (
            '<link rel="stylesheet" '
            'href="https://cdn.jsdelivr.net/npm/prismjs@1.29.0/themes/prism-tomorrow.min.css">\n'
            '<script defer src="https://cdn.jsdelivr.net/npm/prismjs@1.29.0/components/prism-core.min.js"></script>\n'
            '<script defer src="https://cdn.jsdelivr.net/npm/prismjs@1.29.0/plugins/autoloader/prism-autoloader.min.js"></script>'
        )

    return f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{html.escape(title)}</title>
<link rel="preconnect" href="https://fonts.googleapis.com" crossorigin>
<link rel="stylesheet" href="{_font_url(heading_font, body_font)}">
{prism_links}
<style>{css}</style>
</head>
<body class="style-{style}">
<div id="progress" class="progress"></div>
<div class="deck">
{slides_html}
</div>

<aside class="presenter-panel" aria-label="Presenter view (toggle with P)">
    <h3>Clock</h3>
    <div class="clock">--:--:--</div>
    <h3>Speaker notes</h3>
    <div class="notes"></div>
    <div class="next-preview"></div>
</aside>

<div class="chrome">
    <a href="#" onclick="event.preventDefault(); document.dispatchEvent(new KeyboardEvent('keydown', {{key:'P'}}))">P · presenter</a>
    <span id="counter">1 / {len(slides)}</span>
</div>

<script>{JS_PAYLOAD}</script>
</body>
</html>"""


def main(argv: list[str]) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("--slides", help="Path to presenter_notes_parser JSON, or '-' for stdin")
    p.add_argument("--output", help="Path to write HTML (else stdout)")
    p.add_argument("--title", default="Deck", help="Browser tab title")
    p.add_argument("--syntax", action="store_true",
                   help="Enable Prism.js CDN for code syntax highlighting (off by default)")
    p.add_argument("--no-config", action="store_true",
                   help="Bypass design-system config (use DEFAULTS)")
    p.add_argument("--sample", action="store_true",
                   help="Render the built-in 5-slide sample deck")
    p.add_argument("--strict-notes", action="store_true",
                   help="Refuse to render if < 50%% of slides have presenter notes "
                        "AND user wants presenter mode")
    args = p.parse_args(argv)

    if args.sample:
        sys.path.insert(0, str(Path(__file__).resolve().parent))
        import presenter_notes_parser
        import slide_splitter
        slides_payload = slide_splitter.split_slides(slide_splitter.SAMPLE_MARKDOWN)
        deck_payload = presenter_notes_parser.attach_notes(slides_payload)
        title = "Sample Deck — The Case for Single-File HTML"
    else:
        if not args.slides:
            p.print_help()
            return 0
        raw = sys.stdin.read() if args.slides == "-" else Path(args.slides).read_text(encoding="utf-8")
        deck_payload = json.loads(raw)
        title = args.title

    # Hard rule: if --strict-notes, refuse < 50% coverage
    if args.strict_notes:
        coverage = deck_payload.get("summary", {}).get("notes_coverage_pct", 0)
        if coverage < 50:
            print(f"refusing (--strict-notes): only {coverage}% of slides have presenter "
                  f"notes (need ≥ 50% for a presenter deck). Add more "
                  f"<!-- notes: ... --> blocks or drop --strict-notes.",
                  file=sys.stderr)
            return 7

    if args.no_config or os.environ.get("MARKDOWN_HTML_NO_CONFIG") == "1":
        config = _cfg.DEFAULTS if _cfg else {}
    else:
        config = _cfg.load_config() if _cfg else {}

    output = render(deck_payload, config, title=title, enable_syntax=args.syntax)

    if args.output and args.output != "-":
        Path(args.output).write_text(output, encoding="utf-8")
        notes_count = sum(1 for s in deck_payload.get("slides", []) if s.get("has_notes"))
        print(f"wrote {args.output}: {len(output):,} bytes, "
              f"{deck_payload['summary']['total_slides']} slides "
              f"({notes_count} with notes, syntax={args.syntax})")
    else:
        print(output)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
