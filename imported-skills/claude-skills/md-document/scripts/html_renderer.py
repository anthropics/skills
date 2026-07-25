#!/usr/bin/env python3
"""html_renderer.py - Render a parsed-markdown section tree to single-file HTML.

Stdlib-only. Reads a JSON section tree (from markdown_parser.py) plus the
design-system config (from config_loader.py), emits a complete self-contained
.html file with:

  - <title> from the document's H1
  - Google Fonts CDN link (per typography.heading_font + typography.body_font)
  - Prism.js CDN link (per code_theme: light/dark/auto)
  - <style> block with :root { --md-bg: ...; } from the derived 12-token palette
  - Base CSS scaled by typography.scale_ratio and design_style
  - TOC per toc.behavior (sticky-sidebar / collapsible-top / inline / none)
  - Rendered blocks: headings, paragraphs, lists, tables, code, callouts, quotes
  - Footer with company_name + logo (base64-embedded if data: URL or local file)

NO LLM CALLS. Pure templating + config-driven CSS.

The output is one HTML file. Externals are limited to:
  - fonts.googleapis.com (Google Fonts CSS)
  - cdn.jsdelivr.net (Prism.js)
Falls back to system fonts + plain <pre> if either CDN is blocked.

Usage:
    python html_renderer.py --sections sections.json --output report.html
    python html_renderer.py --sample
    python html_renderer.py --sections - --output - --no-config  # full pipe
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

_DESIGN_SYSTEM_SCRIPTS = (
    Path(__file__).resolve().parent.parent.parent / "design-system" / "scripts"
)
sys.path.insert(0, str(_DESIGN_SYSTEM_SCRIPTS))
try:
    import config_loader as _cfg
except ImportError:
    _cfg = None

# Re-export from markdown_parser so html_renderer can self-sample
sys.path.insert(0, str(Path(__file__).resolve().parent))
try:
    import markdown_parser as _mp
except ImportError:
    _mp = None


# ----- Design-style presets ----------------------------------------------------

STYLE_CSS_OVERRIDES: dict[str, str] = {
    "editorial": """
        body.style-editorial { max-width: 720px; line-height: 1.75; }
        body.style-editorial main h2 { font-size: calc(1rem * var(--md-scale) * var(--md-scale) * var(--md-scale)); margin-top: 4rem; }
        body.style-editorial p { font-size: 1.0625rem; }
    """,
    "technical": """
        body.style-technical { max-width: 960px; line-height: 1.6; }
        body.style-technical main h2 { font-size: calc(1rem * var(--md-scale) * var(--md-scale)); margin-top: 2.5rem; }
        body.style-technical pre { font-size: 0.875rem; line-height: 1.5; }
    """,
    "minimal": """
        body.style-minimal { max-width: 680px; line-height: 1.65; }
        body.style-minimal main h2 { font-size: calc(1rem * var(--md-scale)); margin-top: 3rem; font-weight: 400; }
        body.style-minimal .callout { background: transparent; border-left: 2px solid var(--md-border); }
    """,
    "playful": """
        body.style-playful { max-width: 880px; line-height: 1.7; }
        body.style-playful main h2 { font-size: calc(1rem * var(--md-scale) * var(--md-scale) * var(--md-scale)); margin-top: 3.5rem; }
        body.style-playful .callout { border-radius: 1rem; box-shadow: 0 4px 16px rgba(0,0,0,0.04); }
    """,
}


# ----- CSS template ------------------------------------------------------------

BASE_CSS = """
:root {
__PALETTE__
    --md-scale: __SCALE__;
    --md-font-heading: __HEADING_FONT__;
    --md-font-body: __BODY_FONT__;
}

* { box-sizing: border-box; }
html { scroll-behavior: smooth; -webkit-text-size-adjust: 100%; }
body {
    margin: 0;
    padding: 2rem 1.5rem;
    background: var(--md-bg);
    color: var(--md-text);
    font-family: var(--md-font-body);
    font-size: 16px;
    line-height: 1.6;
    max-width: 960px;
    margin-left: auto;
    margin-right: auto;
}

main h1, main h2, main h3, main h4, main h5, main h6 {
    font-family: var(--md-font-heading);
    color: var(--md-text);
    line-height: 1.25;
    margin: 1.5em 0 0.5em;
    font-weight: 600;
    scroll-margin-top: 1rem;
}
main h1 { font-size: calc(1rem * var(--md-scale) * var(--md-scale) * var(--md-scale) * var(--md-scale)); margin-top: 0; }
main h2 { font-size: calc(1rem * var(--md-scale) * var(--md-scale) * var(--md-scale)); border-bottom: 1px solid var(--md-border); padding-bottom: 0.3em; }
main h3 { font-size: calc(1rem * var(--md-scale) * var(--md-scale)); }
main h4 { font-size: calc(1rem * var(--md-scale)); }
main h5, main h6 { font-size: 1rem; color: var(--md-text-muted); }

p { margin: 0.5em 0 1em; }
a { color: var(--md-link); text-decoration: underline; text-underline-offset: 2px; }
a:hover { color: var(--md-link-hover); }

strong { font-weight: 600; }
em { font-style: italic; }

code {
    font-family: 'JetBrains Mono', ui-monospace, SFMono-Regular, Menlo, monospace;
    background: var(--md-code-bg);
    padding: 0.15em 0.35em;
    border-radius: 4px;
    font-size: 0.9em;
}
pre {
    background: var(--md-code-bg);
    border: 1px solid var(--md-border);
    border-radius: 8px;
    padding: 1rem 1.25rem;
    overflow-x: auto;
    font-size: 0.875rem;
    line-height: 1.55;
    margin: 1.5em 0;
    position: relative;
}
pre code { background: transparent; padding: 0; font-size: 1em; }

table {
    width: 100%;
    border-collapse: collapse;
    margin: 1.5em 0;
    font-size: 0.9375rem;
}
th, td {
    border: 1px solid var(--md-border);
    padding: 0.5em 0.75em;
    text-align: left;
}
th { background: var(--md-surface); font-weight: 600; }
td.align-center, th.align-center { text-align: center; }
td.align-right, th.align-right { text-align: right; }

blockquote {
    border-left: 3px solid var(--md-border);
    margin: 1.5em 0;
    padding: 0.5em 0 0.5em 1.25em;
    color: var(--md-text-muted);
    font-style: italic;
}

ul, ol { padding-left: 1.5em; margin: 0.5em 0 1em; }
li { margin: 0.25em 0; }

hr {
    border: 0;
    border-top: 1px solid var(--md-border);
    margin: 3em 0;
}

.callout {
    border-left: 4px solid var(--md-accent);
    background: var(--md-accent-soft);
    padding: 0.75rem 1rem 0.75rem 1.25rem;
    margin: 1.5em 0;
    border-radius: 0 8px 8px 0;
}
.callout .callout-label {
    font-family: var(--md-font-heading);
    font-weight: 600;
    font-size: 0.8125rem;
    text-transform: uppercase;
    letter-spacing: 0.05em;
    margin-bottom: 0.25em;
    color: var(--md-accent);
    display: flex;
    align-items: center;
    gap: 0.5em;
}
.callout .callout-icon {
    display: inline-flex;
    width: 1.125em;
    height: 1.125em;
    align-items: center;
    justify-content: center;
}
.callout-note { border-left-color: var(--md-link); }
.callout-note .callout-label { color: var(--md-link); }
.callout-tip { border-left-color: var(--md-success); }
.callout-tip .callout-label { color: var(--md-success); }
.callout-important { border-left-color: var(--md-accent); }
.callout-warning { border-left-color: var(--md-warn); }
.callout-warning .callout-label { color: var(--md-warn); }
.callout-caution { border-left-color: var(--md-warn); }
.callout-caution .callout-label { color: var(--md-warn); }
.callout p:last-child { margin-bottom: 0; }
.callout p:first-child { margin-top: 0; }

/* TOC */
nav.toc { font-size: 0.9375rem; line-height: 1.5; }
nav.toc ol, nav.toc ul { padding-left: 1.25em; }
nav.toc a {
    color: var(--md-text-muted);
    text-decoration: none;
    display: block;
    padding: 0.15em 0.25em;
    border-radius: 3px;
}
nav.toc a:hover { color: var(--md-link); background: var(--md-accent-soft); }
nav.toc a[aria-current="location"] {
    color: var(--md-accent);
    font-weight: 600;
    background: var(--md-accent-soft);
}

/* TOC variants */
body.toc-sticky-sidebar { display: grid; grid-template-columns: 220px 1fr; gap: 2.5rem; max-width: 1200px; }
body.toc-sticky-sidebar nav.toc {
    position: sticky;
    top: 1.5rem;
    align-self: start;
    max-height: calc(100vh - 3rem);
    overflow-y: auto;
    border-right: 1px solid var(--md-border);
    padding-right: 1rem;
}
@media (max-width: 800px) {
    body.toc-sticky-sidebar { display: block; }
    body.toc-sticky-sidebar nav.toc { position: static; border-right: none; max-height: none; margin-bottom: 2rem; }
}

body.toc-collapsible-top nav.toc {
    background: var(--md-surface);
    border: 1px solid var(--md-border);
    border-radius: 8px;
    padding: 1rem 1.25rem;
    margin-bottom: 2rem;
}
body.toc-collapsible-top nav.toc summary { cursor: pointer; font-weight: 600; font-family: var(--md-font-heading); }

body.toc-none nav.toc { display: none; }

/* Search */
.md-search {
    position: sticky;
    top: 0;
    background: var(--md-bg);
    padding: 0.5rem 0 0.75rem;
    z-index: 10;
    border-bottom: 1px solid var(--md-border);
    margin-bottom: 1rem;
}
.md-search input {
    width: 100%;
    padding: 0.5rem 0.75rem;
    border: 1px solid var(--md-border);
    border-radius: 6px;
    font-size: 0.9375rem;
    background: var(--md-surface);
    color: var(--md-text);
    font-family: inherit;
}
.md-search input:focus {
    outline: 2px solid var(--md-accent);
    outline-offset: 2px;
}
main section[hidden] { display: none; }

/* Code-copy button */
.code-copy {
    position: absolute;
    top: 0.5rem;
    right: 0.5rem;
    background: var(--md-surface);
    color: var(--md-text-muted);
    border: 1px solid var(--md-border);
    border-radius: 5px;
    padding: 0.2em 0.5em;
    font-size: 0.75rem;
    cursor: pointer;
    opacity: 0;
    transition: opacity 0.15s ease;
    font-family: inherit;
}
pre:hover .code-copy { opacity: 1; }
.code-copy:hover { color: var(--md-text); background: var(--md-bg); }
.code-copy.copied { color: var(--md-success); }

/* Footer */
footer.md-footer {
    margin-top: 4rem;
    padding-top: 1.5rem;
    border-top: 1px solid var(--md-border);
    color: var(--md-text-muted);
    font-size: 0.875rem;
    display: flex;
    align-items: center;
    gap: 1rem;
}
footer.md-footer img { max-height: 24px; max-width: 120px; }

@media (prefers-reduced-motion: reduce) {
    * { animation: none !important; transition: none !important; }
    html { scroll-behavior: auto; }
}
"""


# ----- Helpers -----------------------------------------------------------------

CALLOUT_ICONS: dict[str, str] = {
    "NOTE": "i",
    "TIP": "*",
    "IMPORTANT": "!",
    "WARNING": "!",
    "CAUTION": "!",
}


def _palette_to_css(palette: dict[str, str]) -> str:
    if not palette:
        # Fallback dark-mode defaults so an un-onboarded render still works
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
    parts = "&".join(f"family={f.replace(' ', '+')}:wght@400;600" for f in families)
    return f"https://fonts.googleapis.com/css2?{parts}&display=swap"


def _font_stack(name: str, kind: str) -> str:
    fallback = ("Georgia, serif" if "serif" in name.lower() or name in
                ("Playfair Display", "Merriweather", "Lora", "Source Serif 4")
                else "system-ui, -apple-system, sans-serif")
    if "Mono" in name or "Code" in name:
        fallback = "ui-monospace, SFMono-Regular, Menlo, monospace"
    return f"'{name}', {fallback}"


def _prism_theme_link(code_theme: str) -> str:
    # auto: load both light + dark prefers-color-scheme variants
    if code_theme == "dark":
        return ('<link rel="stylesheet" '
                'href="https://cdn.jsdelivr.net/npm/prismjs@1.29.0/themes/prism-tomorrow.min.css">')
    if code_theme == "light":
        return ('<link rel="stylesheet" '
                'href="https://cdn.jsdelivr.net/npm/prismjs@1.29.0/themes/prism.min.css">')
    return (
        '<link rel="stylesheet" media="(prefers-color-scheme: light)" '
        'href="https://cdn.jsdelivr.net/npm/prismjs@1.29.0/themes/prism.min.css">\n'
        '<link rel="stylesheet" media="(prefers-color-scheme: dark)" '
        'href="https://cdn.jsdelivr.net/npm/prismjs@1.29.0/themes/prism-tomorrow.min.css">'
    )


def _embed_logo(logo_url: str) -> str:
    """Return a usable src attribute for the logo. Base64-embed local paths;
    leave URLs as-is (recipient's browser will fetch them)."""
    if not logo_url:
        return ""
    if logo_url.startswith(("data:", "http://", "https://")):
        return logo_url
    p = Path(logo_url).expanduser()
    if p.exists() and p.is_file():
        ext = p.suffix.lstrip(".").lower() or "png"
        data = base64.b64encode(p.read_bytes()).decode("ascii")
        mime = {"png": "image/png", "jpg": "image/jpeg", "jpeg": "image/jpeg",
                "svg": "image/svg+xml", "gif": "image/gif", "webp": "image/webp"}.get(
            ext, f"image/{ext}")
        return f"data:{mime};base64,{data}"
    return logo_url  # let the browser handle the broken reference visibly


def _render_block(block: dict[str, Any]) -> str:
    t = block["type"]
    if t == "heading":
        level = block["level"]
        anchor = block["anchor"]
        text = _mp.render_inline_html(block["text"]) if _mp else html.escape(block["text"])
        return f'<h{level} id="{anchor}">{text}</h{level}>'
    if t == "paragraph":
        return f"<p>{_mp.render_inline_html(block['text']) if _mp else html.escape(block['text'])}</p>"
    if t == "hr":
        return "<hr>"
    if t == "code":
        lang = block.get("language") or "text"
        # Prism class convention
        body = html.escape(block["body"])
        return f'<pre><button class="code-copy" type="button" aria-label="Copy code">Copy</button><code class="language-{html.escape(lang)}">{body}</code></pre>'
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


def _render_toc(blocks: list[dict[str, Any]], max_depth: int, behavior: str) -> str:
    if behavior == "none":
        return ""

    items = [b for b in blocks if b["type"] == "heading" and 2 <= b["level"] <= max_depth + 1]
    if not items:
        return ""

    # Group H2..H{max_depth+1} into a nested <ol> structure
    out: list[str] = []
    out.append('<nav class="toc" aria-label="Table of contents">')
    if behavior == "collapsible-top":
        out.append('<details open><summary>Contents</summary>')
    out.append("<ol>")
    last_level = 2
    for h in items:
        lvl = h["level"]
        if lvl > last_level:
            out.append("<ol>" * (lvl - last_level))
        elif lvl < last_level:
            out.append("</ol>" * (last_level - lvl))
        last_level = lvl
        out.append(f'<li><a href="#{h["anchor"]}">{html.escape(h["text"])}</a></li>')
    if last_level > 2:
        out.append("</ol>" * (last_level - 2))
    out.append("</ol>")
    if behavior == "collapsible-top":
        out.append("</details>")
    out.append("</nav>")
    return "\n".join(out)


def render(sections: dict[str, Any], config: dict[str, Any]) -> str:
    meta = sections.get("meta", {})
    blocks = sections.get("blocks", [])

    title = meta.get("title") or "Document"
    palette = config.get("derived_palette") or {}
    typo = config.get("typography") or {}
    heading_font = typo.get("heading_font", "Inter")
    body_font = typo.get("body_font", "Inter")
    scale = typo.get("scale_ratio", 1.25)
    style = config.get("design_style", "technical")
    code_theme = config.get("code_theme", "auto")
    toc_cfg = config.get("toc") or {}
    toc_behavior = toc_cfg.get("behavior", "sticky-sidebar")
    toc_max_depth = toc_cfg.get("max_depth", 3)
    company_name = config.get("company_name", "")
    logo_url = _embed_logo(config.get("logo_url", "") or "")

    css = (BASE_CSS
           .replace("__PALETTE__", _palette_to_css(palette))
           .replace("__SCALE__", str(scale))
           .replace("__HEADING_FONT__", _font_stack(heading_font, "heading"))
           .replace("__BODY_FONT__", _font_stack(body_font, "body")))
    css += STYLE_CSS_OVERRIDES.get(style, "")

    toc_html = _render_toc(blocks, toc_max_depth, toc_behavior)
    body_html = "\n".join(_render_block(b) for b in blocks)

    footer_parts: list[str] = []
    if logo_url:
        footer_parts.append(f'<img src="{html.escape(logo_url)}" alt="{html.escape(company_name or "Logo")}">')
    if company_name:
        footer_parts.append(f"<span>{html.escape(company_name)}</span>")
    footer_parts.append(f'<span style="margin-left:auto">Generated by markdown-html</span>')
    footer_html = ("<footer class=\"md-footer\">" + "".join(footer_parts) + "</footer>"
                   if footer_parts else "")

    search_html = (
        '<div class="md-search">'
        '<input type="search" id="md-search-input" '
        'placeholder="Filter sections… (Esc to clear)" '
        'aria-label="Filter document sections">'
        '</div>'
    )

    return f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{html.escape(title)}</title>
<link rel="preconnect" href="https://fonts.googleapis.com" crossorigin>
<link rel="stylesheet" href="{_font_url(heading_font, body_font)}">
{_prism_theme_link(code_theme)}
<style>{css}</style>
</head>
<body class="style-{style} toc-{toc_behavior}">
{toc_html}
<main>
{search_html}
{body_html}
{footer_html}
</main>
<script defer src="https://cdn.jsdelivr.net/npm/prismjs@1.29.0/components/prism-core.min.js"></script>
<script defer src="https://cdn.jsdelivr.net/npm/prismjs@1.29.0/plugins/autoloader/prism-autoloader.min.js"></script>
</body>
</html>"""


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--sections", help="Path to sections JSON, or '-' for stdin")
    parser.add_argument("--output", help="Path to write HTML, or '-' for stdout")
    parser.add_argument("--sample", action="store_true",
                        help="Render a built-in sample document")
    parser.add_argument("--no-config", action="store_true",
                        help="Bypass design-system config (use DEFAULTS)")
    args = parser.parse_args(argv)

    if args.sample:
        if _mp is None:
            print("error: markdown_parser not importable", file=sys.stderr)
            return 2
        sections = _mp.parse_markdown(_mp.SAMPLE_MARKDOWN)
    elif args.sections:
        raw = sys.stdin.read() if args.sections == "-" else Path(args.sections).read_text(encoding="utf-8")
        sections = json.loads(raw)
    else:
        parser.print_help()
        return 0

    if args.no_config or os.environ.get("MARKDOWN_HTML_NO_CONFIG") == "1":
        config = _cfg.DEFAULTS if _cfg else {}
    else:
        config = _cfg.load_config() if _cfg else {}

    output = render(sections, config)

    if args.output and args.output != "-":
        Path(args.output).write_text(output, encoding="utf-8")
        print(f"wrote {args.output}: {len(output):,} bytes, "
              f"{sections['meta'].get('section_count', 0)} sections")
    else:
        print(output)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
