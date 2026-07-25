#!/usr/bin/env python3
"""review_html_renderer.py - Render parsed diffs + annotations into a 2-column HTML review.

Stdlib-only. Combines:
  - diff_parser.py output (hunks per file)
  - annotation_extractor.py output (severity-tagged margin notes)
  - design-system config (12-token palette + typography + design_style)

into a single-file HTML page with:

  * Top jump-nav: every annotation listed with severity badge + file:line + 1-line preview
    (Click jumps to the annotation in the right margin and highlights the hunk)
  * 2-column layout: diff on left, annotation cards on right
    (Falls back to stacked layout on viewports < 900px)
  * Per-line diff coloring: additions in success-tinted bg, deletions in warn-tinted bg
  * Severity badges: icon + color + aria-label (WCAG 1.4.1 — color is NOT the sole signal)
  * Mandatory "Reviewer:" footer (refuses to render without --reviewer)

NO LLM CALLS. Pure templating + config-driven CSS.

Single-file output: all CSS + (optional) JS inline. Only external is Google
Fonts CSS for typography (same discipline as md-document; no Prism here —
we render diff coloring ourselves with stable conventions).

Usage:
    python review_html_renderer.py \\
        --diff-blocks hunks.json \\
        --annotations annotations.json \\
        --reviewer "Jane Doe" \\
        --output review.html

    python review_html_renderer.py --sample --reviewer "Sample Reviewer" --output /tmp/review.html
"""

from __future__ import annotations

import argparse
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
    import brand_palette_validator as _bpv
except ImportError:
    _cfg = None
    _bpv = None


# ----- Severity → visual mapping (color + icon + aria-label) -------------------
# Color is NOT the sole signal (WCAG 1.4.1). Every badge has an icon and an
# aria-label that's announced by screen readers.

SEVERITY_DEFAULTS = {
    # severity_name: {token_key_in_palette, icon_text, aria_phrase}
    "BLOCKER":   {"token": "_danger", "icon": "■",  "aria": "Blocker — must fix before merge"},
    "MAJOR":     {"token": "--md-warn", "icon": "▲", "aria": "Major — strongly recommended fix"},
    "MINOR":     {"token": "--md-link", "icon": "●", "aria": "Minor — worth fixing"},
    "NIT":       {"token": "--md-text-muted", "icon": "◦", "aria": "Nit — cosmetic preference"},
}


def _derive_danger_color(palette: dict[str, str]) -> str:
    """Compute a 'danger' color by rotating the accent hue toward red.

    Falls back to a generic red if the palette is unavailable.
    """
    if not palette or _bpv is None:
        return "#D04646"
    accent_hex = palette.get("--md-accent", "#D04646")
    try:
        rgb = _bpv.parse_hex(accent_hex)
        # Rotate hue toward red (0°) — pick the shorter rotation that lands near red
        target = _bpv.shift_hue(rgb, -120)  # rotate 120° toward red
        return _bpv.rgb_to_hex(target)
    except Exception:
        return "#D04646"


def _resolve_severity_color(severity: str, palette: dict[str, str], danger: str) -> str:
    sev = severity.upper()
    spec = SEVERITY_DEFAULTS.get(sev, {"token": "--md-text-muted"})
    token = spec["token"]
    if token == "_danger":
        return danger
    return palette.get(token, "#888888")


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
    parts = "&".join(f"family={f.replace(' ', '+')}:wght@400;600" for f in families)
    return f"https://fonts.googleapis.com/css2?{parts}&display=swap"


def _font_stack(name: str) -> str:
    fallback = ("Georgia, serif" if name in
                ("Playfair Display", "Merriweather", "Lora", "Source Serif 4")
                else "system-ui, -apple-system, sans-serif")
    return f"'{name}', {fallback}"


BASE_CSS = """
:root {
__PALETTE__
    --md-danger: __DANGER__;
    --md-font-heading: __HEADING_FONT__;
    --md-font-body: __BODY_FONT__;
    --md-font-mono: 'JetBrains Mono', ui-monospace, SFMono-Regular, Menlo, monospace;
}

* { box-sizing: border-box; }
html { scroll-behavior: smooth; }
body {
    margin: 0;
    padding: 2rem 1.5rem;
    background: var(--md-bg);
    color: var(--md-text);
    font-family: var(--md-font-body);
    font-size: 16px;
    line-height: 1.55;
    max-width: 1400px;
    margin-left: auto;
    margin-right: auto;
}

h1, h2, h3 { font-family: var(--md-font-heading); color: var(--md-text); margin: 0 0 0.5em; line-height: 1.25; }
h1 { font-size: 1.75rem; }
h2 { font-size: 1.25rem; margin-top: 2rem; padding-bottom: 0.3em; border-bottom: 1px solid var(--md-border); }
a { color: var(--md-link); }

/* Severity badges (color + icon + aria-label — WCAG 1.4.1) */
.sev-badge {
    display: inline-flex;
    align-items: center;
    gap: 0.35em;
    font-family: var(--md-font-heading);
    font-weight: 600;
    font-size: 0.75rem;
    letter-spacing: 0.05em;
    padding: 0.15em 0.55em;
    border-radius: 999px;
    border: 1px solid currentColor;
    background: var(--md-bg);
}
.sev-icon { font-family: var(--md-font-mono); font-size: 0.875em; }

/* Top jump-nav */
nav.jump-nav {
    background: var(--md-surface);
    border: 1px solid var(--md-border);
    border-radius: 10px;
    padding: 1rem 1.25rem;
    margin: 1.5rem 0 2rem;
}
nav.jump-nav h2 { margin-top: 0; font-size: 1rem; border: none; padding: 0; }
nav.jump-nav ul { list-style: none; padding: 0; margin: 0.75rem 0 0; display: grid; gap: 0.4rem; }
nav.jump-nav li { display: flex; align-items: center; gap: 0.75rem; flex-wrap: wrap; }
nav.jump-nav a {
    color: var(--md-text);
    text-decoration: none;
    flex: 1;
    border-radius: 4px;
    padding: 0.2em 0.4em;
}
nav.jump-nav a:hover { background: var(--md-accent-soft); color: var(--md-accent); }
nav.jump-nav .nav-target {
    color: var(--md-text-muted);
    font-family: var(--md-font-mono);
    font-size: 0.875rem;
}
nav.jump-nav .nav-preview { color: var(--md-text-muted); font-size: 0.875rem; }

/* 2-column hunk layout */
.hunk-row {
    display: grid;
    grid-template-columns: minmax(0, 1fr) 320px;
    gap: 1.25rem;
    margin: 1.5rem 0 2rem;
    scroll-margin-top: 1rem;
}
@media (max-width: 900px) {
    .hunk-row { grid-template-columns: 1fr; }
    .hunk-annotations { order: 2; }
}

.hunk {
    background: var(--md-code-bg);
    border: 1px solid var(--md-border);
    border-radius: 8px;
    overflow: hidden;
}
.hunk-head {
    background: var(--md-surface);
    border-bottom: 1px solid var(--md-border);
    padding: 0.5rem 0.85rem;
    font-family: var(--md-font-mono);
    font-size: 0.8125rem;
    color: var(--md-text-muted);
    display: flex;
    flex-wrap: wrap;
    gap: 0.75rem;
}
.hunk-head strong { color: var(--md-text); font-weight: 600; }
.hunk pre {
    margin: 0;
    padding: 0;
    background: transparent;
    font-family: var(--md-font-mono);
    font-size: 0.8125rem;
    line-height: 1.55;
    overflow-x: auto;
}
.hunk .line {
    display: grid;
    grid-template-columns: 3.5em 3.5em 1.25em 1fr;
    padding-right: 0.75rem;
}
.hunk .ln, .hunk .lo {
    color: var(--md-text-muted);
    padding: 0 0.5em;
    text-align: right;
    user-select: none;
    border-right: 1px solid var(--md-border);
    font-size: 0.75rem;
}
.hunk .mark { text-align: center; user-select: none; color: var(--md-text-muted); }
.hunk .src { padding-left: 0.5em; white-space: pre; overflow-wrap: normal; }
.hunk .line.addition { background: color-mix(in srgb, var(--md-success) 15%, transparent); }
.hunk .line.addition .mark { color: var(--md-success); }
.hunk .line.deletion { background: color-mix(in srgb, var(--md-warn) 12%, transparent); }
.hunk .line.deletion .mark { color: var(--md-warn); }
.hunk .line.meta { color: var(--md-text-muted); font-style: italic; padding-left: 1em; }

/* Annotation cards on the right */
.hunk-annotations { display: grid; gap: 0.75rem; align-content: start; }
.annotation {
    background: var(--md-surface);
    border: 1px solid var(--md-border);
    border-left-width: 4px;
    border-radius: 8px;
    padding: 0.75rem 0.85rem;
}
.annotation .annotation-head {
    display: flex;
    justify-content: space-between;
    align-items: center;
    gap: 0.5rem;
    margin-bottom: 0.4rem;
}
.annotation .annotation-body { font-size: 0.9375rem; line-height: 1.5; color: var(--md-text); }
.annotation .annotation-body code {
    font-family: var(--md-font-mono);
    background: var(--md-code-bg);
    padding: 0.1em 0.3em;
    border-radius: 4px;
    font-size: 0.875em;
}
.annotation.unanchored { border-left-color: var(--md-text-muted); }

/* Reviewer footer */
footer.review-footer {
    margin-top: 3rem;
    padding-top: 1.5rem;
    border-top: 1px solid var(--md-border);
    color: var(--md-text-muted);
    font-size: 0.9375rem;
    display: flex;
    align-items: center;
    gap: 1rem;
    flex-wrap: wrap;
}
footer.review-footer strong { color: var(--md-text); }

/* Approval bar (LGTM markers) */
.approval-bar {
    background: color-mix(in srgb, var(--md-success) 12%, transparent);
    border: 1px solid var(--md-success);
    color: var(--md-success);
    padding: 0.5rem 0.85rem;
    border-radius: 8px;
    margin: 1rem 0;
    font-weight: 600;
    font-family: var(--md-font-heading);
}

@media (prefers-reduced-motion: reduce) {
    * { animation: none !important; transition: none !important; }
    html { scroll-behavior: auto; }
}
"""


def _hunk_anchor(block_idx: int, file_idx: int, hunk_idx: int) -> str:
    return f"hunk-b{block_idx}-f{file_idx}-h{hunk_idx}"


def _annotation_anchor(idx: int) -> str:
    return f"ann-{idx}"


def _render_severity_badge(severity: str, palette: dict[str, str], danger: str) -> str:
    spec = SEVERITY_DEFAULTS.get(severity.upper(), {"icon": "?", "aria": severity})
    color = _resolve_severity_color(severity, palette, danger)
    icon = html.escape(spec["icon"])
    aria = html.escape(spec["aria"])
    return (
        f'<span class="sev-badge" style="color: {color}" '
        f'role="status" aria-label="{aria}">'
        f'<span class="sev-icon" aria-hidden="true">{icon}</span>'
        f'{html.escape(severity.upper())}'
        f'</span>'
    )


def _render_hunk(file_idx: int, file_entry: dict[str, Any],
                 block_idx: int, hunk_idx: int) -> str:
    h = file_entry["hunks"][hunk_idx]
    path = file_entry.get("path_new") or file_entry.get("path_old") or "(unknown)"
    anchor = _hunk_anchor(block_idx, file_idx, hunk_idx)
    head = (
        f'<div class="hunk-head">'
        f'<strong>{html.escape(path)}</strong>'
        f'<span>@{h["old_start"]}{html.escape(" → ")}@{h["new_start"]}</span>'
        f'<span>{html.escape(h.get("header_context") or "")}</span>'
        f'</div>'
    )
    body_lines = []
    for ln in h["lines"]:
        kind = ln["kind"]
        mark = {"addition": "+", "deletion": "−", "context": " ", "meta": "\\"}.get(kind, " ")
        old = "" if ln.get("old") is None else str(ln["old"])
        new = "" if ln.get("new") is None else str(ln["new"])
        body_lines.append(
            f'<div class="line {kind}">'
            f'<span class="lo">{old}</span>'
            f'<span class="ln">{new}</span>'
            f'<span class="mark" aria-hidden="true">{mark}</span>'
            f'<span class="src">{html.escape(ln["text"])}</span>'
            f'</div>'
        )
    return (
        f'<div class="hunk" id="{anchor}">'
        f'{head}<pre>{"".join(body_lines)}</pre></div>'
    )


def _render_annotation(idx: int, ann: dict[str, Any],
                       palette: dict[str, str], danger: str,
                       anchor_for_block: dict[int, str]) -> str:
    color = _resolve_severity_color(ann["severity"], palette, danger)
    anchor_target = anchor_for_block.get(ann.get("attached_block"))
    target_link = (
        f'<a href="#{anchor_target}" '
        f'style="color: var(--md-text-muted); font-size: 0.75rem; '
        f'text-decoration: none">jump to diff →</a>'
        if anchor_target else ""
    )
    body = html.escape(ann["body"])
    # Re-inflate inline `code` for readability
    body = body.replace("`", "<code>", 1)
    while "<code>" in body and body.count("<code>") > body.count("</code>"):
        body = body.replace("`", "</code>", 1)
    return (
        f'<div class="annotation{" unanchored" if anchor_target is None else ""}" '
        f'id="{_annotation_anchor(idx)}" style="border-left-color: {color}">'
        f'<div class="annotation-head">'
        f'{_render_severity_badge(ann["severity"], palette, danger)}'
        f'{target_link}'
        f'</div>'
        f'<div class="annotation-body">{body}</div>'
        f'</div>'
    )


def render(
    diff_blocks: dict[str, Any],
    annotations: dict[str, Any],
    config: dict[str, Any],
    reviewer: str,
    pr_title: str = "Code Review",
) -> str:
    palette = config.get("derived_palette") or {}
    typo = config.get("typography") or {}
    heading_font = typo.get("heading_font", "Inter")
    body_font = typo.get("body_font", "Inter")
    style = config.get("design_style", "technical")
    company_name = config.get("company_name", "")

    danger = _derive_danger_color(palette)

    css = (BASE_CSS
           .replace("__PALETTE__", _palette_to_css(palette))
           .replace("__DANGER__", danger)
           .replace("__HEADING_FONT__", _font_stack(heading_font))
           .replace("__BODY_FONT__", _font_stack(body_font)))

    # Build anchor map for jump-nav targets
    anchor_for_block: dict[int, str] = {}
    for block in diff_blocks.get("blocks", []):
        block_idx = block["block_index"]
        for file_idx, file_entry in enumerate(block["files"]):
            if file_entry["hunks"]:
                # Anchor the first hunk of the first file in each block
                anchor_for_block.setdefault(
                    block_idx, _hunk_anchor(block_idx, file_idx, 0)
                )

    # Top jump-nav (ordered by source position, which is annotation order)
    annlist = annotations.get("annotations", [])
    nav_items_html: list[str] = []
    for i, ann in enumerate(annlist):
        target_anchor = _annotation_anchor(i)
        target_diff = anchor_for_block.get(ann.get("attached_block")) or target_anchor
        preview = html.escape(ann["body"][:80] + ("…" if len(ann["body"]) > 80 else ""))
        target_label = (
            f'#{ann.get("attached_block") + 1}' if ann.get("attached_block") is not None
            else "(unanchored)"
        )
        nav_items_html.append(
            f'<li>'
            f'{_render_severity_badge(ann["severity"], palette, danger)}'
            f'<a href="#{target_anchor}">{preview}</a>'
            f'<span class="nav-target">{html.escape(target_label)}</span>'
            f'</li>'
        )

    jump_nav_html = ""
    if annlist:
        counts = annotations.get("summary", {}).get("counts_by_severity", {})
        count_summary = " · ".join(
            f"{n} {sev}" for sev, n in sorted(counts.items())
        )
        jump_nav_html = (
            '<nav class="jump-nav" aria-label="Review annotations">'
            f'<h2>Findings ({count_summary})</h2>'
            f'<ul>{"".join(nav_items_html)}</ul>'
            '</nav>'
        )

    # Approval bar (LGTM markers)
    approvals = annotations.get("approvals", [])
    approval_html = ""
    if approvals and not annlist:
        approval_html = (
            '<div class="approval-bar" role="status">'
            'LGTM — no findings flagged'
            '</div>'
        )

    # Render hunks + their attached annotations
    block_to_annotations: dict[int, list[tuple[int, dict[str, Any]]]] = {}
    unanchored: list[tuple[int, dict[str, Any]]] = []
    for i, ann in enumerate(annlist):
        if ann.get("attached_block") is not None:
            block_to_annotations.setdefault(ann["attached_block"], []).append((i, ann))
        else:
            unanchored.append((i, ann))

    sections_html: list[str] = []
    for block in diff_blocks.get("blocks", []):
        block_idx = block["block_index"]
        anns_for_block = block_to_annotations.get(block_idx, [])
        for file_idx, file_entry in enumerate(block["files"]):
            for hunk_idx in range(len(file_entry["hunks"])):
                hunk_html = _render_hunk(file_idx, file_entry, block_idx, hunk_idx)
                # All annotations for this block render alongside the first hunk
                ann_html = ""
                if file_idx == 0 and hunk_idx == 0 and anns_for_block:
                    ann_html = "".join(
                        _render_annotation(i, ann, palette, danger, anchor_for_block)
                        for i, ann in anns_for_block
                    )
                sections_html.append(
                    '<div class="hunk-row">'
                    f'{hunk_html}'
                    f'<div class="hunk-annotations">{ann_html}</div>'
                    '</div>'
                )

    if unanchored:
        sections_html.append('<h2>General comments</h2>')
        sections_html.append('<div class="hunk-annotations">')
        for i, ann in unanchored:
            sections_html.append(
                _render_annotation(i, ann, palette, danger, anchor_for_block)
            )
        sections_html.append('</div>')

    # Footer with mandatory reviewer name
    footer_html = (
        '<footer class="review-footer">'
        f'<span>Reviewer: <strong>{html.escape(reviewer)}</strong></span>'
        + (f'<span>· {html.escape(company_name)}</span>' if company_name else "")
        + '<span style="margin-left:auto">Generated by markdown-html / md-review</span>'
        '</footer>'
    )

    return f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{html.escape(pr_title)}</title>
<link rel="preconnect" href="https://fonts.googleapis.com" crossorigin>
<link rel="stylesheet" href="{_font_url(heading_font, body_font)}">
<style>{css}</style>
</head>
<body class="style-{style}">
<header><h1>{html.escape(pr_title)}</h1></header>
{jump_nav_html}
{approval_html}
{"".join(sections_html)}
{footer_html}
</body>
</html>"""


def main(argv: list[str]) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("--diff-blocks", help="Path to diff_parser JSON output")
    p.add_argument("--annotations", help="Path to annotation_extractor JSON output")
    p.add_argument("--reviewer", help="Reviewer name (required; refuses to render without)")
    p.add_argument("--title", default="Code Review", help="PR / review title")
    p.add_argument("--output", help="Path to write HTML (else stdout)")
    p.add_argument("--no-config", action="store_true",
                   help="Bypass design-system config (use DEFAULTS)")
    p.add_argument("--sample", action="store_true",
                   help="Render the built-in sample PR review")
    p.add_argument("--severity-convention",
                   default="BLOCKER,MAJOR,MINOR,NIT",
                   help="Comma-separated severity tier list (most → least)")
    args = p.parse_args(argv)

    if args.sample:
        sys.path.insert(0, str(Path(__file__).resolve().parent))
        import annotation_extractor
        import diff_parser
        text = diff_parser.SAMPLE_MARKDOWN
        diff_blocks = diff_parser.parse_markdown_for_diffs(text)
        sev_conv = [s.strip().upper() for s in args.severity_convention.split(",")]
        annotations = annotation_extractor.extract_annotations(text, diff_blocks, sev_conv)
        reviewer = args.reviewer or "Sample Reviewer"
        pr_title = args.title
    else:
        if not (args.diff_blocks and args.annotations):
            print("error: --diff-blocks and --annotations are required "
                  "(use --sample for a built-in demo)", file=sys.stderr)
            return 2
        diff_blocks = json.loads(Path(args.diff_blocks).read_text(encoding="utf-8"))
        annotations = json.loads(Path(args.annotations).read_text(encoding="utf-8"))
        reviewer = args.reviewer
        pr_title = args.title

    # Hard rule 1: reviewer name is mandatory (named owner per research-ops discipline)
    if not reviewer or not reviewer.strip():
        print("refusing: --reviewer is required. A code review must name a human reviewer.",
              file=sys.stderr)
        return 3

    # Hard rule 2: refuse if there are no hunks (wrong skill — route to md-document)
    if diff_blocks.get("summary", {}).get("total_hunks", 0) == 0:
        print("refusing: no diff hunks present in input. This is not a code review — "
              "route to md-document instead.", file=sys.stderr)
        return 4

    if args.no_config or os.environ.get("MARKDOWN_HTML_NO_CONFIG") == "1":
        config = _cfg.DEFAULTS if _cfg else {}
    else:
        config = _cfg.load_config() if _cfg else {}

    output = render(diff_blocks, annotations, config, reviewer, pr_title)

    if args.output and args.output != "-":
        Path(args.output).write_text(output, encoding="utf-8")
        print(f"wrote {args.output}: {len(output):,} bytes "
              f"({diff_blocks['summary']['total_hunks']} hunks, "
              f"{annotations['summary']['total_annotations']} annotations, "
              f"reviewer={reviewer})")
    else:
        print(output)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
