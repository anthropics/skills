#!/usr/bin/env python3
"""WCAG 2.2 Accessibility Scanner for Frontend Codebases.

Scans HTML, JSX, TSX, Vue, Svelte, and CSS files for accessibility
violations across 10 categories: images, forms, headings, landmarks,
keyboard, ARIA, color/contrast, links, tables, and media.

Usage:
    python a11y_scanner.py /path/to/project
    python a11y_scanner.py /path/to/project --json
    python a11y_scanner.py /path/to/project --severity critical,serious
    python a11y_scanner.py /path/to/project --format json
"""

import argparse
import json
import os
import re
import sys
from dataclasses import dataclass, asdict
from typing import List, Optional


@dataclass
class Finding:
    """A single accessibility finding."""
    rule_id: str
    category: str
    severity: str
    message: str
    file: str
    line: int
    snippet: str
    wcag_criterion: str
    fix: str


# ---------------------------------------------------------------------------
# Rule definitions: each returns a list of Finding from a single file
# ---------------------------------------------------------------------------

VALID_ARIA_ATTRS = {
    "aria-activedescendant", "aria-atomic", "aria-autocomplete", "aria-busy",
    "aria-checked", "aria-colcount", "aria-colindex", "aria-colspan",
    "aria-controls", "aria-current", "aria-describedby", "aria-details",
    "aria-disabled", "aria-dropeffect", "aria-errormessage", "aria-expanded",
    "aria-flowto", "aria-grabbed", "aria-haspopup", "aria-hidden",
    "aria-invalid", "aria-keyshortcuts", "aria-label", "aria-labelledby",
    "aria-level", "aria-live", "aria-modal", "aria-multiline",
    "aria-multiselectable", "aria-orientation", "aria-owns", "aria-placeholder",
    "aria-posinset", "aria-pressed", "aria-readonly", "aria-relevant",
    "aria-required", "aria-roledescription", "aria-rowcount", "aria-rowindex",
    "aria-rowspan", "aria-selected", "aria-setsize", "aria-sort",
    "aria-valuemax", "aria-valuemin", "aria-valuenow", "aria-valuetext",
    "aria-braillelabel", "aria-brailleroledescription", "aria-description",
}

BAD_LINK_TEXT = re.compile(
    r">\s*(click here|here|read more|more|link|this)\s*<", re.IGNORECASE
)

TAG_RE = re.compile(r"<(\w[\w-]*)\b([^>]*)(/?)>", re.DOTALL)
ATTR_RE = re.compile(r"""([\w:.-]+)\s*=\s*(?:"([^"]*)"|'([^']*)'|(\S+))""")
ATTR_BOOL_RE = re.compile(r"\b([\w:.-]+)(?=\s|/?>|$)")
INLINE_COLOR_RE = re.compile(
    r'style\s*=\s*["\'][^"\']*\bcolor\s*:', re.IGNORECASE
)
ARIA_ATTR_RE = re.compile(r"\baria-[\w-]+")


def _attrs(attr_str: str) -> dict:
    """Parse HTML/JSX attribute string into a dict."""
    result = {}
    for m in ATTR_RE.finditer(attr_str):
        result[m.group(1)] = m.group(2) or m.group(3) or m.group(4) or ""
    # boolean attrs
    cleaned = ATTR_RE.sub("", attr_str)
    for m in ATTR_BOOL_RE.finditer(cleaned):
        name = m.group(1)
        if name not in result and not name.startswith("/"):
            result[name] = True
    return result


def _snippet(line_text: str) -> str:
    """Trim a line for display as a code snippet."""
    s = line_text.rstrip("\n\r")
    return s[:120] + "..." if len(s) > 120 else s


def _find(rule_id, cat, sev, msg, fp, ln, snip, wcag, fix):
    return Finding(rule_id, cat, sev, msg, fp, ln, snip, wcag, fix)


# ---------- Images ----------------------------------------------------------

def check_img_missing_alt(tag, attrs, fp, ln, snip):
    if tag == "img" and "alt" not in attrs:
        return _find("img-alt-missing", "images", "critical",
                      "<img> missing alt attribute",
                      fp, ln, snip, "1.1.1 Non-text Content",
                      "Add alt=\"description\" or alt=\"\" for decorative images.")

def check_img_empty_alt_informative(tag, attrs, fp, ln, snip):
    if tag == "img" and attrs.get("alt") == "" and attrs.get("src", ""):
        src = attrs.get("src", "")
        if not any(kw in src.lower() for kw in ("spacer", "border", "decorat", "bg")):
            return _find("img-alt-empty-informative", "images", "serious",
                          "<img> has empty alt but may be informative",
                          fp, ln, snip, "1.1.1 Non-text Content",
                          "If image conveys information, add descriptive alt text.")

def check_img_decorative_has_alt(tag, attrs, fp, ln, snip):
    if tag == "img" and attrs.get("role") == "presentation" and attrs.get("alt", "") != "":
        return _find("img-decorative-alt", "images", "moderate",
                      "Decorative image (role=presentation) should have alt=\"\"",
                      fp, ln, snip, "1.1.1 Non-text Content",
                      "Set alt=\"\" on decorative images with role=presentation.")


# ---------- Forms -----------------------------------------------------------

def check_input_missing_label(tag, attrs, fp, ln, snip):
    input_types = {"text", "email", "password", "search", "tel", "url", "number", "date"}
    if tag == "input" and attrs.get("type", "text") in input_types:
        if "aria-label" not in attrs and "aria-labelledby" not in attrs and "id" not in attrs:
            return _find("form-input-no-label", "forms", "critical",
                          "<input> has no id, aria-label, or aria-labelledby",
                          fp, ln, snip, "1.3.1 Info and Relationships",
                          "Add id + <label for>, or aria-label attribute.")

def check_input_no_aria_label(tag, attrs, fp, ln, snip):
    if tag in ("select", "textarea"):
        if "aria-label" not in attrs and "aria-labelledby" not in attrs and "id" not in attrs:
            return _find("form-select-no-label", "forms", "critical",
                          f"<{tag}> has no accessible name",
                          fp, ln, snip, "4.1.2 Name, Role, Value",
                          f"Add aria-label or id + <label for> to <{tag}>.")

def check_orphan_label(lines, fp):
    """Labels whose 'for' points to a non-existent id."""
    findings = []
    ids = set()
    label_fors = []
    for ln, line in enumerate(lines, 1):
        for m in re.finditer(r'\bid\s*=\s*["\']([^"\']+)["\']', line):
            ids.add(m.group(1))
        for m in re.finditer(r'<label[^>]*\bfor\s*=\s*["\']([^"\']+)["\']', line):
            label_fors.append((ln, m.group(1), line))
    for ln, for_val, line in label_fors:
        if for_val not in ids:
            findings.append(_find("form-orphan-label", "forms", "serious",
                                  f"<label for=\"{for_val}\"> references non-existent id",
                                  fp, ln, _snippet(line), "1.3.1 Info and Relationships",
                                  f"Ensure an element with id=\"{for_val}\" exists."))
    return findings

def check_fieldset_legend(lines, fp):
    """Radio/checkbox groups without fieldset."""
    findings = []
    radio_lines = []
    has_fieldset = any("fieldset" in l.lower() for l in lines)
    for ln, line in enumerate(lines, 1):
        if re.search(r'type\s*=\s*["\'](?:radio|checkbox)["\']', line, re.I):
            radio_lines.append((ln, line))
    if radio_lines and not has_fieldset:
        ln, line = radio_lines[0]
        findings.append(_find("form-missing-fieldset", "forms", "serious",
                              "Radio/checkbox group without <fieldset>/<legend>",
                              fp, ln, _snippet(line), "1.3.1 Info and Relationships",
                              "Wrap related radio/checkbox inputs in <fieldset> with <legend>."))
    return findings


# ---------- Headings --------------------------------------------------------

def check_headings(lines, fp):
    findings = []
    heading_levels = []
    for ln, line in enumerate(lines, 1):
        for m in re.finditer(r"<[hH]([1-6])\b", line):
            heading_levels.append((int(m.group(1)), ln, line))
    if not heading_levels:
        return findings
    # Missing h1
    levels_seen = {h[0] for h in heading_levels}
    if 1 not in levels_seen and any(l <= 3 for l in levels_seen):
        findings.append(_find("heading-missing-h1", "headings", "serious",
                              "Page has headings but no <h1>",
                              fp, heading_levels[0][1], _snippet(heading_levels[0][2]),
                              "1.3.1 Info and Relationships",
                              "Add a single <h1> as the main page heading."))
    # Multiple h1s
    h1_lines = [(ln, line) for lvl, ln, line in heading_levels if lvl == 1]
    if len(h1_lines) > 1:
        findings.append(_find("heading-multiple-h1", "headings", "moderate",
                              f"Page has {len(h1_lines)} <h1> elements",
                              fp, h1_lines[1][0], _snippet(h1_lines[1][1]),
                              "1.3.1 Info and Relationships",
                              "Use a single <h1> per page. Demote others to <h2>+."))
    # Skipped levels
    prev_level = 0
    for lvl, ln, line in heading_levels:
        if prev_level > 0 and lvl > prev_level + 1:
            findings.append(_find("heading-skipped", "headings", "moderate",
                                  f"Heading level skips from h{prev_level} to h{lvl}",
                                  fp, ln, _snippet(line),
                                  "1.3.1 Info and Relationships",
                                  f"Use <h{prev_level + 1}> instead of <h{lvl}>."))
        prev_level = lvl
    return findings


# ---------- Landmarks -------------------------------------------------------

def check_landmarks(lines, fp):
    findings = []
    content = "\n".join(lines)
    # Missing main landmark
    if not re.search(r'<main\b|role\s*=\s*["\']main["\']', content, re.I):
        findings.append(_find("landmark-no-main", "landmarks", "serious",
                              "Page missing <main> landmark",
                              fp, 1, "", "1.3.1 Info and Relationships",
                              "Add a <main> element to wrap primary content."))
    # Missing nav
    if not re.search(r'<nav\b|role\s*=\s*["\']navigation["\']', content, re.I):
        findings.append(_find("landmark-no-nav", "landmarks", "moderate",
                              "Page missing <nav> landmark",
                              fp, 1, "", "1.3.1 Info and Relationships",
                              "Add <nav> for primary navigation blocks."))
    # Missing skip link
    if not re.search(r'skip.{0,10}(nav|main|content)', content, re.I):
        findings.append(_find("landmark-no-skip-link", "landmarks", "serious",
                              "Page missing skip navigation link",
                              fp, 1, "", "2.4.1 Bypass Blocks",
                              "Add <a href=\"#main\">Skip to main content</a> as first focusable element."))
    return findings


# ---------- Keyboard --------------------------------------------------------

def check_tabindex_positive(tag, attrs, fp, ln, snip):
    ti = attrs.get("tabindex", "")
    if isinstance(ti, str) and ti.lstrip("-").isdigit() and int(ti) > 0:
        return _find("keyboard-tabindex-positive", "keyboard", "serious",
                      f"tabindex={ti} creates unexpected tab order",
                      fp, ln, snip, "2.4.3 Focus Order",
                      "Use tabindex=\"0\" or tabindex=\"-1\" instead of positive values.")

def check_click_no_keyboard(tag, attrs, fp, ln, snip):
    has_click = "onClick" in attrs or "onclick" in attrs or "@click" in attrs or "on:click" in attrs
    has_key = any(k for k in attrs if "keydown" in k.lower() or "keyup" in k.lower() or "keypress" in k.lower())
    if tag in ("div", "span", "td", "li", "p", "section") and has_click and not has_key:
        if attrs.get("role") not in ("button", "link", "tab", "menuitem"):
            return _find("keyboard-click-no-key", "keyboard", "critical",
                          f"<{tag}> has click handler but no keyboard handler",
                          fp, ln, snip, "2.1.1 Keyboard",
                          f"Add onKeyDown handler or use <button> instead of <{tag}>.")

def check_autofocus_misuse(tag, attrs, fp, ln, snip):
    if "autofocus" in attrs or "autoFocus" in attrs:
        if tag not in ("input", "textarea", "select"):
            return _find("keyboard-autofocus", "keyboard", "moderate",
                          f"autofocus on <{tag}> can disorient screen reader users",
                          fp, ln, snip, "3.2.1 On Focus",
                          "Avoid autofocus on non-input elements. Use focus management instead.")


# ---------- ARIA ------------------------------------------------------------

def check_invalid_aria(tag, attrs, fp, ln, snip):
    findings = []
    for key in attrs:
        if key.startswith("aria-") and key.lower() not in VALID_ARIA_ATTRS:
            findings.append(_find("aria-invalid-attr", "aria", "serious",
                                  f"Invalid ARIA attribute: {key}",
                                  fp, ln, snip, "4.1.2 Name, Role, Value",
                                  f"Remove or replace \"{key}\" with a valid ARIA attribute."))
    return findings

def check_aria_hidden_focusable(tag, attrs, fp, ln, snip):
    if attrs.get("aria-hidden") in ("true", True):
        focusable_tags = {"a", "button", "input", "select", "textarea"}
        if tag in focusable_tags or (isinstance(attrs.get("tabindex", ""), str) and
                                     attrs.get("tabindex", "-1") != "-1"):
            return _find("aria-hidden-focusable", "aria", "critical",
                          f"aria-hidden=\"true\" on focusable <{tag}>",
                          fp, ln, snip, "4.1.2 Name, Role, Value",
                          "Remove aria-hidden or make element non-focusable (tabindex=\"-1\").")

def check_aria_live_missing(lines, fp):
    """Alert/status roles or live regions without aria-live."""
    findings = []
    for ln, line in enumerate(lines, 1):
        if re.search(r'role\s*=\s*["\'](?:alert|status)["\']', line, re.I):
            if "aria-live" not in line:
                findings.append(_find("aria-live-missing", "aria", "serious",
                                      "role=alert/status without explicit aria-live",
                                      fp, ln, _snippet(line),
                                      "4.1.3 Status Messages",
                                      "Add aria-live=\"assertive\" (alert) or aria-live=\"polite\" (status)."))
    return findings


# ---------- Color/Contrast --------------------------------------------------

def check_inline_color(tag, attrs, fp, ln, snip):
    style = attrs.get("style", "")
    if isinstance(style, str) and re.search(r"\bcolor\s*:", style, re.I):
        if not re.search(r"background", style, re.I):
            return _find("color-inline-no-bg", "color", "moderate",
                          "Inline color set without background — contrast may be insufficient",
                          fp, ln, snip, "1.4.3 Contrast (Minimum)",
                          "Ensure foreground and background colors meet 4.5:1 contrast ratio.")

def check_text_over_image(lines, fp):
    """Detects patterns where text is positioned over background images without overlay."""
    findings = []
    for ln, line in enumerate(lines, 1):
        if re.search(r"background-image\s*:", line, re.I):
            if not re.search(r"(overlay|rgba|linear-gradient)", line, re.I):
                findings.append(_find("color-text-over-image", "color", "serious",
                                      "Background image without contrast overlay for text",
                                      fp, ln, _snippet(line),
                                      "1.4.3 Contrast (Minimum)",
                                      "Add a semi-transparent overlay or ensure text contrast."))
    return findings


# ---------- Links -----------------------------------------------------------

def check_empty_link(tag, attrs, fp, ln, snip):
    if tag == "a" and not attrs.get("aria-label") and not attrs.get("aria-labelledby"):
        return None  # handled by line-level check below

def check_empty_links_line(lines, fp):
    findings = []
    for ln, line in enumerate(lines, 1):
        # <a ...></a> or <a ...> </a>
        if re.search(r"<a\b[^>]*>\s*</a>", line, re.I):
            if "aria-label" not in line and "aria-labelledby" not in line:
                findings.append(_find("link-empty", "links", "critical",
                                      "Empty link — no text or accessible name",
                                      fp, ln, _snippet(line), "2.4.4 Link Purpose",
                                      "Add link text or aria-label."))
        # Bad link text
        if BAD_LINK_TEXT.search(line):
            findings.append(_find("link-bad-text", "links", "serious",
                                  "Link uses vague text like 'click here'",
                                  fp, ln, _snippet(line), "2.4.4 Link Purpose",
                                  "Use descriptive link text that makes sense out of context."))
    return findings

def check_same_page_link(tag, attrs, fp, ln, snip):
    href = attrs.get("href", "")
    if tag == "a" and isinstance(href, str) and href == "#":
        return _find("link-empty-fragment", "links", "moderate",
                      "Link with href=\"#\" — use a button or valid fragment",
                      fp, ln, snip, "2.4.4 Link Purpose",
                      "Use <button> for actions or href=\"#section-id\" for anchors.")


# ---------- Tables ----------------------------------------------------------

def check_table_headers(lines, fp):
    findings = []
    in_table = False
    table_start = 0
    has_th = False
    has_caption = False
    has_aria_label = False
    for ln, line in enumerate(lines, 1):
        if re.search(r"<table\b", line, re.I):
            in_table = True
            table_start = ln
            has_th = False
            has_caption = False
            has_aria_label = "aria-label" in line
        if in_table:
            if "<th" in line.lower():
                has_th = True
            if "<caption" in line.lower():
                has_caption = True
            if re.search(r"</table>", line, re.I):
                if not has_th:
                    findings.append(_find("table-no-headers", "tables", "serious",
                                          "<table> has no <th> header cells",
                                          fp, table_start, _snippet(lines[table_start - 1]),
                                          "1.3.1 Info and Relationships",
                                          "Add <th> elements to identify column/row headers."))
                if not has_caption and not has_aria_label:
                    findings.append(_find("table-no-caption", "tables", "moderate",
                                          "<table> missing <caption> or aria-label",
                                          fp, table_start, _snippet(lines[table_start - 1]),
                                          "1.3.1 Info and Relationships",
                                          "Add <caption> or aria-label to describe the table."))
                in_table = False
    return findings


# ---------- Media -----------------------------------------------------------

def check_media_captions(tag, attrs, fp, ln, snip):
    if tag == "video":
        return None  # handled at block level

def check_media_captions_block(lines, fp):
    findings = []
    in_video = False
    video_start = 0
    has_track = False
    has_controls = False
    has_autoplay = False
    for ln, line in enumerate(lines, 1):
        if re.search(r"<video\b", line, re.I):
            in_video = True
            video_start = ln
            has_track = False
            has_controls = "controls" in line.lower()
            has_autoplay = "autoplay" in line.lower()
        if in_video:
            if re.search(r'<track\b[^>]*kind\s*=\s*["\']captions["\']', line, re.I):
                has_track = True
            if "controls" in line.lower():
                has_controls = True
            if re.search(r"</video>", line, re.I) or (re.search(r"<video\b", line, re.I) and "/>" in line):
                if not has_track:
                    findings.append(_find("media-no-captions", "media", "critical",
                                          "<video> missing captions track",
                                          fp, video_start, _snippet(lines[video_start - 1]),
                                          "1.2.2 Captions (Prerecorded)",
                                          "Add <track kind=\"captions\" src=\"...\" srclang=\"en\">."))
                if has_autoplay and not has_controls:
                    findings.append(_find("media-autoplay-no-controls", "media", "serious",
                                          "<video> has autoplay without controls",
                                          fp, video_start, _snippet(lines[video_start - 1]),
                                          "1.4.2 Audio Control",
                                          "Add the controls attribute so users can pause/stop."))
                in_video = False
    # Single-line video tags
    for ln, line in enumerate(lines, 1):
        if re.search(r"<audio\b", line, re.I):
            if "autoplay" in line.lower() and "controls" not in line.lower():
                findings.append(_find("media-audio-autoplay", "media", "serious",
                                      "<audio> has autoplay without controls",
                                      fp, ln, _snippet(line), "1.4.2 Audio Control",
                                      "Add the controls attribute to <audio>."))
    return findings


# ---------------------------------------------------------------------------
# Scanner engine
# ---------------------------------------------------------------------------

SUPPORTED_EXTENSIONS = {".html", ".htm", ".jsx", ".tsx", ".vue", ".svelte", ".css"}

TAG_LEVEL_CHECKS = [
    check_img_missing_alt,
    check_img_empty_alt_informative,
    check_img_decorative_has_alt,
    check_input_missing_label,
    check_input_no_aria_label,
    check_tabindex_positive,
    check_click_no_keyboard,
    check_autofocus_misuse,
    check_aria_hidden_focusable,
    check_inline_color,
    check_same_page_link,
]

TAG_LEVEL_MULTI_CHECKS = [
    check_invalid_aria,
]


def scan_file(filepath: str) -> List[Finding]:
    """Scan a single file and return all findings."""
    findings: List[Finding] = []
    try:
        with open(filepath, "r", encoding="utf-8", errors="replace") as f:
            lines = f.readlines()
    except (OSError, IOError):
        return findings

    # Tag-level checks
    for ln, line in enumerate(lines, 1):
        for m in TAG_RE.finditer(line):
            tag = m.group(1).lower()
            attr_str = m.group(2)
            attrs = _attrs(attr_str)
            snip = _snippet(line)
            for check in TAG_LEVEL_CHECKS:
                result = check(tag, attrs, filepath, ln, snip)
                if result:
                    findings.append(result)
            for check in TAG_LEVEL_MULTI_CHECKS:
                results = check(tag, attrs, filepath, ln, snip)
                if results:
                    findings.extend(results)

    # File-level / multi-line checks
    findings.extend(check_orphan_label(lines, filepath))
    findings.extend(check_fieldset_legend(lines, filepath))
    findings.extend(check_headings(lines, filepath))
    findings.extend(check_landmarks(lines, filepath))
    findings.extend(check_aria_live_missing(lines, filepath))
    findings.extend(check_text_over_image(lines, filepath))
    findings.extend(check_empty_links_line(lines, filepath))
    findings.extend(check_table_headers(lines, filepath))
    findings.extend(check_media_captions_block(lines, filepath))

    return findings


def collect_files(path: str) -> List[str]:
    """Recursively collect scannable files under path."""
    files = []
    if os.path.isfile(path):
        _, ext = os.path.splitext(path)
        if ext.lower() in SUPPORTED_EXTENSIONS:
            files.append(path)
        return files
    for root, dirs, filenames in os.walk(path):
        # Skip common non-source directories
        dirs[:] = [d for d in dirs if d not in (
            "node_modules", ".git", "dist", "build", "__pycache__",
            ".next", ".nuxt", "vendor", "coverage"
        )]
        for fname in filenames:
            _, ext = os.path.splitext(fname)
            if ext.lower() in SUPPORTED_EXTENSIONS:
                files.append(os.path.join(root, fname))
    files.sort()
    return files


# ---------------------------------------------------------------------------
# Output formatting
# ---------------------------------------------------------------------------

SEVERITY_ORDER = {"critical": 0, "serious": 1, "moderate": 2, "minor": 3}


def format_human(findings: List[Finding], files_scanned: int) -> str:
    """Format findings as human-readable text report."""
    if not findings:
        return (f"Scanned {files_scanned} file(s) -- no accessibility issues found.\n"
                "All checks passed.")

    lines = []
    lines.append(f"WCAG 2.2 Accessibility Scan Results")
    lines.append(f"{'=' * 50}")
    lines.append(f"Files scanned: {files_scanned}")
    lines.append(f"Issues found:  {len(findings)}")

    # Summary by severity
    severity_counts = {}
    for f in findings:
        severity_counts[f.severity] = severity_counts.get(f.severity, 0) + 1
    for sev in ("critical", "serious", "moderate", "minor"):
        if sev in severity_counts:
            lines.append(f"  {sev.upper():10s}: {severity_counts[sev]}")
    lines.append("")

    # Summary by category
    cat_counts = {}
    for f in findings:
        cat_counts[f.category] = cat_counts.get(f.category, 0) + 1
    lines.append("By category:")
    for cat in sorted(cat_counts, key=lambda c: -cat_counts[c]):
        lines.append(f"  {cat:20s}: {cat_counts[cat]}")
    lines.append("")

    # Detailed findings sorted by severity then file
    sorted_findings = sorted(findings, key=lambda f: (SEVERITY_ORDER.get(f.severity, 9), f.file, f.line))
    for i, f in enumerate(sorted_findings, 1):
        lines.append(f"[{f.severity.upper()}] {f.rule_id}")
        lines.append(f"  File: {f.file}:{f.line}")
        lines.append(f"  WCAG: {f.wcag_criterion}")
        lines.append(f"  Issue: {f.message}")
        if f.snippet:
            lines.append(f"  Code:  {f.snippet}")
        lines.append(f"  Fix:   {f.fix}")
        lines.append("")

    return "\n".join(lines)


def format_json(findings: List[Finding], files_scanned: int) -> str:
    """Format findings as JSON."""
    severity_counts = {}
    for f in findings:
        severity_counts[f.severity] = severity_counts.get(f.severity, 0) + 1

    report = {
        "summary": {
            "files_scanned": files_scanned,
            "total_issues": len(findings),
            "by_severity": severity_counts,
        },
        "findings": [asdict(f) for f in findings],
    }
    return json.dumps(report, indent=2)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="a11y_scanner",
        description="Scan frontend codebases for WCAG 2.2 accessibility violations.",
        epilog=(
            "Supported file types: .html, .htm, .jsx, .tsx, .vue, .svelte, .css\n"
            "Exit codes: 0 = pass, 1 = critical/serious found, 2 = moderate/minor only"
        ),
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument(
        "path",
        help="File or directory to scan",
    )
    parser.add_argument(
        "--json", dest="json_flag", action="store_true",
        help="Output results as JSON (shorthand for --format json)",
    )
    parser.add_argument(
        "--format", dest="output_format", choices=["text", "json"],
        default="text",
        help="Output format: text (default) or json",
    )
    parser.add_argument(
        "--severity", dest="severity",
        default=None,
        help="Comma-separated severity filter (e.g. critical,serious)",
    )
    return parser


def main():
    parser = build_parser()
    args = parser.parse_args()

    path = os.path.abspath(args.path)
    if not os.path.exists(path):
        print(f"Error: path does not exist: {path}", file=sys.stderr)
        sys.exit(1)

    use_json = args.json_flag or args.output_format == "json"

    # Collect and scan files
    files = collect_files(path)
    if not files:
        print(f"No scannable files found in: {path}", file=sys.stderr)
        sys.exit(0)

    all_findings: List[Finding] = []
    for fpath in files:
        all_findings.extend(scan_file(fpath))

    # Filter by severity if requested
    if args.severity:
        allowed = {s.strip().lower() for s in args.severity.split(",")}
        all_findings = [f for f in all_findings if f.severity in allowed]

    # Output
    if use_json:
        print(format_json(all_findings, len(files)))
    else:
        print(format_human(all_findings, len(files)))

    # Exit code
    severities = {f.severity for f in all_findings}
    if severities & {"critical", "serious"}:
        sys.exit(1)
    elif severities & {"moderate", "minor"}:
        sys.exit(2)
    else:
        sys.exit(0)


if __name__ == "__main__":
    main()
