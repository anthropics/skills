#!/usr/bin/env python3
"""SEO + AEO audit for a single public URL.

See ../SKILL.md for when and how to use this. See
../reference/checklist.md for the check catalog.

Uses only the Python 3 standard library.
"""

from __future__ import annotations

import argparse
import ipaddress
import json
import re
import sys
import textwrap
import urllib.parse
import urllib.request
from dataclasses import dataclass, field
from html.parser import HTMLParser
from typing import Callable

USER_AGENT = "seo-aeo-audit/1.0 (+https://github.com/anthropics/skills)"
FETCH_TIMEOUT = 15


# ------------------------------------------------------------------ #
# Result model
# ------------------------------------------------------------------ #


@dataclass
class Finding:
    check: str
    family: str  # "seo" | "aeo"
    severity: str  # "error" | "warn" | "info" | "ok"
    message: str
    fix: str | None = None


@dataclass
class Page:
    url: str
    final_url: str
    status: int
    headers: dict[str, str]
    html: str
    title: str | None = None
    meta: dict[str, str] = field(default_factory=dict)
    links: list[dict[str, str]] = field(default_factory=list)
    headings: list[tuple[int, str]] = field(default_factory=list)
    images: list[dict[str, str]] = field(default_factory=list)
    scripts: list[dict[str, str]] = field(default_factory=list)
    html_lang: str | None = None
    canonical: str | None = None
    jsonld: list[dict] = field(default_factory=list)
    first_paragraph: str | None = None
    paragraphs: list[str] = field(default_factory=list)
    has_article: bool = False
    has_main: bool = False
    has_nav: bool = False
    has_section: bool = False


# ------------------------------------------------------------------ #
# HTML parsing
# ------------------------------------------------------------------ #


class _Parser(HTMLParser):
    def __init__(self, page: Page) -> None:
        super().__init__(convert_charrefs=True)
        self.page = page
        self._stack: list[str] = []
        self._collect: str | None = None
        self._buffer: list[str] = []
        self._current_heading_level: int | None = None
        self._current_script_attrs: dict[str, str] | None = None

    def handle_starttag(self, tag: str, attrs_list: list[tuple[str, str | None]]) -> None:
        attrs = {k.lower(): (v or "") for k, v in attrs_list}
        self._stack.append(tag)

        if tag == "html":
            if "lang" in attrs:
                self.page.html_lang = attrs["lang"]
        elif tag == "title":
            self._collect = "title"
            self._buffer = []
        elif tag == "meta":
            name = attrs.get("name") or attrs.get("property") or attrs.get("http-equiv")
            if name:
                self.page.meta[name.lower()] = attrs.get("content", "")
        elif tag == "link":
            rel = attrs.get("rel", "").lower()
            entry = {"rel": rel, **{k: v for k, v in attrs.items() if k != "rel"}}
            self.page.links.append(entry)
            if rel == "canonical":
                self.page.canonical = attrs.get("href")
        elif tag in ("h1", "h2", "h3", "h4", "h5", "h6"):
            self._collect = "heading"
            self._current_heading_level = int(tag[1])
            self._buffer = []
        elif tag == "img":
            self.page.images.append(
                {
                    "src": attrs.get("src", ""),
                    "alt": attrs.get("alt", None) if "alt" in attrs else None,
                    "width": attrs.get("width", ""),
                    "height": attrs.get("height", ""),
                    "loading": attrs.get("loading", ""),
                }
            )
        elif tag == "script":
            self._current_script_attrs = attrs
            script_type = attrs.get("type", "").lower()
            if script_type == "application/ld+json":
                self._collect = "jsonld"
                self._buffer = []
            else:
                self.page.scripts.append(
                    {
                        "src": attrs.get("src", ""),
                        "async": "async" in attrs,
                        "defer": "defer" in attrs,
                        "type": script_type,
                    }
                )
        elif tag == "p":
            self._collect = "paragraph"
            self._buffer = []
        elif tag == "article":
            self.page.has_article = True
        elif tag == "main":
            self.page.has_main = True
        elif tag == "nav":
            self.page.has_nav = True
        elif tag == "section":
            self.page.has_section = True

    def handle_endtag(self, tag: str) -> None:
        if self._stack and self._stack[-1] == tag:
            self._stack.pop()
        text = "".join(self._buffer).strip()
        if self._collect == "title" and tag == "title":
            self.page.title = text
            self._collect = None
            self._buffer = []
        elif self._collect == "heading" and tag in ("h1", "h2", "h3", "h4", "h5", "h6"):
            self.page.headings.append((self._current_heading_level or 0, text))
            self._collect = None
            self._current_heading_level = None
            self._buffer = []
        elif self._collect == "jsonld" and tag == "script":
            self._parse_jsonld(text)
            self._collect = None
            self._buffer = []
        elif self._collect == "paragraph" and tag == "p":
            if text:
                self.page.paragraphs.append(text)
                if self.page.first_paragraph is None:
                    self.page.first_paragraph = text
            self._collect = None
            self._buffer = []

    def handle_data(self, data: str) -> None:
        if self._collect:
            self._buffer.append(data)

    def _parse_jsonld(self, text: str) -> None:
        if not text.strip():
            return
        try:
            parsed = json.loads(text)
        except json.JSONDecodeError:
            self.page.jsonld.append({"@type": "__invalid__", "_raw": text[:200]})
            return
        blocks = parsed if isinstance(parsed, list) else [parsed]
        for block in blocks:
            if isinstance(block, dict):
                self.page.jsonld.append(block)


# ------------------------------------------------------------------ #
# Fetching
# ------------------------------------------------------------------ #


class AuditError(Exception):
    pass


def _is_private_target(url: str) -> str | None:
    """Return a rejection reason if `url` targets a private host, else None."""
    parsed = urllib.parse.urlparse(url)
    if parsed.scheme not in ("http", "https"):
        return f"unsupported scheme: {parsed.scheme!r}"
    host = (parsed.hostname or "").strip().lower()
    if not host:
        return "no hostname"
    if host in ("localhost",) or host.endswith(".local") or host.endswith(".internal"):
        return f"private hostname: {host}"
    try:
        addr = ipaddress.ip_address(host)
        if addr.is_private or addr.is_loopback or addr.is_link_local or addr.is_reserved:
            return f"private IP: {host}"
    except ValueError:
        pass
    return None


def fetch(url: str) -> Page:
    reason = _is_private_target(url)
    if reason:
        raise AuditError(f"refusing to audit non-public URL — {reason}")
    req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT, "Accept": "text/html,*/*;q=0.5"})
    try:
        with urllib.request.urlopen(req, timeout=FETCH_TIMEOUT) as resp:
            final_url = resp.geturl()
            status = resp.status
            headers = {k.lower(): v for k, v in resp.headers.items()}
            raw = resp.read()
    except urllib.error.HTTPError as e:
        raise AuditError(f"HTTP {e.code} fetching {url}: {e.reason}") from e
    except urllib.error.URLError as e:
        raise AuditError(f"network error fetching {url}: {e.reason}") from e

    encoding = _detect_encoding(headers, raw)
    html = raw.decode(encoding, errors="replace")
    page = Page(url=url, final_url=final_url, status=status, headers=headers, html=html)
    parser = _Parser(page)
    parser.feed(html)
    return page


def _detect_encoding(headers: dict[str, str], raw: bytes) -> str:
    ct = headers.get("content-type", "")
    match = re.search(r"charset=([\w-]+)", ct, re.I)
    if match:
        return match.group(1)
    match = re.search(rb'<meta[^>]+charset=["\']?([\w-]+)', raw[:2048], re.I)
    if match:
        try:
            return match.group(1).decode("ascii")
        except UnicodeDecodeError:
            pass
    return "utf-8"


def fetch_optional(url: str) -> tuple[int, str] | None:
    reason = _is_private_target(url)
    if reason:
        return None
    req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    try:
        with urllib.request.urlopen(req, timeout=FETCH_TIMEOUT) as resp:
            return resp.status, resp.read().decode("utf-8", errors="replace")
    except Exception:
        return None


# ------------------------------------------------------------------ #
# Checks
# ------------------------------------------------------------------ #

CheckFn = Callable[[Page], list[Finding]]
CHECKS: list[tuple[str, str, CheckFn]] = []


def check(name: str, family: str) -> Callable[[CheckFn], CheckFn]:
    def wrap(fn: CheckFn) -> CheckFn:
        CHECKS.append((name, family, fn))
        return fn

    return wrap


# ---- SEO checks --------------------------------------------------- #


@check("title-tag", "seo")
def _c_title(page: Page) -> list[Finding]:
    if not page.title:
        return [Finding("title-tag", "seo", "error", "missing <title> tag", "Add a descriptive <title> in <head>, 30–60 chars.")]
    n = len(page.title)
    if n < 30:
        return [Finding("title-tag", "seo", "warn", f"title is {n} chars; recommended 30–60", "Add specificity or a brand suffix.")]
    if n > 60:
        return [Finding("title-tag", "seo", "warn", f"title is {n} chars; will truncate in SERP (>60)", "Trim to under 60 chars, front-load the keyword.")]
    return [Finding("title-tag", "seo", "ok", f"title present, {n} chars")]


@check("meta-description", "seo")
def _c_meta_desc(page: Page) -> list[Finding]:
    desc = page.meta.get("description", "")
    if not desc:
        return [Finding("meta-description", "seo", "error", "missing <meta name=description>", "Add a 70–160 char description that summarises the page.")]
    n = len(desc)
    if n < 70:
        return [Finding("meta-description", "seo", "warn", f"meta description is {n} chars; recommended 70–160")]
    if n > 160:
        return [Finding("meta-description", "seo", "warn", f"meta description is {n} chars; SERP truncates >160")]
    return [Finding("meta-description", "seo", "ok", f"meta description present, {n} chars")]


@check("robots-directive", "seo")
def _c_robots(page: Page) -> list[Finding]:
    robots = page.meta.get("robots", "").lower()
    x_robots = page.headers.get("x-robots-tag", "").lower()
    combined = f"{robots} {x_robots}".strip()
    findings = []
    if "noindex" in combined:
        findings.append(Finding("robots-directive", "seo", "error", f"page is noindex ({combined!r}) — will not appear in search",
                                "Remove `noindex` unless the page is intentionally excluded."))
    if "nofollow" in combined:
        findings.append(Finding("robots-directive", "seo", "warn", f"page is nofollow ({combined!r}) — outbound links do not pass authority"))
    if not findings:
        findings.append(Finding("robots-directive", "seo", "ok", "no noindex/nofollow"))
    return findings


@check("canonical", "seo")
def _c_canonical(page: Page) -> list[Finding]:
    if not page.canonical:
        return [Finding("canonical", "seo", "warn", "no <link rel=canonical> declared",
                        "Add <link rel=\"canonical\" href=\"…\"> pointing at the preferred URL.")]
    if not page.canonical.startswith(("http://", "https://")):
        return [Finding("canonical", "seo", "warn", f"canonical is relative: {page.canonical!r}", "Use an absolute URL.")]
    canon = urllib.parse.urlparse(page.canonical)
    final = urllib.parse.urlparse(page.final_url)
    if canon.netloc != final.netloc:
        return [Finding("canonical", "seo", "info", f"canonical points to a different host: {page.canonical!r} (fetched from {final.netloc})")]
    return [Finding("canonical", "seo", "ok", f"canonical present: {page.canonical}")]


@check("h1-hierarchy", "seo")
def _c_h1(page: Page) -> list[Finding]:
    h1s = [h for lvl, h in page.headings if lvl == 1]
    findings: list[Finding] = []
    if not h1s:
        findings.append(Finding("h1-hierarchy", "seo", "error", "no <h1> on the page", "Add exactly one <h1> naming the page topic."))
    elif len(h1s) > 1:
        findings.append(Finding("h1-hierarchy", "seo", "warn", f"{len(h1s)} <h1> tags found; recommended: exactly one"))
    else:
        findings.append(Finding("h1-hierarchy", "seo", "ok", f"one <h1>: {h1s[0][:80]!r}"))
    # heading level jumps
    levels = [lvl for lvl, _ in page.headings]
    for a, b in zip(levels, levels[1:]):
        if b > a + 1:
            findings.append(Finding("h1-hierarchy", "seo", "warn", f"heading level jumps h{a} → h{b}",
                                     "Keep the outline monotone — do not skip levels."))
            break
    return findings


@check("html-lang", "seo")
def _c_lang(page: Page) -> list[Finding]:
    if not page.html_lang:
        return [Finding("html-lang", "seo", "warn", "<html> missing lang attribute", 'Add e.g. <html lang="en">.')]
    return [Finding("html-lang", "seo", "ok", f"html lang={page.html_lang!r}")]


@check("open-graph", "seo")
def _c_og(page: Page) -> list[Finding]:
    required = ["og:title", "og:description", "og:image", "og:url", "og:type"]
    missing = [k for k in required if not page.meta.get(k)]
    if missing:
        return [Finding("open-graph", "seo", "warn", f"missing Open Graph tags: {', '.join(missing)}",
                        "Complete the OG set so link previews render correctly on social + chat.")]
    return [Finding("open-graph", "seo", "ok", "all five core OG tags present")]


@check("twitter-card", "seo")
def _c_twitter(page: Page) -> list[Finding]:
    if not page.meta.get("twitter:card"):
        return [Finding("twitter-card", "seo", "info", "no twitter:card declared", "Add <meta name=\"twitter:card\" content=\"summary_large_image\">.")]
    return [Finding("twitter-card", "seo", "ok", f"twitter:card = {page.meta.get('twitter:card')!r}")]


@check("image-alt", "seo")
def _c_img_alt(page: Page) -> list[Finding]:
    total = len(page.images)
    if total == 0:
        return [Finding("image-alt", "seo", "info", "no <img> tags on the page")]
    missing = [i for i in page.images if i["alt"] is None]
    if missing:
        return [Finding("image-alt", "seo", "warn", f"{len(missing)}/{total} images have no alt attribute at all",
                        "Add alt=\"…\" — use alt=\"\" only for purely decorative images.")]
    return [Finding("image-alt", "seo", "ok", f"all {total} images have an alt attribute")]


@check("https", "seo")
def _c_https(page: Page) -> list[Finding]:
    if not page.final_url.startswith("https://"):
        return [Finding("https", "seo", "error", f"page served over HTTP: {page.final_url}", "Serve over HTTPS with a valid cert.")]
    return [Finding("https", "seo", "ok", "HTTPS")]


# ---- AEO checks --------------------------------------------------- #


@check("first-paragraph-answer", "aeo")
def _c_first_para(page: Page) -> list[Finding]:
    p = (page.first_paragraph or "").strip()
    if not p:
        return [Finding("first-paragraph-answer", "aeo", "warn", "no <p> content found in body",
                        "Lead the page with a self-contained 2–4 sentence answer.")]
    words = len(p.split())
    if words < 15:
        return [Finding("first-paragraph-answer", "aeo", "warn", f"first paragraph is only {words} words — too short to be a self-contained answer",
                        "Rewrite the intro so a first-time reader gets the answer in one paragraph.")]
    if words > 120:
        return [Finding("first-paragraph-answer", "aeo", "warn", f"first paragraph is {words} words — too long for extraction",
                        "Split the intro; keep the leading paragraph at 2–4 tight sentences.")]
    return [Finding("first-paragraph-answer", "aeo", "ok", f"first paragraph is {words} words")]


@check("question-shaped-headings", "aeo")
def _c_question_headings(page: Page) -> list[Finding]:
    lower_headings = [(lvl, h) for lvl, h in page.headings if lvl in (2, 3)]
    if not lower_headings:
        return [Finding("question-shaped-headings", "aeo", "info", "no h2/h3 headings to evaluate")]
    question = [h for _, h in lower_headings if h.strip().endswith("?") or _looks_like_question(h)]
    ratio = len(question) / len(lower_headings)
    if ratio < 0.2:
        return [Finding("question-shaped-headings", "aeo", "warn",
                        f"only {len(question)}/{len(lower_headings)} h2/h3 are question-shaped",
                        "Reframe at least a third of subheadings as the real question the section answers.")]
    return [Finding("question-shaped-headings", "aeo", "ok", f"{len(question)}/{len(lower_headings)} h2/h3 are question-shaped")]


_QUESTION_STARTERS = ("how ", "what ", "why ", "when ", "where ", "which ", "who ", "can ", "should ", "is ", "are ", "do ", "does ")


def _looks_like_question(h: str) -> bool:
    return h.strip().lower().startswith(_QUESTION_STARTERS)


@check("structured-data-jsonld", "aeo")
def _c_jsonld(page: Page) -> list[Finding]:
    findings: list[Finding] = []
    invalid = [b for b in page.jsonld if b.get("@type") == "__invalid__"]
    if invalid:
        findings.append(Finding("structured-data-jsonld", "aeo", "error",
                                f"{len(invalid)} JSON-LD block(s) failed to parse", "Validate the JSON-LD payload; missing quotes/commas are the usual cause."))
    types = sorted({_extract_type(b) for b in page.jsonld if b.get("@type") != "__invalid__"})
    if not page.jsonld:
        findings.append(Finding("structured-data-jsonld", "aeo", "warn",
                                "no JSON-LD structured data",
                                "Add JSON-LD for the page type: Article, Product, FAQPage, HowTo, Organization, etc."))
    else:
        findings.append(Finding("structured-data-jsonld", "aeo", "ok",
                                f"JSON-LD @types present: {', '.join(t for t in types if t)}"))
    return findings


def _extract_type(block: dict) -> str:
    t = block.get("@type", "")
    if isinstance(t, list):
        return ",".join(t)
    return str(t)


@check("faq-qa-schema", "aeo")
def _c_faq(page: Page) -> list[Finding]:
    types = {_extract_type(b) for b in page.jsonld}
    has_faq = any("FAQPage" in t or "QAPage" in t for t in types)
    q_marks = sum(1 for _, h in page.headings if h.strip().endswith("?"))
    if q_marks >= 3 and not has_faq:
        return [Finding("faq-qa-schema", "aeo", "warn",
                        f"page has {q_marks} question-shaped headings but no FAQPage/QAPage schema",
                        "Add FAQPage JSON-LD — a direct extractability win for answer engines.")]
    if has_faq:
        return [Finding("faq-qa-schema", "aeo", "ok", "FAQPage/QAPage schema present")]
    return [Finding("faq-qa-schema", "aeo", "info", "no Q&A schema (page doesn't appear to be FAQ-shaped)")]


@check("entity-clarity", "aeo")
def _c_entity(page: Page) -> list[Finding]:
    ent_types = ("Organization", "Person", "Product", "SoftwareApplication", "LocalBusiness")
    matches = [b for b in page.jsonld if any(t in _extract_type(b) for t in ent_types)]
    if not matches:
        return [Finding("entity-clarity", "aeo", "info",
                        "no entity schema (Organization/Person/Product/SoftwareApplication/LocalBusiness)",
                        "Add entity JSON-LD with sameAs links to Wikidata / LinkedIn / GitHub etc. so engines de-ambiguate.")]
    has_sameas = any(b.get("sameAs") for b in matches)
    if not has_sameas:
        return [Finding("entity-clarity", "aeo", "warn",
                        "entity schema present but no sameAs links",
                        "Add sameAs = [wikidata, linkedin, github, …] so engines can link the entity to its canonical record.")]
    return [Finding("entity-clarity", "aeo", "ok", "entity schema with sameAs is present")]


@check("semantic-html", "aeo")
def _c_semantic(page: Page) -> list[Finding]:
    missing = []
    if not page.has_main:
        missing.append("<main>")
    if not (page.has_article or page.has_section):
        missing.append("<article> or <section>")
    if missing:
        return [Finding("semantic-html", "aeo", "warn",
                        f"missing semantic landmarks: {', '.join(missing)}",
                        "Wrap primary content in <main> and use <article>/<section> for logical blocks.")]
    return [Finding("semantic-html", "aeo", "ok", "semantic landmarks present")]


@check("dated-content", "aeo")
def _c_dated(page: Page) -> list[Finding]:
    has_date_meta = any(k for k in page.meta if "date" in k or "modified" in k or "published" in k)
    has_date_ld = any(b.get("datePublished") or b.get("dateModified") for b in page.jsonld)
    if has_date_meta or has_date_ld:
        return [Finding("dated-content", "aeo", "ok", "machine-readable date signal present")]
    return [Finding("dated-content", "aeo", "info",
                    "no machine-readable publish/modified date",
                    "Add datePublished/dateModified in JSON-LD; answer engines prefer citing dated content.")]


@check("heading-anchors", "aeo")
def _c_anchors(page: Page) -> list[Finding]:
    heading_anchor_pattern = re.compile(r"<h[2-3][^>]*id=[\"']([^\"']+)[\"']", re.I)
    anchors = heading_anchor_pattern.findall(page.html)
    total_h2h3 = sum(1 for lvl, _ in page.headings if lvl in (2, 3))
    if total_h2h3 == 0:
        return [Finding("heading-anchors", "aeo", "info", "no h2/h3 to anchor")]
    if not anchors:
        return [Finding("heading-anchors", "aeo", "warn",
                        f"none of {total_h2h3} h2/h3 have id= anchors",
                        "Add id= to h2/h3 so engines can cite sections directly (example.com/page#section).")]
    if len(anchors) / total_h2h3 < 0.5:
        return [Finding("heading-anchors", "aeo", "warn",
                        f"only {len(anchors)}/{total_h2h3} h2/h3 have id= anchors")]
    return [Finding("heading-anchors", "aeo", "ok", f"{len(anchors)}/{total_h2h3} h2/h3 have id= anchors")]


# ------------------------------------------------------------------ #
# Runner
# ------------------------------------------------------------------ #


def audit_page(page: Page, skip_seo: bool = False, skip_aeo: bool = False) -> list[Finding]:
    findings: list[Finding] = []
    for name, family, fn in CHECKS:
        if family == "seo" and skip_seo:
            continue
        if family == "aeo" and skip_aeo:
            continue
        try:
            findings.extend(fn(page))
        except Exception as e:  # noqa: BLE001
            findings.append(Finding(name, family, "error", f"check failed to run: {e}"))
    return findings


SEV_ORDER = {"error": 0, "warn": 1, "info": 2, "ok": 3}


def format_report(page: Page, findings: list[Finding]) -> str:
    lines = [f"URL:   {page.url}"]
    if page.final_url != page.url:
        lines.append(f"Final: {page.final_url}")
    lines.append(f"HTTP:  {page.status}")
    lines.append("")
    grouped = sorted(findings, key=lambda f: (SEV_ORDER.get(f.severity, 9), f.family, f.check))
    for f in grouped:
        icon = {"error": "✗", "warn": "!", "info": "·", "ok": "✓"}.get(f.severity, "?")
        lines.append(f"  {icon} [{f.severity:5s}] [{f.family}] {f.check}: {f.message}")
        if f.fix and f.severity in ("error", "warn"):
            for wrapped in textwrap.wrap(f"→ {f.fix}", width=100, subsequent_indent=" " * 8):
                lines.append(f"          {wrapped}")
    lines.append("")
    counts = {sev: sum(1 for f in findings if f.severity == sev) for sev in SEV_ORDER}
    lines.append(f"  {counts['error']} errors  ·  {counts['warn']} warnings  ·  {counts['info']} info  ·  {counts['ok']} ok")
    return "\n".join(lines)


# ------------------------------------------------------------------ #
# Self-test
# ------------------------------------------------------------------ #


_FIXTURE_GOOD = """<!doctype html>
<html lang="en">
<head>
<title>How to bake sourdough bread at home: a complete guide</title>
<meta name="description" content="A step-by-step guide to baking sourdough bread at home, covering starter care, autolyse, bulk fermentation, shaping, and cold retard.">
<link rel="canonical" href="https://example.com/sourdough">
<meta property="og:title" content="Sourdough Guide">
<meta property="og:description" content="Bake great bread at home.">
<meta property="og:image" content="https://example.com/img.jpg">
<meta property="og:url" content="https://example.com/sourdough">
<meta property="og:type" content="article">
<meta name="twitter:card" content="summary_large_image">
<script type="application/ld+json">
{"@context":"https://schema.org","@type":"Article","datePublished":"2025-01-01","author":{"@type":"Person","name":"Jane"}}
</script>
<script type="application/ld+json">
{"@context":"https://schema.org","@type":"FAQPage","mainEntity":[{"@type":"Question","name":"How long?"}]}
</script>
<script type="application/ld+json">
{"@context":"https://schema.org","@type":"Organization","name":"Example","sameAs":["https://en.wikipedia.org/wiki/Example"]}
</script>
</head>
<body>
<main>
<article>
<h1>How to bake sourdough bread at home</h1>
<p>Sourdough is fermented bread leavened by a live starter culture instead of commercial yeast. The process takes 24–48 hours but only 30 minutes of hands-on work, split across four stages: feed the starter, mix and rest, bulk ferment, and bake.</p>
<h2 id="starter">How do I keep a starter alive?</h2>
<p>Feed it flour and water daily at room temperature, or once a week if refrigerated.</p>
<h2 id="bulk">How long is bulk fermentation?</h2>
<p>Four to six hours at 24C, or overnight in a cool room.</p>
<h2 id="shape">How should I shape the loaf?</h2>
<p>Use a bench scraper and stretch-and-fold every 30 minutes for the first two hours.</p>
<img src="/hero.jpg" alt="A finished sourdough loaf on a cutting board" width="800" height="600">
</article>
</main>
</body>
</html>
"""


_FIXTURE_BAD = """<!doctype html>
<html>
<head>
<title>Bread</title>
<meta name="robots" content="noindex">
</head>
<body>
<div><div><div>
<h2>Bread</h2>
<h4>Skipping levels</h4>
<img src="/a.jpg">
<img src="/b.jpg">
</div></div></div>
</body>
</html>
"""


def _synthetic_page(html: str, url: str = "https://example.com/") -> Page:
    page = Page(url=url, final_url=url, status=200, headers={"content-type": "text/html; charset=utf-8"}, html=html)
    _Parser(page).feed(html)
    return page


def self_test() -> int:
    ok = 0
    fail = 0
    good = _synthetic_page(_FIXTURE_GOOD)
    good_findings = audit_page(good)
    good_errors = [f for f in good_findings if f.severity == "error"]
    if good_errors:
        for f in good_errors:
            print(f"  [good-fixture] unexpected error: {f.check}: {f.message}", file=sys.stderr)
        fail += len(good_errors)
    else:
        ok += 1

    bad = _synthetic_page(_FIXTURE_BAD)
    bad_findings = audit_page(bad)
    required_errors = {"robots-directive", "meta-description", "h1-hierarchy"}
    seen_errors = {f.check for f in bad_findings if f.severity == "error"}
    for want in required_errors:
        if want in seen_errors:
            ok += 1
        else:
            print(f"  [bad-fixture] expected error on {want!r} but not found", file=sys.stderr)
            fail += 1
    required_warns = {"image-alt", "h1-hierarchy"}
    seen_warns = {f.check for f in bad_findings if f.severity == "warn"}
    for want in required_warns:
        if want in seen_warns or want in seen_errors:
            ok += 1
        else:
            print(f"  [bad-fixture] expected warn on {want!r} but not found", file=sys.stderr)
            fail += 1

    reason = _is_private_target("http://localhost/x")
    if reason:
        ok += 1
    else:
        print("  [private-target] expected refusal for localhost", file=sys.stderr)
        fail += 1

    print(f"self-test: {ok} passed, {fail} failed")
    return 0 if fail == 0 else 1


# ------------------------------------------------------------------ #
# CLI
# ------------------------------------------------------------------ #


def main() -> int:
    try:
        sys.stdout.reconfigure(encoding="utf-8")
        sys.stderr.reconfigure(encoding="utf-8")
    except AttributeError:
        pass
    ap = argparse.ArgumentParser(description=__doc__.strip().splitlines()[0])
    ap.add_argument("url", nargs="?", help="URL to audit (https://…)")
    ap.add_argument("--compare", metavar="URL", help="second URL to audit alongside")
    ap.add_argument("--skip-seo", action="store_true", help="skip classic SEO checks")
    ap.add_argument("--skip-aeo", action="store_true", help="skip AEO checks")
    ap.add_argument("--json", action="store_true", help="emit JSON instead of human report")
    ap.add_argument("--self-test", action="store_true", help="run built-in fixtures and exit")
    args = ap.parse_args()

    if args.self_test:
        return self_test()

    if not args.url:
        ap.error("URL is required (or use --self-test)")

    urls = [args.url] + ([args.compare] if args.compare else [])
    exit_code = 0
    all_reports: list[dict] = []
    for url in urls:
        try:
            page = fetch(url)
        except AuditError as e:
            print(f"error: {e}", file=sys.stderr)
            return 2
        findings = audit_page(page, skip_seo=args.skip_seo, skip_aeo=args.skip_aeo)
        if any(f.severity == "error" for f in findings):
            exit_code = 1
        if args.json:
            all_reports.append(
                {
                    "url": url,
                    "final_url": page.final_url,
                    "status": page.status,
                    "findings": [f.__dict__ for f in findings],
                }
            )
        else:
            print(format_report(page, findings))
            print()
    if args.json:
        print(json.dumps(all_reports if len(all_reports) > 1 else all_reports[0], indent=2))
    return exit_code


if __name__ == "__main__":
    sys.exit(main())
