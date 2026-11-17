---
name: seo-aeo-audit
description: >
  Audit a public URL for both classic SEO (title tag, meta
  description, H1 hierarchy, canonical, Open Graph, Twitter Card,
  JSON-LD structured data, image alt text, robots directives,
  sitemap discoverability, hreflang) and Answer-Engine Optimization
  (AEO) — the properties that determine whether ChatGPT, Perplexity,
  Google AI Overviews, Claude, and similar answer engines will cite
  or extract from the page. AEO checks include: a single crisp
  first-paragraph answer, question-shaped H2/H3s, FAQ / QAPage /
  HowTo schema presence, entity clarity (Organization / Person /
  Product schema), stable URLs, semantic HTML over div soup, table-
  of-contents anchors, cite-friendly authorship + dated content, and
  extractable "chunks" (short paragraphs, definition lists, TL;DRs).
  Use when the user asks to "audit this URL", "SEO check", "why
  isn't this ranking / getting cited by AI", "AEO audit", "make this
  page LLM-friendly", or pastes a URL and asks how to improve its
  discoverability. Do NOT use for keyword research, backlink audits,
  server-side performance tuning, or writing new copy — those are
  different skills. The scanner is stateless and read-only; it fetches
  one URL at a time.
license: Complete terms in LICENSE.txt
---

# SEO + AEO Audit

## Why this exists

Being findable used to mean "rank in Google." Today it also means
"get cited by an answer engine." The two overlap heavily —
crawlability, structured data, clear semantic HTML — but they
diverge in a few important places, and most SEO audit tools were
built before that divergence mattered. This skill covers both
surfaces in one pass.

**SEO** ranks pages by their signals. Answer engines extract from
them. The extractor is not a ranking algorithm — it is a parser
looking for a self-contained answer it can trust and cite. So the
AEO layer is about being *legible to a first-time reader who has
patience for exactly one paragraph*.

## When to run the audit

Run it when the user says any of:

- "audit this URL", "SEO check", "SEO/AEO audit"
- "why isn't this ranking / getting cited / showing up in AI answers"
- "make this page LLM-friendly / AI-search-friendly"
- pastes a URL and asks how to improve its discoverability

Do **not** run it for:

- Keyword research or ranking tracking — needs an external SERP data
  source. Recommend an SEO SaaS tool instead.
- Backlink audits — off-page signal, needs a third-party index.
- Server performance — Core Web Vitals need a real browser + field
  data. The audit will report *hints* (image dimensions, render-
  blocking script counts) but will not measure LCP or CLS.
- Content generation — the audit finds gaps; a separate content
  skill fills them.

## How to run it

The skill ships `scripts/audit.py`. It uses only the Python 3
standard library — no `pip install` required. Always try `--help`
first to see current flags:

```bash
python scripts/audit.py --help
```

Common invocations:

```bash
# Audit a single URL, human-readable report
python scripts/audit.py https://example.com/pricing

# JSON output (for piping into a report generator)
python scripts/audit.py https://example.com/pricing --json

# Compare two URLs (before/after, or self vs. competitor)
python scripts/audit.py https://a.example.com --compare https://b.example.com

# Skip AEO checks and only run classic SEO
python scripts/audit.py https://example.com --skip-aeo

# Skip SEO checks and only run AEO
python scripts/audit.py https://example.com --skip-seo
```

The script exits `0` on a clean audit, `1` when any severity-`error`
finding is present, and `2` on fetch failure (DNS, timeout, non-2xx
that is not a documented redirect).

Findings are printed with severity, check name, and a short
description. When there is an obvious fix, the script prints a one-
line remediation directly under the finding.

## Reading the output

The audit reports three severity levels:

- **error** — a signal is missing or broken in a way answer engines
  and search crawlers demonstrably penalise. `noindex` when the page
  should be indexed. Missing `<title>`. Duplicate `<h1>`.
- **warn** — a signal is suboptimal but not broken. Meta description
  over 160 chars (truncated in SERP). Title over 60 chars. Sparse
  alt text. Missing FAQ schema on a page that clearly has FAQs.
- **info** — an observation worth naming but not something to fix on
  its own. "No hreflang declared" is `info` unless the site clearly
  targets multiple locales.

When you summarise the audit for the user, group by severity, lead
with errors, and pair each finding with a **why-this-matters** line
in plain language. Do not just print the check name — the user is
usually not the person who will do the fix and they need the
translation.

## The two check families

### Classic SEO (`--skip-aeo` isolates these)

- Title tag: present, 30–60 chars, contains the primary keyword.
- Meta description: present, 70–160 chars, non-generic.
- Canonical URL: present, absolute, self-referential unless the page
  is intentionally a syndication of another URL.
- One and only one `<h1>`. Heading hierarchy monotone (no skipping
  h2→h4).
- `<html lang>` attribute present.
- Meta `robots` — flag any `noindex` or `nofollow` explicitly.
- Open Graph (`og:title`, `og:description`, `og:image`, `og:url`,
  `og:type`) — all five required for shareability.
- Twitter Card (`twitter:card` at minimum).
- JSON-LD structured data — parsed, validated as JSON, `@type`
  reported per block.
- Every `<img>` has non-empty `alt` unless explicitly decorative
  (`alt=""`, which is intentional and allowed).
- `<link rel="alternate" hreflang="…">` present when multiple
  locales are shipped.
- Discoverable `robots.txt` and `sitemap.xml` at the root of the
  origin.
- HTTPS, HSTS advertised in headers.

### Answer-Engine Optimization (`--skip-seo` isolates these)

- **First-paragraph answer.** The first non-boilerplate paragraph
  should self-contain the page's core answer in ~2–4 sentences.
  Answer engines quote the first coherent chunk that stands alone;
  don't bury it under lore.
- **Question-shaped H2/H3s.** Real user questions rank as
  extractable chunks. `## How does X work?` beats `## Mechanism`.
- **FAQ / QAPage / HowTo schema.** If the page is Q&A-shaped and
  doesn't declare FAQPage or QAPage schema, that's an easy win.
- **Entity clarity.** Organization, Person, Product, or SoftwareApp
  schema with `sameAs` links to canonical entity sources (Wikidata,
  LinkedIn, GitHub, Crunchbase). This is how engines de-ambiguate
  "Anthropic" the company from "anthropic" the adjective.
- **Semantic HTML.** `<article>`, `<section>`, `<nav>`, `<main>`,
  `<figure>`. Deep `<div>`-only trees are extraction-hostile.
- **Table of contents / heading anchors.** An `id=` on every h2/h3
  lets engines cite `example.com/page#specific-section`, which
  encourages citation.
- **Cite-friendly signals.** Visible byline (`author` in JSON-LD or
  `rel=author`), a machine-readable published/modified date
  (`datePublished`, `dateModified`), and where relevant an
  `about`/`mentions` array of entities.
- **Extractable chunks.** Short paragraphs (< 100 words), bulleted
  lists with parallel structure, definition lists (`<dl>`), and
  TL;DR / summary blocks at the top of long articles.
- **Stable URL shape.** Kebab-case slugs, no session tokens, no
  redirect chains longer than 1 hop, canonical matches request URL.
- **Content freshness signal.** A visible `Last updated:` line, or
  `dateModified` in JSON-LD, more recent than 12 months for anything
  in a fast-moving domain.

## Never do

- **Never run the audit against localhost, private IPs, or a
  staging URL protected by basic auth.** The script explicitly
  refuses `127.0.0.1`, `10./172.16./192.168./169.254./::1`, and
  anything on `.local` — an AEO audit is a *public* discoverability
  check by definition. If the user wants a pre-production check,
  suggest a preview deployment on a public URL.
- **Never bulk-crawl.** The script fetches one URL and, if enabled,
  one `robots.txt` and one `sitemap.xml`. It does not follow links.
  If the user asks to crawl a whole site, say no and recommend
  Screaming Frog or Sitebulb.
- **Never fabricate a Core Web Vitals score.** The script reports
  static hints (missing `width`/`height` on images, count of render-
  blocking scripts) but does not measure LCP/FID/INP/CLS. If the
  user needs those, point them at PageSpeed Insights or Lighthouse.

## Extending the check set

`reference/checklist.md` is the authoritative list of checks. Each
entry has: check name, family (SEO or AEO), severity, what it
inspects, the "why this matters" one-liner, and the remediation
template. When adding a new check:

1. Add the entry to `reference/checklist.md`.
2. Implement it in `scripts/audit.py` inside the appropriate
   `run_seo_*` or `run_aeo_*` function, and register it in
   `CHECKS`.
3. Add or extend the unit-test cases at the bottom of `audit.py`
   (`--self-test`) so the check has at least one pass fixture and
   one fail fixture.
4. Run `python scripts/audit.py --self-test` — must be 0 failures.
