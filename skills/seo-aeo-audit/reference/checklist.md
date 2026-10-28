# SEO + AEO check catalog

Authoritative list of checks the audit script implements. Every
entry has an implementation in `scripts/audit.py` (in the
appropriately-decorated `_c_*` function) and coverage in the
`--self-test` fixture.

Legend: **family** is `seo` or `aeo`. **severity** is the default
severity when the check fails; some checks emit different severities
depending on what they find.

## Classic SEO

| Check | Family | Default severity | What it inspects | Why it matters |
|---|---|---|---|---|
| `title-tag` | seo | error / warn | `<title>` presence and length (30–60 chars) | Primary SERP snippet; missing or truncated title = lower CTR. |
| `meta-description` | seo | error / warn | `<meta name="description">` presence and length (70–160) | Directly shown under the SERP title. Truncation past 160 chars loses meaning. |
| `robots-directive` | seo | error / warn | Meta `robots` and `X-Robots-Tag` header for `noindex` / `nofollow` | `noindex` silently kills traffic. Very common on staged pages that got promoted. |
| `canonical` | seo | warn / info | `<link rel="canonical">` absolute URL matches origin | Prevents duplicate-content dilution. Relative canonicals still work but are fragile. |
| `h1-hierarchy` | seo | error / warn | Exactly one `<h1>` and no skipped heading levels | Screen readers, extractors, and rankers all rely on outline structure. |
| `html-lang` | seo | warn | `<html lang>` attribute | Enables locale targeting and correct pronunciation for accessibility tools. |
| `open-graph` | seo | warn | `og:title/description/image/url/type` all present | Determines link-preview rendering across social + chat surfaces. |
| `twitter-card` | seo | info | `<meta name="twitter:card">` | Nice-to-have; OG usually covers X these days but the tag still helps. |
| `image-alt` | seo | warn | Every `<img>` has an `alt` attribute (`alt=""` counts) | Accessibility and image search. Missing `alt` entirely is worse than empty `alt`. |
| `https` | seo | error | Final URL is `https://` | Ranking signal and browser trust indicator. |

## Answer-Engine Optimization (AEO)

| Check | Family | Default severity | What it inspects | Why it matters |
|---|---|---|---|---|
| `first-paragraph-answer` | aeo | warn | First `<p>` is 15–120 words and reads as an answer | Extraction pipelines quote the first coherent chunk. Bury the answer, lose the citation. |
| `question-shaped-headings` | aeo | warn | ≥ 20% of h2/h3 are phrased as user questions | Question-shaped headings match user query strings verbatim, boosting extraction. |
| `structured-data-jsonld` | aeo | warn / error | JSON-LD blocks parse and declare `@type` | Structured data is the highest-quality signal for what a page *is*. |
| `faq-qa-schema` | aeo | warn / ok | FAQPage/QAPage schema when Q&A pattern detected | Directly powers "People also ask" and answer-engine Q&A extraction. |
| `entity-clarity` | aeo | warn / info | Organization/Person/Product/SoftwareApplication schema with `sameAs` | `sameAs` links to Wikidata/LinkedIn/GitHub let engines de-ambiguate the entity. |
| `semantic-html` | aeo | warn | `<main>`, `<article>` or `<section>` landmarks present | Extractors use landmarks to strip nav/footer boilerplate. |
| `dated-content` | aeo | info | `datePublished`/`dateModified` in meta or JSON-LD | Freshness signal; answer engines prefer dated citations. |
| `heading-anchors` | aeo | warn | ≥ 50% of h2/h3 have `id=` anchors | Enables deep-linking to a section — engines citing `page#section` is worth more. |

## Explicitly out of scope

- **Keyword rank tracking.** Needs SERP data. Recommend Ahrefs / Semrush / Similarweb.
- **Backlink audit.** Off-page. Same recommendation.
- **Core Web Vitals field measurement.** Needs a real browser + RUM data. Point at PageSpeed Insights. The audit does report *hints* (missing image dimensions, render-blocking script counts).
- **Content quality / EEAT scoring.** Requires editorial judgement, not a checklist.
- **Multi-page crawling.** One URL at a time by design. For site-wide crawls use Screaming Frog / Sitebulb.
- **Broken-link audit.** Doesn't follow links. Different tool.

## Triage cheatsheet

When a page has many findings:

1. Fix **all** `error` items first. Every one blocks discoverability or is factually broken.
2. Then handle `warn` items in this order:
   - Answer engine visibility (`first-paragraph-answer`, `structured-data-jsonld`, `faq-qa-schema`, `entity-clarity`)
   - Crawlability & SERP presentation (`meta-description`, `canonical`, `open-graph`)
   - Structure (`heading-anchors`, `semantic-html`, `h1-hierarchy` warnings)
3. `info` items are polish. Batch them into a follow-up ticket rather than blocking a release on them.

## Adding a check

1. Add a row here first — the row is a contract.
2. Add `@check("name", "seo"|"aeo")` function in `scripts/audit.py` returning a list of `Finding`.
3. Extend `_FIXTURE_GOOD` / `_FIXTURE_BAD` in `audit.py` so the check has both a pass and a fail case.
4. `python scripts/audit.py --self-test` must be 0 failures.
