# Firecrawl Technical Guide

Technical integration patterns for the Firecrawl API within the Universal Scraping Architect (Mode 1: API-Driven). Use this when the source is a public URL, a JS-heavy SPA, requires search-first discovery, or involves bulk crawling across a domain.

## Authentication (BYOK)
Firecrawl uses a Bring-Your-Own-Key model. The key is **always** read from the
`FIRECRAWL_API_KEY` environment variable — never hardcoded, never committed.
The free tier is sufficient for evaluation and small jobs, which keeps this skill
compliant with the repo's "no paid commercial dependency" rule.

```python
import os
from firecrawl import FirecrawlApp
app = FirecrawlApp(api_key=os.getenv("FIRECRAWL_API_KEY"))
```

## Choosing the right operation
- **`scrape`** — single URL → clean markdown/HTML/structured JSON. Cheapest; one credit per page. Default for "give me this page."
- **`crawl`** — follow links across a domain up to a depth/limit. Credit cost scales with pages; always set `limit` and `maxDepth` to bound spend.
- **`map`** — fast URL discovery (sitemap-style) without full extraction. Use it *first* to scope a crawl before paying for full extraction.
- **`search`** — query-first discovery when you don't yet have URLs.

## Quota & rate-limit awareness
Estimate credits **before** launching bulk jobs (`map` → count URLs → multiply).
Treat HTTP 429 / quota errors as expected: back off exponentially, log the quota
state, and checkpoint progress so a re-run resumes rather than restarts. Firecrawl
returns structured error payloads — surface the message rather than swallowing it.

## Token-budget discipline
Extracted markdown frequently exceeds an LLM context window. Estimate tokens
(`chars / 4` as a cheap proxy) and chunk before passing downstream, reserving
output tokens for the model's response. See `scripts/firecrawl_example.py`.

## Output formats
Request only the formats you need (`["markdown"]` is smallest). Markdown for prose,
structured-JSON extraction for tabular/typed data, HTML only when you need the DOM.

### Authoritative Sources
1. [Firecrawl API Documentation](https://docs.firecrawl.dev/api-reference/introduction)
2. [Firecrawl SDK for Python](https://github.com/mendableai/firecrawl-py)
3. [REST API Design Best Practices (Microsoft)](https://learn.microsoft.com/en-us/azure/architecture/best-practices/api-design)
4. [Handling API Rate Limits (Cloudflare)](https://developers.cloudflare.com/fundamentals/api/reference/rate-limits/)
5. [JSON Schema Standard](https://json-schema.org/specification.html)
6. [Exponential Backoff and Jitter (AWS Architecture Blog)](https://aws.amazon.com/blogs/architecture/exponential-backoff-and-jitter/)
