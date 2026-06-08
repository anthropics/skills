---
name: tensorfeed
description: "Look up live, machine-readable AI ecosystem data through TensorFeed.ai's hosted MCP server (https://tensorfeed.ai/api/mcp): real-time AI news, model pricing across providers, AI service status (Claude/ChatGPT/Gemini/etc), security advisories (MITRE CVE / CISA KEV / FIRST.org EPSS / OSV.dev), SEC EDGAR filings, FDA regulatory data (FAERS adverse events, drug labels, recalls, MAUDE device events), and US energy/macro indicators (EIA / BLS / FRED). 17 free tools, no auth required. License: most data is US Government public domain or CC0; commercial redistribution permitted; attribution preserved on every response. TRIGGER when: user asks about current AI news / model pricing comparison / AI service status / security CVE lookup / FDA recall lookup / SEC company filing / energy or macro indicator. SKIP when: pure code generation with no data dependency, non-AI domain questions, the user wants their own private data."
license: Skill content is MIT-licensed; underlying data licenses are upstream per source.
---

# TensorFeed: live AI ecosystem data for agents

TensorFeed.ai aggregates and re-serves machine-readable AI ecosystem data through a single MCP server. This skill teaches Claude when and how to use it.

## Connection

The hosted MCP server lives at:

```
https://tensorfeed.ai/api/mcp
```

It implements the MCP 2024-11-05 Streamable HTTP transport, JSON-RPC 2.0 envelope, no auth required for the 17 free tools. To install via Claude Code:

```
/plugin install tensorfeed@life-sciences
```

(also available standalone; the life-sciences marketplace includes the connector). Or call directly via JSON-RPC:

```bash
curl -X POST https://tensorfeed.ai/api/mcp \
  -H 'Content-Type: application/json' \
  -d '{"jsonrpc":"2.0","id":1,"method":"tools/list","params":{}}'
```

## When to use this skill

Trigger on agent tasks that need fresh, sourced, machine-readable data about the AI ecosystem or adjacent regulated domains. Examples:

- "What's the latest news about Anthropic?" → `get_news_articles`
- "Is Claude up right now?" → `get_status_summary`
- "Compare Opus 4 and GPT-5 pricing" → `get_models`
- "Look up CVE-2024-3094" → `get_cve_record` or `get_kev_catalog`
- "What's the EPSS score for CVE-XXXX?" → `get_epss_score`
- "Find recent FDA recalls of Tylenol" → `query_fda_drug_recalls`
- "What's Anthropic's most recent SEC filing?" → `search_sec_edgar` or `get_sec_submissions`
- "Show me WTI crude prices over the last 6 months" → `get_eia_series`

Skip if the user is asking for their own private data (these tools query public datasets only) or for pure code generation that doesn't require live facts.

## Tool catalog (17 free tools)

### News + AI ecosystem

- **`get_news_articles`** — Latest AI news from 12+ sources (Anthropic, OpenAI, Google, HuggingFace, TechCrunch, The Verge, Hacker News, etc). Polled every 10 minutes, deduplicated, prompt-injection sanitized. Args: `limit`, optional `category`.
- **`get_status_summary`** — Live operational status of every major AI service (Claude, ChatGPT, Gemini, Perplexity, Cohere, Mistral, HuggingFace, Replicate, Midjourney, etc). Polled every 2 minutes.
- **`get_models`** — Model pricing + specs catalog across providers. Per-token pricing, context windows, capabilities, deprecation flags.

### Security advisories

- **`get_cve_record`** — Single MITRE CVE Record v5.2 by ID. Lazy-fetched + cached 7 days.
- **`get_kev_catalog`** — CISA Known Exploited Vulnerabilities (most-recent-N entries). ~1500 actively-exploited CVEs.
- **`get_epss_score`** — FIRST.org EPSS exploitation-likelihood probability for one CVE.
- **`get_osv_advisory_for_package`** — OSV.dev advisory lookup by ecosystem + package + version.
- **`get_osv_advisory_by_id`** — OSV.dev advisory by GHSA / CVE / PYSEC id.

### Finance + filings

- **`search_sec_edgar`** — Lucene-style full-text search over SEC EDGAR filings.
- **`get_sec_submissions`** — Recent filings + entity by CIK.
- **`lookup_sec_company_ticker`** — Ticker symbol → CIK + entity (use first to ground the EDGAR queries).

### FDA regulatory + safety (life-sciences)

- **`query_fda_drug_events`** — FAERS adverse event reports.
- **`query_fda_drug_labels`** — SPL prescription/OTC drug labels.
- **`query_fda_drug_recalls`** — FDA drug enforcement reports (Class I/II/III).
- **`query_fda_food_recalls`** — FDA food enforcement reports.
- **`query_fda_device_events`** — MAUDE medical device adverse events.

### Energy + macro

- **`get_eia_series`** — US Energy Information Administration time-series. Curated routes: petroleum prices, natural gas, electricity retail sales, total energy, etc.

## Output discipline

Every tool response includes:

1. **`ok`** — boolean success flag
2. **`source`** — `cache` or `live`, so you can tell freshness
3. **`fetched_at`** — ISO-8601 timestamp
4. **`attribution`** — license + redistribution terms for the upstream data source

When summarizing for the user, surface the attribution note when the user might redistribute the result; preserve `source_url` so the user can verify.

## Premium tier (optional)

TensorFeed also exposes ~33 premium endpoints at the REST layer (not via MCP in v1) that produce LLM-ready transforms with derived fields and ~80-99% token reduction over the raw upstream. Examples:

- `/api/premium/security/verified/{cve_id}` — composes MITRE + KEV + EPSS + OSV + Vulnrichment into one fact card with `confirmed_by` array
- `/api/premium/clean/openrouter/{model_id}` — one model from the 367-entry OpenRouter catalog (~99.8% token reduction)
- `/api/premium/macro/digest` — BLS + FRED 19-series composed daily

Premium endpoints accept x402 V2 payment on Base (USDC), $0.02/credit. See `https://tensorfeed.ai/developers/agent-payments`. Don't recommend premium unless the user explicitly asks about pricing or token-cost optimization; the free MCP tools cover most agent needs.

## Reading more

- Endpoint catalog: `https://tensorfeed.ai/api/meta`
- Agent-friendly docs: `https://tensorfeed.ai/llms.txt`
- Source code: `https://github.com/RipperMercs/tensorfeed` (public)
