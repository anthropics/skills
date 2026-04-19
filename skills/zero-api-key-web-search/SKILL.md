---
name: zero-api-key-web-search
description: "Free web search, page browsing, and claim verification for AI agents. No API keys required. 100% free. Use this skill whenever the user needs to search the web, read a web page, verify a claim against live sources, or generate an evidence report. TRIGGER when: the user asks to look something up online, check if a statement is true, find current information, read a URL, compare sources, or get citation-ready evidence. Also trigger when the user mentions web search, fact-checking, claim verification, evidence gathering, source validation, or browsing a page — even if they don't name a specific tool. SKIP: tasks that don't require live web data or external source verification."
---

# Zero-API-Key Web Search

Free web search, full-page reading, and evidence-aware claim verification. No API keys, no accounts, no paid services. Install once and your agent can search, browse, and verify against live sources.

## Installation

```bash
pip install zero-api-key-web-search
```

Python 3.10+ required. No configuration needed.

## MCP Server

Add to your MCP client config (Claude Code, Cursor, Copilot, etc.):

```json
{
  "mcpServers": {
    "zero-api-key-web-search": {
      "command": "zero-mcp"
    }
  }
}
```

This exposes four MCP tools: `search_web`, `browse_page`, `verify_claim`, `evidence_report`.

## Tools

### search_web

Search the web for results. Supports general, news, images, videos, and books. Returns titles, URLs, and snippets.

When to use: The user needs current information that isn't in your training data, or wants to find specific web pages.

### browse_page

Extract clean, readable text from any URL. Strips navigation, ads, and boilerplate automatically.

When to use: The user wants to read the content of a web page, or you need the full text of a search result for deeper analysis.

### verify_claim

Verify a claim against live web sources. Classifies evidence as supporting, conflicting, or neutral, and returns a verdict with confidence.

When to use: The user asks "is X true?", "fact-check this", or wants to validate a statement against current sources.

Verdicts: `supported`, `likely_supported`, `contested`, `likely_false`, `insufficient_evidence`.

Use the `--deep` flag (deep mode) to fetch and analyze top result pages for stronger evidence.

### evidence_report

Generate a structured, citation-ready evidence report. Includes verdict, confidence, executive summary, rationale, source digest with per-source classification, and next steps.

When to use: The user needs a formal evidence summary, wants supporting and conflicting sources laid out clearly, or is preparing a research deliverable.

## How Verification Works

1. Search for the claim across available providers
2. Score each source on keyword overlap, source quality, and freshness
3. Classify as supporting, conflicting, or neutral
4. Optionally fetch top pages for deeper page-aware analysis
5. Render a verdict with confidence and evidence breakdown

This is a heuristic evidence classifier, not a proof engine. It reflects the weight of found evidence, not ground truth.

## Dual-Provider Cross-Validation

Default install uses DuckDuckGo (free, no key). For stronger evidence, add a self-hosted SearXNG instance:

```bash
pip install zero-api-key-web-search
./scripts/start-searxng.sh
export ZERO_SEARCH_SEARXNG_URL="http://127.0.0.1:8080"
```

Two independent providers cross-validate results, reducing single-source bias.

## CLI Quick Reference

```bash
zero-search "Python 3.13 release" --json
zero-browse "https://docs.python.org/3/whatsnew/" --json
zero-verify "Python 3.13 is the latest stable release" --deep --json
zero-report "Python 3.13 stable release" --claim "Python 3.13 is the latest stable release" --deep --json
```

## GitHub

https://github.com/wd041216-bit/cross-validated-search