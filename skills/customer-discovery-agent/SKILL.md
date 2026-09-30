---
name: customer-discovery-agent
description: Scrapes Reddit (and soon IndieHackers / 即刻 / 知乎) for pain-pattern keywords, clusters posts into 3-7 themes with Claude, ships a weekly markdown digest of literal user quotes. Use when validating a new product idea, picking the next feature, or running Monday-morning customer-research instead of building from gut.
---

# Customer Discovery Agent

Scans online communities for what indie makers are actually frustrated about, clusters quotes into themes, and ships a weekly markdown digest. Replaces "build from gut → product-without-buyers" with "read 50 literal quotes from your target user every Monday for $0.05."

## When to use this skill

Invoke this skill when:

- The user is about to start building a new feature without independent demand signal
- A weekly cron should land a "what is r/SaaS / r/IndieHackers complaining about" digest in the operator's inbox
- The user asks "is there demand for X" or "what should I build next"
- A product launch needs verbatim user-language to feed into landing-page copy
- The user wants pain-points as PainPoint pydantic data for downstream agents (marketing-agent positioning, funnel-analytics segmentation)

## What it does

1. **Scrapes Reddit** via PRAW (top + new posts in an N-hour window across N subreddits)
2. **Filters with 17 pain-pattern keywords**: "i wish", "frustrated", "is there a tool", "anyone know how", "why is X so", "tired of", "hate when", etc.
3. **Deduplicates** into PainPoint pydantic models (title, body, url, subreddit, score, comments, matched_pattern)
4. **Clusters with Claude Haiku 4.5** in one call into 3-7 themes when `ANTHROPIC_API_KEY` is set. Falls back to keyword-based heuristic clustering otherwise
5. **Renders a markdown digest** with metadata (window, scanned count, hit count) + per-cluster theme + 3-5 representative quote URLs
6. **Optional VibeX ai_reviews source** (v0.5.0+): re-uses already-paid Claude project reviews from VibeXForge as zero-new-API PainPoint data

## Examples

### Example 1: Weekly cron digest

User: "Scan SaaS / IndieHackers / SideProject / Entrepreneur for the past 7 days and give me the digest"

Skill output:
```
# Customer Discovery Digest — week of 2026-06-02

Window: 168h  ·  Subreddits: 4  ·  Posts scanned: 1,247  ·  Pain hits: 86

## Theme 1: i18n is still painful (24 mentions)
- "Why is there no good i18n tool for Next 15? next-intl breaks on app router"
  → reddit.com/r/SaaS/comments/abc123
- "frustrated with translating my landing page — DeepL costs $30/mo for 200 strings"
  → reddit.com/r/IndieHackers/comments/def456
...

## Theme 2: Vercel build minutes burning solo budgets (18 mentions)
- "is there a tool to catch type errors BEFORE Vercel charges me 5 min"
  → reddit.com/r/SideProject/comments/ghi789
...

## Theme 3: Cold-email tooling is overkill for indie raises (14 mentions)
...
```

### Example 2: Feed pain-points into marketing-agent

User: "Cluster yesterday's r/ClaudeAI posts and pass them to marketing-agent so we draft a HN response thread"

Skill: Runs scan with a 24h window, emits JSON instead of markdown (`--format json`), and pipes the top cluster's URLs into marketing-agent's `--source customer-discovery` flag so the draft thread cites actual user quotes by URL.

## Guidelines

- **Always use a window long enough for the subreddit's volume** — 6h for r/SaaS is fine, 6h for r/SideProject misses 80% of signal. Default 168h (1 week) is safe
- **Never publish quotes without their URL** — provenance is the whole point of literal-quote research
- **Cap LLM cost** — one cluster call per scan, never per pain-point. Costs $0.001-0.05 depending on hit count
- **Heuristic fallback is real, not a stub** — if no `ANTHROPIC_API_KEY`, keyword-based clustering still ships a usable digest
- **Respect PRAW credentials** — never commit them. PRAW env vars are shared with marketing-agent's Reddit adapter
- **The digest is a starting point, not a verdict** — surfacing 24 mentions of "i18n is painful" does NOT mean "build an i18n tool." It means "go talk to those 24 people"
- **Cross-week diffing is the killer feature (v0.5 roadmap)** — "this theme grew 3× this week" is the signal that justifies building

## Configuration

Required:
- `REDDIT_CLIENT_ID`, `REDDIT_CLIENT_SECRET`, `REDDIT_USER_AGENT` — PRAW credentials

Optional:
- `ANTHROPIC_API_KEY` — enables LLM clustering mode (Haiku 4.5). Without it, heuristic clustering ships
- `CUSTOMER_DISCOVERY_HOURS` — default 168 (1 week)
- `CUSTOMER_DISCOVERY_SUBREDDITS` — comma-separated list, default `SaaS,IndieHackers,SideProject,Entrepreneur`

## Provenance

This skill wraps the open-source [customer-discovery-agent](https://github.com/alex-jb/customer-discovery-agent) (MIT, PyPI: `pip install customer-discovery-agent`) — one of 11 agents in the Solo Founder OS stack at github.com/alex-jb/solo-founder-os. Currently shipped at v0.5.0 with 13 passing tests, MCP server for Claude Desktop, and the VibeX ai_reviews source that re-uses already-paid Claude project reviews as PainPoint data at zero new API cost.

## See the rest of the stack

The full Solo Founder OS canonical 7-layer one-person-company runtime includes 10 sibling agents covering: monthly cost audit, pre-push code review, multi-platform marketing (12 channels incl 小红书 / 即刻 / 知乎 / B站), sales / cold email, customer support, payments, analytics, bilingual EN/ZH content sync, and the SFOS core framework. Browse the meta-repo at `alex-jb/solo-founder-os-skills`.
