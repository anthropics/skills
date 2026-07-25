# Bot Access + AI Citation Monitoring

This reference answers two operational decisions: **can AI crawlers reach your content at all**, and **how do you know when you're being cited (or losing citations)?**

Bot access is the prerequisite for every other AEO investment — perfect E-E-A-T and schema mean nothing if the crawler is blocked. Monitoring closes the loop: AEO is non-deterministic, so you iterate on evidence, not assumptions.

Folded in from the former `ai-seo` skill (merged into `aeo` 2026-06); landscape data last validated 2026-03 — verify platform behavior with manual testing before major decisions.

---

## Part 1: Bot Access

### The AI Crawler Matrix

Check `yourdomain.com/robots.txt`. These bots must NOT be blocked for the corresponding platform to index or cite you:

| Bot user-agent | Platform it feeds | Blocking it means |
|---|---|---|
| `GPTBot` | OpenAI / ChatGPT | No ChatGPT search citations |
| `PerplexityBot` | Perplexity | No Perplexity citations |
| `ClaudeBot` / `anthropic-ai` | Anthropic / Claude | No Claude browse citations |
| `Google-Extended` | Google AI Overviews + Gemini | No AI Overview / Gemini grounding |
| `Applebot-Extended` | Apple Intelligence | No Apple Intelligence answers |
| `cohere-ai` | Cohere | No Cohere-backed answers |
| (Bingbot) | ChatGPT search + Microsoft Copilot | Both use Bing's index — Bing indexing is a prerequisite |

**robots.txt to allow all major AI bots:**

```
User-agent: GPTBot
Allow: /

User-agent: PerplexityBot
Allow: /

User-agent: ClaudeBot
Allow: /

User-agent: Google-Extended
Allow: /
```

Notes:

- Blocking training crawl ≠ blocking citation — for most platforms they are the same crawl. Selective `Disallow:` rules trade training exposure against citation visibility; there is no confirmed way to get one without the other.
- **A blocked AI bot is the single highest-priority AEO finding.** It zeroes visibility on that platform and is a 5-minute fix. Flag it before anything else.
- JavaScript-only content is effectively invisible to most AI crawlers — content that requires JS execution to render may never be extracted.

### Indexing prerequisites per platform

| Platform | Index used | Prerequisite |
|---|---|---|
| Google AI Overviews | Google's own index | You must rank in traditional Google search first — AI Overviews strongly prefer top-10 pages |
| ChatGPT (search) | Bing API + internal | Submit sitemap to Bing Webmaster Tools; verify with URL Inspection |
| Perplexity | Own crawler + Brave + Bing | Allow PerplexityBot; real-time retrieval rewards fresh content |
| Claude (browse) | Brave + direct fetch | Allow ClaudeBot; clean fetchable HTML |
| Microsoft Copilot | Bing | Same Bing requirements as ChatGPT |

### Cross-platform signal summary

| Signal | AI Overviews | ChatGPT | Perplexity | Claude | Copilot |
|---|---|---|---|---|---|
| Must rank in traditional search | Yes | Bing only | No | No | Bing only |
| Schema markup impact | High | Medium | Low-Medium | Medium | Medium |
| Content recency weight | High | Medium | Very high | Medium | Medium |
| Original data advantage | High | High | High | High | High |
| Author attribution impact | Medium | High | Low | High | Medium |

(For per-LLM citation selection heuristics, see `llm_citation_patterns.md` — this table covers only access/weighting signals.)

---

## Part 2: Monitoring

The honest truth: AI citation monitoring is immature. There is no Search Console equivalent for Perplexity or ChatGPT. The reliable stack today is **Google Search Console (for AI Overviews) + weekly manual testing + the `citation_tracker.py` ledger in this skill**.

### Google Search Console — AI Overviews (best current tooling)

1. Search Console → Performance → Search results
2. Filter: "Search type" → "AI Overviews"
3. Date range: last 90 days minimum

What to act on:

- Sort by impressions → your current AI Overview presences
- Impressions growing + clicks dropping on a query → an AI Overview is answering it; you're cited but not visited (AI Overview CTR typically runs 50-70% below organic)
- Sharp impression drops → you likely lost an AI Overview slot; run the drop diagnostic below

Frequency: weekly check; monthly CSV export for trends.

### Manual testing protocol (Perplexity, ChatGPT, Copilot)

Weekly, for your top 10-20 target queries, in a fresh/incognito session:

1. Run the query on each platform
2. Check the sources panel / citations
3. Record: cited (yes/no), position among sources, which URL, top cited competitor

Log results with this skill's `citation_tracker.py` (local ledger at `~/.aeo-data/citations.json`). Interpretation:

- Cited 4/4 weeks → stable (protect the page; don't restructure it)
- Cited 2/4 weeks → fragile (strengthen extractability + authority signals)
- Never cited → gap (page lacks extractable patterns — see `extractable_content_patterns.md`)

ChatGPT citations vary by session — treat them as probabilistic and test monthly, not weekly; the goal is appearing in the citation set, not every time.

### Indirect traffic signals

- **Referrals**: filter GA4 for `perplexity.ai`, `chat.openai.com`, `claude.ai`, `copilot.microsoft.com` — low volume, high intent
- **Direct-traffic anomalies** to deep content pages (not homepage) can signal AI-driven attention (users copy/paste cited URLs)

### When citations drop — diagnostic order

1. **robots.txt** — did someone block an AI bot? (Most common, fastest fix; recovery typically 1-4 weeks after unblocking)
2. **Page structure** — was the definition block, FAQ, or steps section removed in an edit?
3. **Competitor** — did someone publish a more extractable page on the same query?
4. **Page health** — noindex added, canonical changed, Core Web Vitals regressed?
5. **Authority** — significant backlink loss; check for manual actions in Search Console

| Root cause | Fix |
|---|---|
| AI bot blocked | Restore robots.txt allow rules |
| Patterns removed | Restore definition/FAQ/steps blocks |
| Competitor outranked | Add specifics, original data, schema |
| Authority drop | Rebuild links; check manual penalties |
| Content stale | Refresh data with current year |

---

## Citations (6 sources)

1. Google Search Central — "AI features and your website" + Search Console AI Overviews reporting documentation (developers.google.com/search)
2. OpenAI — GPTBot documentation (platform.openai.com/docs/gptbot)
3. Perplexity — PerplexityBot crawler documentation (docs.perplexity.ai)
4. Anthropic — "Does Anthropic crawl data from the web?" ClaudeBot support documentation (support.anthropic.com)
5. Bing Webmaster Tools documentation — indexing and URL inspection (bing.com/webmasters)
6. Kevin Indig — "Growth Memo" analyses of AI Overviews CTR impact and zero-click behavior (growth-memo.com)
