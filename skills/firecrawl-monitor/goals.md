# Writing monitor goals and queries

Reference for authoring `--goal` (all monitors) and `--queries` (web monitors). Read from [SKILL.md](SKILL.md) when creating or tuning a monitor.

## Writing a good `--goal`

The goal is what the AI change judge uses to decide whether a page is `changed` vs `same`. Convert the user's intent into a concise 2-3 sentence goal:

- Start with `Alert when ...` and state the trigger using the user's wording.
- Restate any scope they mentioned: top N, price, role type, region, company, topic, status, or a specific entity.
- Add an `Ignore ...` sentence **only** for intent-specific exclusions (e.g. points/comments for rankings, marketing copy for pricing, general company-page updates for job listings). The judge already handles generic noise — whitespace, casing, punctuation, encoding, formatting-only changes, request/session IDs, cache busters, tracking params, generic metadata, and unrelated page chrome — so leave those out.
- Include only page-specific sections, entities, thresholds, exclusions, or business rules the user actually mentioned.
- If the user is vague or asks for "any change", keep the goal broad with no exclusions. If the user mentions noise they do not care about, include that explicitly.

| User says                   | Good goal                                                                                                                                                             |
| --------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `top 10 hackernews stories` | `Alert when stories enter, leave, or change rank within the Hacker News top 10. Ignore points, comments, and timestamps. Do not alert on changes outside the top 10.` |
| `pricing changes`           | `Alert when pricing information changes, including prices, plan names, billing periods, tiers, limits, or included features. Ignore unrelated marketing copy.`        |
| `new engineering roles`     | `Alert when a new engineering role is posted. Ignore general company-page updates unless they add, remove, or change an engineering role.`                            |
| `track this page`           | `Alert when substantive visible content on this page changes.`                                                                                                        |
| `any change`                | `Alert when any visible page content changes, including copy, numbers, timestamps, counters, links, and layout text.`                                                 |

## Writing good `--queries` (web monitors)

For a web monitor, **queries control recall** (what the search retrieves) and **the goal controls precision** (which results alert). Tune both — a perfect goal can't alert on a result the queries never pulled in, and broad queries with a vague goal produce constant low-value alerts.

- Write **keywords, not sentences**: `OpenAI new model release`, not `tell me when OpenAI releases a new model`.
- Quote multi-word entities (`"Llama 4"`); group synonyms with `OR` (`launch OR release OR announcement`).
- Keep each query tight (~2–6 terms). One broad query usually beats several narrow ones — extra queries split the `--max-results` budget without adding coverage.
- One query per **distinct** subject. Several facets of one subject = one query; only split for genuinely separate entities (e.g. "OpenAI, Anthropic, and Google").
- Restrict or exclude sources with `--include-domains` / `--exclude-domains` rather than `site:` operators in queries.
- **`--search-window`** sets recency — `5m`, `15m`, `1h`, `6h`, `24h`, `7d` (default `24h`). Widen it for niche topics that don't publish often.
- **`--max-results`** caps results per query, 1–50 (default `10`).

```bash
firecrawl monitor create --name "AI model releases" --schedule "daily at 9:00" \
  --queries "new AI model release,frontier model launch" \
  --goal "Alert when a major lab releases a new AI model. Ignore tutorials and listicles." \
  --search-window 7d --max-results 20 \
  --webhook-url https://example.com/hook
```

**What good looks like:** a healthy web monitor mostly returns `new: 0` and alerts only on genuinely new, on-goal results. If many retrieved results are off-goal, the queries pull noise the goal rejects — tighten the queries. If a topic returns nothing for long stretches, the queries are too narrow or `--search-window` too tight — broaden them. If the user dismisses alerts, the goal is too broad — add an intent-specific `Ignore ...`. The aim is high precision with enough recall: every alert worth acting on, nothing real missed.
