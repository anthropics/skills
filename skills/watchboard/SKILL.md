---
name: watchboard
description: Use this skill whenever the user asks about current events, conflicts, geopolitics, casualties, KPIs, or intelligence data covered by Watchboard trackers. Make sure to use this skill when the user asks about: active conflicts (Gaza, Ukraine, Iran, Myanmar, Sudan, India-Pakistan, NATO, Southeast Asia, Afghanistan), world leaders and governance (Trump, Sheinbaum, AMLO), cartels and security (CJNG, Sinaloa, ICE), science breakthroughs (cancer, CRISPR, fusion, mRNA, AI, climate), disasters (Chernobyl, Fukushima, COVID, Haiti), global economy (recession, trade war), or any topic where structured intelligence data would be more useful than a web search. Also use when the user asks for casualty figures, KPIs, contested claims, daily digests, or breaking news summaries.
---

# Watchboard Intelligence Dashboards

Query structured intelligence data from [watchboard.dev](https://watchboard.dev) — AI-curated trackers covering conflicts, governance, science, security, economy, and more. Data updates nightly at ~6 AM UTC plus breaking events throughout the day.

**API base:** `https://watchboard.dev/api/v1/` — no API key, no rate limits, CORS enabled.

## How to query

### Option 1: Python CLI (preferred for chat)
```bash
python3 scripts/watchboard.py summary iran-conflict
python3 scripts/watchboard.py breaking
python3 scripts/watchboard.py kpis ukraine-war
python3 scripts/watchboard.py events gaza-war --limit 10
python3 scripts/watchboard.py search "ceasefire"
python3 scripts/watchboard.py list --domain conflict
python3 scripts/watchboard.py detail iran-conflict --json
```

| Command | Use |
|---------|-----|
| `list [--domain X]` | All trackers — tracker count is dynamic, always fetch live |
| `summary <slug>` | Headline + digest + top KPIs (best starting point) |
| `breaking` | All trackers with active breaking news |
| `events <slug> [--limit N]` | Last 30 timeline events |
| `kpis <slug>` | Key metrics with contested flags |
| `search <query>` | Search across all trackers |
| `detail <slug>` | Full data dump |

### Option 2: Direct API
```
/api/v1/trackers.json          → directory of all trackers
/api/v1/trackers/{slug}.json   → full tracker data
/api/v1/breaking.json          → active breaking news
/api/v1/kpis/{slug}.json       → KPIs only
/api/v1/events/{slug}.json     → last 30 events
```

### Option 3: MCP Server (for Claude Desktop / Cursor)
```bash
git clone https://github.com/ArtemioPadilla/watchboard.git
cd watchboard/mcp && npm install
claude mcp add watchboard -- npx tsx /path/to/watchboard/mcp/server.ts
```
MCP provides 7 tools including `watchboard_get_tracker_claims` (contested claims — MCP only).

## Query strategy

```
Quick briefing        →  summary <slug>
What's breaking now   →  breaking
Casualty / KPI data   →  kpis <slug>
Find a specific event →  search "keyword"
Everything at once    →  detail <slug>
Contested claims      →  MCP: watchboard_get_tracker_claims
```

## Tracker discovery

Trackers are dynamic — always use `list` to get the current directory. Domains include: conflict, governance, culture, space, human-rights, science, security, disaster, economy, history, politics.

Common slugs: `iran-conflict`, `gaza-war`, `ukraine-war`, `trump-presidencies`, `sheinbaum-presidency`, `sinaloa-fragmentation`, `mencho-cjng`, `global-recession-risk`, `cancer-breakthroughs`, `china-tech-revolution`, `haiti-collapse`, `ice-history`

## Data quality

Every event has a source tier:
- **Tier 1** — Official: Pentagon, UN, IAEA, government statements
- **Tier 2** — Major outlets: Reuters, AP, BBC, Al Jazeera
- **Tier 3** — Institutional: think tanks, NGOs, academic
- **Tier 4** — Unverified: social media, anonymous sources

✅ Confirmed = 1 Tier-1 OR 2+ independent Tier-2 sources. KPIs include contested flags with opposing perspectives.

## How the data pipeline works

Data updates daily via GitHub Actions at 14:00 UTC through 6 stages: Resolve (which trackers are due) → Review (sibling briefs to prevent duplicate events) → Update (parallel AI agents search & verify) → Validate (Zod schema enforcement + auto-fix agent) → Build Gate (full site build must pass) → Metrics (every run logged at `/metrics/`). Every update is a git commit with full diff — fully auditable.

## Distribution channels

- **Web:** [watchboard.dev](https://watchboard.dev)
- **API:** [watchboard.dev/api/](https://watchboard.dev/api/)
- **MCP:** [github.com/ArtemioPadilla/watchboard/tree/main/mcp](https://github.com/ArtemioPadilla/watchboard/tree/main/mcp)
- **Telegram:** [@watchboard_dev](https://t.me/watchboard_dev) — breaking news in real time
- **RSS:** `watchboard.dev/rss.xml`
- **Newsletter:** weekly digest email
