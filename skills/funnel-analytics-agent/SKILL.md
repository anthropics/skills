---
name: funnel-analytics-agent
description: Daily morning brief + real-time anomaly alerts for indie launches. Reads Vercel + OpenPanel + HyperDX + Supabase + Product Hunt + GitHub Stars + VibeX into one 30-second markdown brief. Use during a Product Hunt launch, when 5+ dashboards are eating an hour a day, or before any decision that depends on cross-source funnel data.
---

# Funnel Analytics Agent

Solo Founder OS agent #5. Collapses 6+ launch-day dashboards (Vercel, OpenPanel, HyperDX, Supabase, Product Hunt, GitHub) into a single morning markdown brief + a cron-triggered alert that exits non-zero if anything is on fire.

## When to use this skill

Invoke this skill when:

- The user is in launch week (Product Hunt, HN, Reddit) and needs every-7-minutes anomaly detection
- A daily 7 AM cron should land a "what changed overnight" markdown brief in the operator's inbox
- The user asks "are my crons running" / "what's the funnel look like today" / "is the launch on track"
- A retro is needed for PH+24h post-mortem (`--retro` mode)
- The user is cycling between Vercel + OpenPanel + HyperDX + Supabase tabs for more than 20 minutes a day

## What it does

1. **Fetches via 9 source adapters**: Vercel deployments, Product Hunt votes/comments/momentum, OpenPanel analytics, HyperDX errors, Supabase advisor warnings, GitHub Stars, VibexSource (Supabase Management API), and 2 more
2. **Per-source failure isolation** — Vercel API down doesn't kill PH stats fetch. Source abstraction (`sources/base.py`) returns a `SourceReport` per provider
3. **Severity ladder**: `info` → `warn` → `alert` → `critical`. 7-day baseline lookup auto-promotes severity on >50% drops
4. **Brief composer** outputs structured markdown: critical → alert → warn → metrics-by-source → unavailable. Designed for 30-second read at 7 AM
5. **CLI modes**: `--brief` (default daily), `--alert` (exit 2 on critical for cron pipelines), `--retro` (PH+24h post-mortem markdown), `--source <name>` (single-provider drill)
6. **Pure stdlib HTTP** (`urllib.request` + `json`) — fast `pip install`, zero supply-chain surface

## Examples

### Example 1: PH launch-day cron

User: "Set me up for every-7-minute alerts during Monday's PH launch + daily brief at 7 AM"

Skill output (cron pattern):
```cron
# Every 7 minutes on Monday — alert mode + push if critical
7,17,27,37,47,57 * * * 1 funnel-analytics-agent --alert || \
  curl -d "PH alert" ntfy.sh/alex-launch

# Daily brief at 7:03 AM, written to alex-brain
3 7 * * * funnel-analytics-agent \
  --out ~/Documents/alex-brain/morning-briefs/$(date +%Y-%m-%d).md
```

Sample brief output:
```
# Morning Brief — 2026-05-04

## 🔴 CRITICAL (1)
- Product Hunt: only 23 votes after 4 hours on launch day
  (7-day baseline at this hour: 87). Investigate hunter activity now.

## 🟡 WARN (2)
- Vercel: 2 failed deployments in last 24h (was 0 the prior 6 days)
- Supabase advisor: 4 new RLS warnings since yesterday

## 🟢 OK
- OpenPanel: 1,247 visits (+18% vs 7-day avg)
- HyperDX: 0 errors in last 24h
- GitHub: +12 stars (running total: 487)
```

### Example 2: PH post-mortem retro

User: "PH launch ended 24h ago, give me the retro"

Skill: Runs `--retro` mode, fetches 48h of all-source data, generates markdown with hourly rank/comments/votes timeline, top traffic spikes from OpenPanel, error budget burn from HyperDX, and milestone tweets sent vs. planned.

## Guidelines

- **Read-only across all sources** — this skill never mutates Vercel deployments, Product Hunt votes, Supabase rows, or anything else. Operator decides what to do with the alerts
- **Exit code 2 on `--alert` mode when any source returns `critical`** — wire this into a cron pipeline with `||` for push notifications
- **Always include "unavailable sources" section in the brief** — silent missing data is worse than a flagged unavailable provider
- **Baseline rotation is automatic** — `baseline.jsonl` gz-rotates at 10 MB. Don't manually trim
- **Push notifications go through `Notifier` adapters** (Ntfy, Telegram, Slack) — urgent priority on Ntfy vibrates phone through DnD
- **Never report a metric without a baseline comparison** — "1,247 visits" is meaningless; "1,247 visits (+18% vs 7-day avg)" is actionable

## Configuration

The skill expects environment variables for read-only API access (skip any that are missing — that provider gets flagged in the brief header):

- `VERCEL_TOKEN` — Vercel API read scope
- `PRODUCT_HUNT_TOKEN` — GraphQL v2 dev token
- `OPENPANEL_CLIENT_ID` + `OPENPANEL_CLIENT_SECRET`
- `HYPERDX_API_KEY`
- `SUPABASE_PROJECT_REF` + `SUPABASE_ANON_KEY`
- `GH_TOKEN` — for GitHub Stars source
- `ANTHROPIC_API_KEY` — optional, enables Claude-summarized brief (v0.5+) at top of markdown
- `NTFY_TOPIC` / `TELEGRAM_BOT_TOKEN` / `SLACK_WEBHOOK` — optional notifiers

## Provenance

This skill wraps the open-source [funnel-analytics-agent](https://github.com/alex-jb/funnel-analytics-agent) (MIT, PyPI: `pip install funnel-analytics-agent`) — one of 11 agents in the Solo Founder OS stack at github.com/alex-jb/solo-founder-os. Currently shipped at v0.12.0 with 91 passing tests, 9 source adapters, `--retro` mode for PH+24h post-mortems, and an MCP server for Claude Desktop.

## See the rest of the stack

The full Solo Founder OS canonical 7-layer one-person-company runtime includes 10 sibling agents covering: monthly cost audit, pre-push code review, multi-platform marketing (12 channels incl 小红书 / 即刻 / 知乎 / B站), customer discovery, sales / cold email, customer support, payments, bilingual EN/ZH content sync, and the SFOS core framework. Browse the meta-repo at `alex-jb/solo-founder-os-skills`.
