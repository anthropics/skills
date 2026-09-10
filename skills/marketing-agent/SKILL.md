---
name: marketing-agent
description: Auto-generates platform-specific launch copy for 9 channels (X / Threads / LinkedIn / Reddit / HN / Dev.to / Bluesky + 小红书/知乎 dry-run), runs a critic + dedup quality gate, Thompson-sampling variant bandit, trends-driven proactive loop, and ships drafts to a markdown HITL queue. Use during a PH/HN launch week, for daily auto-drafts from commits + trending topics, or when 30 min/day is being spent rewriting the same post for 6 platforms.
---

# Marketing Agent

Auto-promo agent for solo founders launching across 9 platforms simultaneously. Drafter → Critic → Rewriter supervisor (Reflexion-lite), reflexion memory, hybrid retrieval dedup, variant bandit, best-time-to-post, HITL queue, MCP server, A2A agent card. Production-grade — used to support VibeXForge's PH launch.

## When to use this skill

Invoke this skill when:

- The user is launching on Product Hunt / HN / Reddit / Dev.to in the same week and needs platform-tuned copy
- A daily cron should produce drafts from BOTH recent commits AND trending topics (proactive loop)
- The user asks "draft a launch post for <platform>" or "generate this week's marketing"
- A variant test needs to ship (Thompson-sampling bandit picks emoji-led vs question-led vs stat-led per platform)
- 小红书 / 知乎 dry-run previews are needed for manual publishing (these platforms are NEVER auto-published — see anti-bot strategy below)

## What it does

1. **Drafter → Critic → Rewriter supervisor** (Reflexion-lite):
   - Heuristic critic (hype words, char limits, caps, hashtag spam)
   - LLM critic (Haiku 4.5 when keyed; harsher of the two wins)
   - Heuristic rewriter (strip hype, de-shout, trim, cap hashtags)
   - Anthropic Agent SDK adapter with graceful fallback
2. **Reflexion memory** — SQLite log of past critique findings, prepended to next LLM prompt as "patterns to avoid"
3. **Hybrid retrieval dedup** — 60% dense_cosine + 40% BM25_normalized (+17pp MRR vs dense-alone). Catches paraphrased reposts
4. **Variant bandit** — Thompson sampling Beta(α,β) per (platform, variant_key). X currently runs 3 variants: emoji-led / question-led / stat-led
5. **Best-time-to-post** — hour-of-week empirical CDF over engagement history
6. **HITL markdown queue** — `queue/{pending,approved,posted,rejected}/`. Human moves via `git mv` → `publish.yml` triggers post
7. **Trends-driven proactive loop**: `trends.py` aggregates GitHub trending + HN Algolia + Reddit JSON (stdlib-only); `trends_to_drafts` converts to platform-specific drafts; daily cron drafts about your platform's own hot projects via `vibex_trends`
8. **Foot-guns wired**: `trend_memory` per-(project, URL) 7d cooldown + daily LLM budget cap (`MARKETING_AGENT_DAILY_BUDGET_USD`) + per-project breakdown in daily issue body
9. **Cross-agent SFOS interop** — ReflexionMemory + PreferenceStore + bandit + autopsy promoted to SFOS v0.13 core so vc-outreach / bilingual / funnel-analytics can reuse

## Examples

### Example 1: Daily cron draft

User: "Run today's marketing draft cycle"

Skill output:
```
# Marketing Agent — daily run 2026-06-06 14:00 UTC

Projects: vibexforge, orallexa, marketing-agent
Trends ingested: 27 (GitHub: 9, HN: 12, Reddit: 6, VibeX: 0 new)
Commit-driven drafts: 4
Trend-anchored drafts: 11
Critic pass rate: 14/15 (1 BLOCK on hashtag spam in x-orallexa-stat-led)
LLM budget used: $0.34 / $1.00 daily cap

Drafts queued in queue/pending/:
  - x-vibexforge-emoji-led-2026-06-06.md
  - threads-vibexforge-2026-06-06.md
  - linkedin-vibexforge-2026-06-06.md
  - devto-vibexforge-2026-06-06.md
  - reddit-claudeai-marketing-agent-2026-06-06.md
  - xiaohongshu-vibexforge-2026-06-06.dry_run.md   ← manual paste only
  - zhihu-vibexforge-2026-06-06.dry_run.md         ← manual paste only
  [...]

Bandit picks for today:
  x: stat-led (Beta α=12 β=4, expected CTR 0.71)
  threads: emoji-led (Beta α=8 β=3)
```

### Example 2: 小红书 dry-run preview

User: "Draft a 小红书 post for VibeXForge but don't publish"

Skill: Runs `xiaohongshu.dry_run_preview()` — produces a platform-tuned 1500-character post with:
- AI-disclosure reminder banner at top
- 3-hook templates (curiosity / contrast / numbered list) for the operator to pick
- Length classifier (1500-char "深度" vs 600-char "速读")
- Tag suggestions
- Output marked `.dry_run.md` so it never accidentally enters the auto-publish path

Operator hand-pastes at `creator.xiaohongshu.com`.

## Guidelines

- **Never auto-send. Always queue for human review.** Even on platforms with API access (X, Threads, LinkedIn, Reddit, Dev.to). Human moves `queue/pending/` → `queue/approved/` and `publish.yml` triggers
- **NEVER auto-publish to 小红书 / 知乎.** Q2 2026 anti-bot research locked this: 小红书 阿瑞斯 risk system uses TLS fingerprinting + behavioral models, new accounts need 2-4 weeks 养号, 37 matrix accounts banned in one Jan 2026 sweep, 知乎 has no public publishing API since 2020. We ship `dry_run_preview()` content; operator pastes manually
- **Daily LLM budget cap is hard** — `MARKETING_AGENT_DAILY_BUDGET_USD` is enforced before each LLM call. Over-budget → fall back to heuristic-only drafts
- **Trend memory cooldown is per-(project, URL)** — default 7 days. The same HN article never gets drafted twice for the same project within a week
- **Banned-hype-word list is enforced in critic** — drafts containing "revolutionary", "game-changing", "synergy", "leverage" trigger a rewrite. Don't disable
- **Variant bandit needs >30 posts of history before it converges** — early on, expect Thompson sampling to look noisy. That's correct
- **Template fallback is real** — stale or missing `ANTHROPIC_API_KEY` → heuristic-only path still ships drafts. LLM unlocks supervisor + reflexion depth but is not required

## Configuration

Required for publishing (any subset):
- `X_BEARER_TOKEN` / `X_API_KEY` etc — for X auto-publish
- `THREADS_ACCESS_TOKEN` — Meta Graph API
- `LINKEDIN_ACCESS_TOKEN`
- `REDDIT_CLIENT_ID` + `REDDIT_CLIENT_SECRET` + `REDDIT_USER_AGENT`
- `DEVTO_API_KEY`
- `BLUESKY_HANDLE` + `BLUESKY_APP_PASSWORD`

Optional:
- `ANTHROPIC_API_KEY` — enables Drafter + Critic + Rewriter LLM path
- `MARKETING_AGENT_DAILY_BUDGET_USD` — hard daily cap, default $1.00
- `MARKETING_AGENT_QUEUE_ROOT` — defaults `~/.orallexa-marketing-agent/queue/`
- `USAGE_LOG_PATH` — cross-provider usage logging (Anthropic + Cloudflare + LiteLLM ensemble)

Optional extras:
- `pip install "orallexa-marketing-agent[mcp]"` — MCP server
- `pip install "orallexa-marketing-agent[embeddings]"` — local sentence-transformers for dedup
- `pip install "orallexa-marketing-agent[agent_sdk]"` — Anthropic Agent SDK

## Provenance

This skill wraps the open-source [marketing-agent](https://github.com/alex-jb/orallexa-marketing-agent) (MIT, PyPI: `pip install orallexa-marketing-agent`) — one of 11 agents in the Solo Founder OS stack at github.com/alex-jb/solo-founder-os. Currently shipped at v0.18.1 with 384 passing tests at 77% coverage, CI green on Python 3.11/3.12, 20 GitHub releases, 6 Actions workflows, MCP server, A2A agent card, and the trends-driven proactive loop wired into daily cron.

## See the rest of the stack

The full Solo Founder OS canonical 7-layer one-person-company runtime includes 10 sibling agents covering: monthly cost audit, pre-push code review, customer discovery, sales / cold email, customer support, payments, analytics, bilingual EN/ZH content sync, and the SFOS core framework. Browse the meta-repo at `alex-jb/solo-founder-os-skills`.
