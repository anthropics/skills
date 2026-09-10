---
name: cost-audit-agent
description: Monthly bill audit across Vercel, Anthropic, OpenPanel, HyperDX, Supabase, and GitHub Actions. Detects dollar-tagged waste findings and unused features. Use when reviewing monthly cloud / SaaS bills, before promoting infra changes to production, or when a budget alert fires.
---

# Cost Audit Agent

Audit recurring SaaS / cloud bills for a solo founder running multiple AI agents in production. Returns a dollar-tagged waste-findings report with severity classifications, so the operator can cut spend without breaking working systems.

## When to use this skill

Invoke this skill when:

- The user asks "what's costing us money?" / "audit my bills" / "find waste in my cloud spend"
- A monthly billing email arrives and the user wants a tight summary
- Before promoting infrastructure changes that might introduce new line items
- Quarterly cost reviews for OSS agents running on cron schedules

## What it does

For each provider in the configured list (default: Vercel, Anthropic, OpenPanel, HyperDX, Supabase, GitHub Actions):

1. **Pulls billing data** via provider API (read-only credentials)
2. **Cross-checks against usage**: which features are billed but not actually used?
3. **Flags advisor warnings**: Supabase advisor RLS issues that increase query cost; HyperDX retention that exceeds need; Anthropic cache misses
4. **Estimates overage projections**: GitHub Actions minutes used vs. plan limit, projected monthly run
5. **Outputs a Markdown brief** with three severity tiers:
   - 🔴 **WASTE** (cancel or scale down immediately) — feature is billed and unused
   - 🟡 **WATCH** (revisit in 30 days) — borderline use that may become waste
   - 🟢 **OK** (keep) — line item with confirmed productive use

## Examples

### Example 1: Routine monthly audit

User: "Audit my bills for May."

Skill output:
```
# Monthly Cost Audit — 2026-05

Total spend: $147.32 (was $156.81 in April, −6.1%)

## 🔴 WASTE ($12.40 / month)
- HyperDX: retention set to 90d, last query went back 11d. Cut to 30d → saves $8.50/mo
- OpenPanel: unused "Pro" tier sub-events, last fired 47 days ago → downgrade to Free → saves $3.90/mo

## 🟡 WATCH
- Supabase: 86 RLS policies wrapped in (select auth.uid()), 4 still unwrapped at 100+ rows/day query → projected +$2.40/mo if traffic 5x. Wrap before next launch.

## 🟢 OK
- Vercel: $19.20 (Hobby + builds), under cap
- Anthropic: $28.40 (~70% cache hit), within projection
```

### Example 2: Pre-launch sanity check

User: "I'm about to promote this Vercel deploy with new analytics — what's my cost exposure?"

Skill: Reads vercel.json + checks current plan + recent deploy frequency + estimates incremental cost. Flags if a new Cron + new Edge function would push past Hobby plan limits.

## Guidelines

- **Never invoke billing changes directly** — this is a read + report skill. Operator decides what to cut.
- **Always cite the exact API endpoint or dashboard URL** where the operator can verify the finding.
- **Prefer 30-day rolling windows** over monthly snapshots to catch trend changes faster.
- **Flag Anthropic prompt-caching opportunities** specifically: if cache-miss rate is climbing on a recurring agent, that's silent cost growth.
- **Never report dollar figures without a date range** — "saves $8.50/mo" is meaningful, "saves $8.50" alone is not.

## Configuration

The skill expects environment variables for read-only API access:

- `VERCEL_TOKEN` — Vercel API read scope
- `ANTHROPIC_API_KEY` — usage dashboard read
- `SUPABASE_PROJECT_REF` + `SUPABASE_ANON_KEY` — for advisor + usage
- `OPENPANEL_CLIENT_ID`
- `HYPERDX_API_KEY`
- `GH_TOKEN` — for Actions minutes

If a credential is missing, skip that provider and flag in the report header.

## Provenance

This skill wraps the open-source [cost-audit-agent](https://github.com/alex-jb/cost-audit-agent) (MIT, PyPI: `pip install cost-audit-agent`) — one of 11 agents in the Solo Founder OS stack at github.com/alex-jb/solo-founder-os. The Skills Marketplace version embeds the same logic with the YAML-frontmatter wrapper for Claude integration.

## See the rest of the stack

The full Solo Founder OS canonical 7-layer one-person-company runtime includes 10 sibling agents covering: pre-push code review, multi-platform marketing (12 channels incl 小红书 / 即刻 / 知乎 / B站), customer discovery, sales / cold email, customer support, payments, analytics, bilingual EN/ZH content sync, and the SFOS core framework. Browse the meta-repo at `alex-jb/solo-founder-os-skills`.
