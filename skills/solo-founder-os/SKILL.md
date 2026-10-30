---
name: solo-founder-os
description: The shared base library + 6-layer self-evolving framework that the other 10 SFOS agents are built on. Source/MetricSample contract, 7-day baseline with auto-rotation, Anthropic client with auto cost logging, prompt caching, structured outputs, batch API, notifiers, brief composer, HITL queue, scheduler, eval council + evolver loops, multi-machine sync, local observability dashboard. Use when starting a NEW solo-founder agent and want 4-hour scaffolding instead of 2-day boilerplate.
---

# Solo Founder OS

The framework wrapping the entire 11-agent stack. Phase 1 of the original SFOS roadmap, pulled forward because shipping 7 agents revealed 60-70% duplication and the founder chose "build the foundation right" over "ship more agents fast" on 2026-04-29.

## When to use this skill

Invoke this skill when:

- The user is starting a NEW solo-founder agent and wants the canonical scaffolding
- A new agent needs: source abstraction, 7-day baseline, Anthropic client with usage logging, brief composer, notifiers, HITL queue, scheduler — without writing them again
- The user asks "how do I structure a SFOS-compatible agent" / "give me the boilerplate"
- The user wants to set up the local observability dashboard (`sfos-ui`) to monitor all running agents
- A multi-machine sync is needed (`sfos-sync`) to keep agent state coherent across laptops
- The user wants the weekly eval council + evolver loops (skill drift detection + PR-gated self-improvement)

## What it provides

1. **`Source` ABC + `SourceReport` + `MetricSample`** — the contract every agent's fetch path uses. Severity ladder pinned to `["info", "warn", "alert", "critical"]`
2. **`urlopen_json` + `with_retry`** — pure stdlib HTTP with retry decorator (URLError / ConnectionError / TimeoutError default, exponential backoff 1s→2s→4s)
3. **`baseline.enrich_with_baseline` / `record_samples`** — 7-day median lookup, severity promotion on >50% drops, auto-rotation to `.gz` when log > 10 MB
4. **`AnthropicClient`** — wraps `anthropic.Anthropic` with graceful degrade (no key → None + error string, never raises) + automatic token usage logging + prompt caching (v0.4+) + structured outputs (v0.5+) + Batch API path at 50% off (v0.5+)
5. **`Notifier` ABC + Ntfy / Telegram / Slack** — `fan_out()` helper, urgent priority on Ntfy vibrates phone through DnD
6. **`compose_brief` + `has_critical`** — markdown report renderer with severity sections + optional Claude summary at top
7. **`HitlQueue` + CLI** — markdown queue primitives every agent uses for human-in-the-loop review
8. **Scheduler** (v0.3+) — cron-style + launchd plist generators
9. **Eval council + evolver + retro** (v0.13+) — `sfos-eval`, `sfos-council`, `sfos-evolver`, `sfos-retro` CLIs; 4-job Sunday cron on launchd
10. **Local observability dashboard** — `sfos-ui` serves a localhost dashboard of all 11 agents' last run, errors, usage, queue depth
11. **Multi-machine sync** — `sfos-sync` keeps agent state coherent across laptops
12. **Testing helpers** — `fake_urlopen_ok`, `fake_anthropic`, `make_metric`, `make_report`, `tmp_baseline_path`. First test file of a new agent goes from 50 boilerplate lines to actual test logic

## Examples

### Example 1: Scaffold a new agent

User: "Start a new agent called `competitor-watch-agent` using SFOS conventions"

Skill output:
```
✓ Created competitor-watch-agent/
  ├── competitor_watch_agent/
  │   ├── __init__.py
  │   ├── __main__.py        (CLI with --brief / --alert / --out)
  │   ├── sources/
  │   │   └── base.py         (re-exports solo_founder_os.Source)
  │   └── digest.py           (uses solo_founder_os.compose_brief)
  ├── tests/
  │   ├── conftest.py         (imports from solo_founder_os.testing)
  │   └── test_smoke.py       (10 passing tests pre-wired)
  ├── pyproject.toml          (dep on solo-founder-os>=0.27)
  └── README.md (EN) + README.zh-CN.md (ZH)

Next steps:
  pip install -e .
  pytest                       (10 / 10 passing)
  competitor-watch-agent --brief
```

### Example 2: Local observability dashboard

User: "Show me what all 11 agents are doing right now"

Skill:
```
$ sfos-ui
Serving Solo Founder OS dashboard at http://127.0.0.1:7811

Last 24h across all agents:
  funnel-analytics-agent   23 runs, 0 errors, $0.014, queue: 0
  marketing-agent           1 run,  0 errors, $0.34, queue: 11 pending
  customer-discovery-agent  1 run,  0 errors, $0.04, queue: 1 digest
  cost-audit-agent          1 run,  0 errors, $0.00, queue: 0
  bilingual-content-sync-agent  0 runs (idle)
  vc-outreach-agent         3 runs, 0 errors, $0.08, queue: 2 pending
  customer-support-agent    8 runs, 0 errors, $0.02, queue: 4 pending
  payments-agent            1 run,  0 errors, $0.00, queue: 5 pending
  build-quality-agent       14 invocations across 3 repos, 2 BLOCKs, $0.008
  solo-founder-os           4-job Sunday cron healthy
  vibex-publish-agent       0 runs (v0.1 scaffolding)

Weekly LLM spend: $0.49 (cap: $5.00)
```

## Guidelines

- **One fix benefits all current AND future agents** — that's the whole point. Resist the urge to fork shared code into an agent. If a behavior is needed twice, lift it into SFOS
- **Pure stdlib for HTTP** — `urlopen_json` not `requests`. Keeps `pip install` fast and supply-chain surface minimal. Agents that need richer HTTP can opt in, but the SFOS contract stays stdlib
- **Graceful degrade on missing API key** is the canonical pattern — `AnthropicClient` returns `(None, error_string)`, never raises. Agents handle the None case with template fallback
- **Severity ladder is fixed**: `info` → `warn` → `alert` → `critical`. New agents do NOT invent new levels
- **HITL queue is markdown files**, regex-parseable, hand-editable. Don't introduce a database
- **Baseline rotation is automatic** at 10 MB → gz. Don't manually trim
- **Weekly eval council + evolver loops are PR-gated** — self-improvement proposals land as PRs the operator reviews. No autonomous merge
- **Multi-machine sync via `sfos-sync`** is opt-in per agent — some agent state should never sync (per-machine API keys), some should (queue, baseline, eval log)

## Configuration

Minimal:
- `ANTHROPIC_API_KEY` — for the shared `AnthropicClient`. Without it, all agents fall through to template / heuristic mode

Per-feature opt-ins:
- `SFOS_USAGE_LOG_PATH` — cross-agent token usage log, default `~/.solo-founder-os/usage.jsonl`
- `SFOS_BASELINE_ROOT` — default `~/.solo-founder-os/baselines/`
- `SFOS_SKILLS_ROOT` — default `~/.solo-founder-os/skills/` (for skill_promoter)
- `SFOS_SYNC_REMOTE` — git remote for `sfos-sync`
- `SFOS_DAILY_BUDGET_USD` — global LLM budget cap across all 11 agents

CLIs available after install:
`sfos-eval / sfos-council / sfos-evolver / sfos-retro / sfos-cron / sfos-ui / sfos-sync / sfos-bus / sfos-inbox / sfos-doctor`

## Provenance

This skill wraps the open-source [solo-founder-os](https://github.com/alex-jb/solo-founder-os) (MIT, PyPI: `pip install solo-founder-os`) — the framework foundation for the 11-agent stack. Currently shipped at v0.27.4 LIVE on PyPI with 513 passing tests, 4-job Sunday cron on launchd, local observability dashboard, multi-machine sync, and weekly eval council + evolver loops. Operator-side: all 11 agents pip-installed locally via `pip install -e` + symlinked to `~/.local/bin` at <$0.06/week.

## See the rest of the stack

The full Solo Founder OS canonical 7-layer one-person-company runtime includes 10 sibling agents built on this framework, covering: monthly cost audit, pre-push code review, multi-platform marketing (12 channels incl 小红书 / 即刻 / 知乎 / B站), customer discovery, sales / cold email, customer support, payments, analytics, bilingual EN/ZH content sync, and a v0.1 publishing agent for 抖音 / 小红书 / B站. Browse the meta-repo at `alex-jb/solo-founder-os-skills`.
