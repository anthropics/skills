---
name: wrap-up
description: Close out (or revisit) a Claude Managed Agent build — regenerate the overview page, recap every primitive the founder now owns, show the run log and live status, suggest 1–2 tailored next upgrades, and sweep hygiene (sessions archived, key only in .env, no literal dates in deployment kickoffs). Use when the founder says "/wrap-up", "wrap up", "close it out", "where do things stand with my agent", or at the end of a /launch-your-agent build.
license: Complete terms in LICENSE.txt
version: 0.2.0
dependencies: A `./my-agent/` folder from /launch-your-agent. ANTHROPIC_API_KEY in `my-agent/.env` optional — without it the wrap-up is describe-only.
---

# Wrap-up — celebrate it, show what they built, point at what's next

You are closing out (or checking in on) a founder's Claude Managed Agent. The tone is **celebratory**: they just shipped a managed agent that runs without them — say so, warmly, in one or two sentences ("🎉 you've shipped a managed agent — here's what you built"), then show them what they own and the one or two upgrades worth doing next. End on the overview page, not a wall of text. This is a moment, not a checklist read-out.

Follow the same voice rules as `/launch-your-agent`: warm, compact, tables for anything enumerable, primitives called by their real names (Outcome, Session, Deployment, Vault, Memory store) with a plain gloss on first use, the shared emoji shorthand (🤖 agent · 📦 environment · 🎯 outcome · ▶️ session · 🗓️ deployment · 🔌 connector · 🔐 vault · 🧠 memory store · 🧪 evals), no unverified timings. **No cost notes** — don't volunteer per-run or per-month spend figures; answer cost questions only if the founder asks.

## 1. Read the state

- Read `./my-agent/`: `build-sheet.json`, `IDS.env`, `NEXT-DIRECTIONS.md`, `outcome.md`, `evals/`, the existing `agent-overview.html`. (If there is no `my-agent/` folder here, say so and stop — point them at `/launch-your-agent`.)
- If `my-agent/.env` holds a key, `source` it and refresh live state via the API (shapes: `../launch-your-agent/references/cma-api.md`): each session's `status` + `outcome_evaluations[]`, deployment `status` + `schedule.upcoming_runs_at`, latest `usage`. Parse with python (`strict=False`), never jq.
- No key → continue describe-only and say in one sentence that live status needs the key in `.env`.
- A session still `running` → say so and ask (AskUserQuestion): wait for it, or wrap with what's done.
- Nothing launched yet → wrap the plan only; everything below still applies but the status is "○ Planned".

## 2. Produce the wrap-up (in this order)

1. **Congratulate them.** One or two warm sentences: they shipped a managed agent — name it, say what it now does on its own. 🎉
2. **Overview page.** Regenerate `agent-overview.html` (template: `../launch-your-agent/references/overview-template.html`) with live IDs, the run log, eval verdicts, the schedule with next run times, Console links for the key's workspace, and the v1/v2 next directions. **Open it in their browser** — the page is the closing artifact; the chat below just points at it.
3. **"Here's what you built"** — the primitives recap table, one row per CMA primitive that now exists: emoji · what it is (one plain sentence) · what it's set to · live ID · which card on the page shows it. Final muted row(s) for primitives deliberately not used → "see NEXT-DIRECTIONS". Follow with the run log table (run · rubric version · verdict · one-line note).
4. **"Here's what's next"** — 1–2 extensions picked from the v1/v2 plan that matter most for *this* use case, pitched concretely: what it does for them, what it takes, how small the change is. The rest of the plan stays written down. Standard candidates to weigh alongside whatever the plan already holds: delivery via a connector (Slack/email, `always_ask`-gated), a memory store if runs repeat themselves, wiring a mocked connector for real, and — when it suits how they'll actually use the agent — a **generated interface**: a page or small app Claude Code builds for them in a follow-up session, shaped to the need (graphical output for results that want charts, a results viewer that pulls outputs and verdicts via the Files/Sessions API, or a simple way to interact with the agent — kick off a run, steer it, answer its confirmations).
5. **Hygiene sweep — quiet by default.** Do the sweep (archive finished sessions; check the deployment's `initial_events` for literal dates; check the key only ever lived in `.env`; save a passed run as `evals/case-01/expected.md` if there's no golden case yet) and **fix silently what you can**. Only mention something if it's materially relevant — i.e. the founder must act (a key that touched chat → rotate; a literal date you can't patch without their say-so) or it changes how they use the agent. No "✅ all good" lists.
6. **Last words** — one short line: everything lives in their Console (platform.claude.com → Claude Managed Agents, in the key's workspace), this folder recreates it anywhere (`LAUNCH.md`), and they can rerun `/wrap-up` whenever they want a fresh picture.

## Notes

- Idempotent: running it again just refreshes the page and tables.
- Don't re-litigate design decisions here — this skill reports and suggests; changes go through `/launch-your-agent` (or a plain conversation) afterwards.
