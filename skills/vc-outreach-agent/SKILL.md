---
name: vc-outreach-agent
description: Drafts personalized cold emails per (investor or customer, project) via Claude Sonnet 4.6, manages a markdown HITL queue, never auto-sends. Dual-mode — `--mode vc` for pre-seed raises, `--mode customer` for paying-customer outreach. Use before a raise, when a customer-discovery digest surfaces qualified leads, or any time generic cold email would burn a relationship.
---

# VC Outreach Agent

Cold-email drafter for solo founders running a pre-seed raise OR paying-customer outreach. Enforces traction-first opening, banned-vocab list, and a markdown HITL queue. Built specifically for Orallexa's pre-seed raise; generalized for any indie founder.

## When to use this skill

Invoke this skill when:

- The user is about to send investor cold emails and wants per-(investor, project) personalization
- A customer-discovery digest has surfaced qualified leads who need a tailored first-touch
- The user asks "draft a cold email to <investor> about <project>" or "<customer>" with `--mode customer`
- An IMAP reply needs threading + follow-up cadence (T+5d, T+12d declining conviction)
- A pipeline analytics question lands ("which thesis_hint pattern gets the highest reply rate")

## What it does

1. **Investor / Customer + Project data models** — `Investor` (name, firm, thesis_hint), `Project` (name, traction lines, recent shipped artifact, demand signal), `Draft` (subject, body, status)
2. **Drafter via Claude Sonnet 4.6** — cold email needs nuance; Sonnet beats Haiku here. Prompt enforces:
   - Sentence 1: one specific `thesis_hint → project` line. No "I follow your work"
   - Sentences 2-3: traction-first (one number, one shipped artifact, one demand signal)
   - Sentence 4: one specific ask ("15-min call this week" — never "any thoughts you have")
   - Body <110 words, subject <8 words
3. **Banned-vocab enforcement**: synergy, disrupting, passionate, leverage, innovative, cutting-edge, revolutionize, "I'd love to", "circle back", "touch base", "thought leader", "in the AI space", "exciting opportunity"
4. **Markdown HITL queue** — each draft → `queue/pending/<timestamp>-<project>-to-<investor>.md`. Operator reviews in Obsidian, moves to `approved/` or `rejected/`
5. **Dual mode** (v0.9.0+):
   - `--mode vc` (default): pre-seed raise, Sonnet
   - `--mode customer`: paying-customer outreach, Haiku default, verbatim `signal_text` gate, separate queue + usage log roots
6. **SMTP sender** (v0.2 roadmap): picks up `queue/approved/`, sends via configured SMTP, tracks IMAP replies

## Examples

### Example 1: VC mode — draft for a raise

User: "Draft a cold email from Orallexa to Garry Tan about our paper-trading P&L"

Skill output (writes to `queue/pending/2026-06-06-orallexa-to-garry-tan.md`):
```markdown
---
mode: vc
investor: garry-tan
firm: y-combinator
project: orallexa
status: pending
draft_id: 2026-06-06-1438
---

Subject: Quant agent +5,950 P&L over 30 days

Garry,

Your recent thread on "earnings calls + live retail" maps to what we
just shipped: 30-day paper-trading backtest of Orallexa's quant agent
returned +$5,950 P&L (n=128, 60.9% win rate, p<0.005) against the
SPCX-pure-play 8-ticker watchlist published nightly to GitHub Pages.

Three solo-founder companies have already wired their Polymarket positions
through it via the Calibrated Alert SDK.

15-min call this week to walk through the live track record?

— Alex
github.com/alex-jb/orallexa
```

### Example 2: Customer mode with verbatim signal

User: "We have a customer-discovery quote from r/SaaS user `indie_dev_42`: 'I wish there was a build-quality hook that ran the actual build before charging me Vercel minutes.' Draft a customer cold email."

Skill: Runs `--mode customer` with `--signal-text "I wish there was a build-quality hook that ran the actual build before charging me Vercel minutes"`. Drafter is required to quote the exact signal verbatim in sentence 1, then pitch build-quality-agent's `--build` flag. Lands in `queue/customer/pending/`.

## Guidelines

- **Never auto-send. Always queue for human review.** One bad email burns a relationship (investors talk to each other; customers screenshot). v0.1+ NEVER auto-sends
- **Verbatim signal_text gate in customer mode** — the signal quote MUST appear in the draft. If the LLM rewrites it, the draft is rejected before queueing
- **Banned vocab list is enforced post-generation** — any banned phrase triggers a regenerate. Don't disable this
- **Template fallback is real** — no `ANTHROPIC_API_KEY` → still produces personalized drafts via `thesis_hint` template substitution. Same `Draft` shape both paths
- **HITL is the moat, not a limitation** — the 1% personalization that matters comes from the founder's IRL context. The agent's job is to handle the 99% scaffolding
- **Separate queue roots for VC vs customer mode** — never mix the usage log, never cross-route to the wrong SMTP profile
- **Subject line discipline**: <8 words, no exclamation, no "quick question" / "circling back"

## Configuration

Required:
- `ANTHROPIC_API_KEY` — for Sonnet 4.6 (vc) or Haiku 4.5 (customer) drafting. Template fallback works without it

Optional:
- `VC_OUTREACH_QUEUE_ROOT` — defaults `~/.vc-outreach-agent/queue/`
- `CUSTOMER_OUTREACH_QUEUE_ROOT` — defaults `~/.vc-outreach-agent/queue/customer/`
- `SMTP_HOST` + `SMTP_USER` + `SMTP_PASS` — for v0.2 sender (still HITL-gated by `queue/approved/` move)
- `IMAP_HOST` — for reply tracking

## Provenance

This skill wraps the open-source [vc-outreach-agent](https://github.com/alex-jb/vc-outreach-agent) (MIT, PyPI: `pip install vc-outreach-agent`) — one of 11 agents in the Solo Founder OS stack at github.com/alex-jb/solo-founder-os. Currently shipped at v0.9.0 with 59 passing tests, MCP server for Claude Desktop, dual-mode (vc + customer) after merging the deprecated customer-outreach-agent on 2026-05-08, and live VibeX traction injection in vc mode.

## See the rest of the stack

The full Solo Founder OS canonical 7-layer one-person-company runtime includes 10 sibling agents covering: monthly cost audit, pre-push code review, multi-platform marketing (12 channels incl 小红书 / 即刻 / 知乎 / B站), customer discovery, customer support, payments, analytics, bilingual EN/ZH content sync, and the SFOS core framework. Browse the meta-repo at `alex-jb/solo-founder-os-skills`.
