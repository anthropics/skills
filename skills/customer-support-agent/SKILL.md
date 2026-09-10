---
name: customer-support-agent
description: Triages incoming user messages, drafts replies via Claude, queues every draft for human review before sending. Use when a solo founder's support inbox starts taking more than 30 min/day, when launch traffic floods the contact form, or when reply latency starts costing churn.
---

# Customer Support Agent

Solo Founder OS agent #9. Triages incoming user messages (email, contact form, GitHub issues, Discord DMs) and auto-drafts reply candidates for the operator to review and send. Never auto-replies — closes the 5th of the 7 canonical one-person-company layers.

## When to use this skill

Invoke this skill when:

- The user's support inbox is taking more than 30 min/day and the queue is still growing
- Launch traffic is about to multiply the contact-form volume 10×
- A churn investigation surfaces "we took 3 days to reply" as a top cancel reason
- The user wants every message triaged into bug / feature-request / billing / "needs-founder" buckets before deciding what to read
- A standard FAQ-style answer needs to be drafted with project-specific context (release notes, known issues) embedded

## What it does

1. **Ingest** support messages from configured sources (IMAP inbox, GitHub issues webhook, contact-form Supabase rows, Discord DM export)
2. **Triage classifier** assigns each message to one of: `bug` / `feature-request` / `billing` / `usage-question` / `needs-founder` / `spam`. Confidence score attached
3. **Reply drafter** (Claude Haiku 4.5 for FAQ-style, Sonnet 4.6 for nuanced cases) — pulls in project release notes, known-issue list, and the user's prior thread history as context
4. **HITL markdown queue** — each draft → `queue/pending/<timestamp>-<user>-<triage_label>.md`. Operator reviews in Obsidian, moves to `approved/` (sender picks up) or `rejected/`
5. **Tone presets** per project — match the founder's actual voice rather than a generic support tone
6. **Severity escalation** — `needs-founder` triage bucket always surfaces at the top of the queue with a `!critical` flag

## Examples

### Example 1: Morning inbox triage

User: "Triage everything in my support inbox from last 24h"

Skill output:
```
# Support Triage — 2026-06-06 08:14

12 messages processed.

## 🔴 needs-founder (2)
- enterprise-buyer@biggco.com: "Procurement question about SOC2"
  → queue/pending/2026-06-06-0814-biggco-needs-founder.md
- partner@othertool.com: "Co-marketing partnership"
  → queue/pending/2026-06-06-0814-othertool-needs-founder.md

## 🟡 bug (4)
- alice@example.com: "Project page crashes on Safari iOS 17.3"
  → queue/pending/...
[3 more]

## 🟢 usage-question (4) — drafts ready
- bob@example.com: "How do I export my project as PDF?"
  Draft cites docs/export.md + offers 1-click solution
  → queue/pending/...
[3 more]

## ⚪ spam (2) — auto-archived
```

### Example 2: Draft with release-note context

User: "Draft a reply for the user asking 'when will dark mode ship?'"

Skill: Pulls the latest 3 release-note files from the project, finds that "dark mode" is listed as in-progress for v0.21, drafts a reply that says exactly that with a link to the GitHub issue + an offer to ping when it ships. Lands in `queue/pending/`. Operator reviews, may add a personal "thanks for asking — you're the 4th person this week" line, then moves to `approved/`.

## Guidelines

- **Never auto-send. Always queue for human review.** Even on `usage-question` with 99% confidence — a wrong answer here costs more than the time saved
- **Triage confidence below 0.7 → escalate to `needs-founder`** rather than guess. The operator reads it
- **Release-note context is required** — drafting "dark mode is coming soon" without checking what's actually on the roadmap produces hallucinations that damage trust
- **Tone preset is non-negotiable per project** — VibeXForge support voice is not the same as Orallexa support voice. Configure per project before first run
- **Prior thread history is always loaded** — replying to a user who already complained 3 times without acknowledging that is worse than not replying
- **Spam bucket auto-archives, but logs** — operator can review the spam log weekly to catch classifier drift
- **Never invent fix ETAs, refund amounts, or feature commitments** — the LLM proposes; the founder commits

## Configuration

Required:
- `ANTHROPIC_API_KEY` — for Haiku 4.5 / Sonnet 4.6 drafting

Source-specific (at least one required):
- `IMAP_HOST` + `IMAP_USER` + `IMAP_PASS` — inbox source
- `GH_TOKEN` + `GH_REPO` — GitHub issues source
- `SUPABASE_PROJECT_REF` + `SUPABASE_ANON_KEY` + `CONTACT_FORM_TABLE` — Supabase contact-form source
- `DISCORD_BOT_TOKEN` + `DISCORD_CHANNEL_ID` — Discord source

Optional:
- `CUSTOMER_SUPPORT_QUEUE_ROOT` — defaults `~/.customer-support-agent/queue/`
- `CUSTOMER_SUPPORT_TONE_PRESET` — path to per-project tone YAML

## Provenance

This skill wraps the open-source [customer-support-agent](https://github.com/alex-jb/customer-support-agent) (MIT, PyPI: `pip install customer-support-agent`) — one of 11 agents in the Solo Founder OS stack at github.com/alex-jb/solo-founder-os. Currently shipped at v0.1.0 with 25 passing tests, closing the 5th of 7 canonical one-person-company layers.

## See the rest of the stack

The full Solo Founder OS canonical 7-layer one-person-company runtime includes 10 sibling agents covering: monthly cost audit, pre-push code review, multi-platform marketing (12 channels incl 小红书 / 即刻 / 知乎 / B站), customer discovery, sales / cold email, payments, analytics, bilingual EN/ZH content sync, and the SFOS core framework. Browse the meta-repo at `alex-jb/solo-founder-os-skills`.
