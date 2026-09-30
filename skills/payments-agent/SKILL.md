---
name: payments-agent
description: Drafts overdue-invoice reminder emails with hard money-safety rules baked into the prompt and asserted in tests. Stripe-shaped types with MockProvider fallback (works without a Stripe key). Severity ladder: gentle (≤7d) / firm (8-30d) / final (>30d). Use when AR aging hits 7+ days, when invoices are quietly slipping past 30d, or to set up a weekly overdue sweep — never auto-sends.
---

# Payments Agent

Solo Founder OS agent #11. Drafts overdue-invoice reminders with money-safety constraints encoded in both the system prompt AND the test suite. Closes the 7th of 7 canonical one-person-company layers. Never auto-sends — every reminder ships through HITL queue.

## When to use this skill

Invoke this skill when:

- The user has 1+ invoices crossed 7 days overdue and wants the first nudge
- A weekly cron should sweep AR aging and draft severity-appropriate reminders
- An invoice is approaching 30 days and needs the firm / final-warning tone shift
- The user asks "what's overdue" / "who do I need to chase" / "draft the dunning email"
- The user wants to test the workflow without a real Stripe key (MockProvider path)

## What it does

1. **Fetches overdue invoices** from Stripe (or MockProvider if `STRIPE_API_KEY` is missing — works for demo + tests)
2. **Computes severity** per invoice:
   - **Gentle** — ≤7 days overdue
   - **Firm** — 8-30 days overdue
   - **Final** — >30 days overdue (last-warning tone, includes escalation hint)
3. **Drafts reminder via Claude** with hard money-safety rules in the system prompt:
   - NEVER thank the customer for the unpaid invoice
   - State EXACT amount (no rounding)
   - State EXACT days overdue (no fuzzing)
   - NEVER invent a payment link — only use the provider's actual hosted URL
4. **HITL markdown queue** — each draft → `queue/pending/<timestamp>-<customer>-<severity>.md`. Operator reviews, moves to `approved/` (sender picks up) or `rejected/`
5. **Money-safety asserted in tests** — the system prompt rules are not just commented intent; they're verified by the test suite so prompt rewrites can't drift them

## Examples

### Example 1: Weekly overdue sweep

User: "Run the weekly overdue sweep and queue reminders"

Skill output:
```
# Payments Sweep — 2026-06-06

Stripe AR aging snapshot:
  Outstanding total: $4,832.00
  Overdue invoices: 5

## 🟢 gentle (≤7d) — 2 drafts queued
- acme-co  $480.00, 3d overdue
  → queue/pending/2026-06-06-acme-co-gentle.md
- biggcorp $1,200.00, 6d overdue
  → queue/pending/2026-06-06-biggcorp-gentle.md

## 🟡 firm (8-30d) — 2 drafts queued
- midco   $850.00, 14d overdue
  → queue/pending/2026-06-06-midco-firm.md
- legacy  $1,500.00, 22d overdue
  → queue/pending/2026-06-06-legacy-firm.md

## 🔴 final (>30d) — 1 draft queued
- ghosted-llc $802.00, 47d overdue
  → queue/pending/2026-06-06-ghosted-llc-final.md
  ⚠ Final notice tone — review escalation path before sending
```

### Example 2: Draft inspection

User: "Show me the firm-tone draft for midco"

Skill output (contents of `queue/pending/2026-06-06-midco-firm.md`):
```markdown
---
mode: payments
customer: midco
invoice_id: in_1AbCdEfGhIjKlMn
amount_usd: 850.00
days_overdue: 14
severity: firm
status: pending
draft_id: 2026-06-06-1438
---

Subject: Invoice in_1AbCdEfGhIjKlMn — $850.00 — 14 days overdue

Hi midco team,

Invoice in_1AbCdEfGhIjKlMn for $850.00 was due on 2026-05-23 and is
now 14 days past due. Please settle at the hosted link below or
reply here to confirm a payment date this week.

Payment link: https://invoice.stripe.com/i/acct_xxx/in_1AbCdEfGhIjKlMn

— Alex
```

## Guidelines

- **Never auto-send. Always queue for human review.** Money-handling agents that mutate or transmit without HITL are how solo founders blow up customer relationships
- **Money-safety rules are tested, not just commented** — NEVER thank for unpaid invoice, EXACT amount, EXACT days overdue, NEVER invent payment link. Prompt rewrites that drop these MUST fail the test suite
- **Payment link must come from the provider** — Stripe's hosted invoice URL, not an LLM-generated string. MockProvider returns a clearly-fake URL so demos can't accidentally ship
- **Severity ladder is hardcoded by day count, not vibe** — 7-day and 30-day thresholds are not LLM judgment calls
- **Final-notice tone includes an escalation hint in the queue file** ("⚠ Final notice — review escalation path before sending") so the operator pauses before approving
- **Subject lines include invoice ID + amount + days overdue** — never euphemize ("quick reminder") for an overdue invoice
- **MockProvider is for demos, tests, and onboarding only** — never wire MockProvider into a real cron. Test suite asserts MockProvider returns a clearly-fake link

## Configuration

Optional (MockProvider fallback works without):
- `STRIPE_API_KEY` — for real AR aging fetch
- `ANTHROPIC_API_KEY` — for Claude-drafted reminders. Without it, template fallback ships

Optional:
- `PAYMENTS_QUEUE_ROOT` — defaults `~/.payments-agent/queue/`
- `PAYMENTS_GENTLE_THRESHOLD_DAYS` — defaults 7
- `PAYMENTS_FIRM_THRESHOLD_DAYS` — defaults 30
- `SMTP_HOST` + `SMTP_USER` + `SMTP_PASS` — for sender (still HITL-gated by `queue/approved/` move)

## Provenance

This skill wraps the open-source [payments-agent](https://github.com/alex-jb/payments-agent) (MIT, PyPI: `pip install payments-agent`) — one of 11 agents in the Solo Founder OS stack at github.com/alex-jb/solo-founder-os. Currently shipped at v0.1.0 with 21 passing tests, CI added 2026-05-08 (test/lint/release workflows from funnel-analytics-agent template, first run all green), closing the 7th of 7 canonical one-person-company layers.

## See the rest of the stack

The full Solo Founder OS canonical 7-layer one-person-company runtime includes 10 sibling agents covering: monthly cost audit, pre-push code review, multi-platform marketing (12 channels incl 小红书 / 即刻 / 知乎 / B站), customer discovery, sales / cold email, customer support, analytics, bilingual EN/ZH content sync, and the SFOS core framework. Browse the meta-repo at `alex-jb/solo-founder-os-skills`.
