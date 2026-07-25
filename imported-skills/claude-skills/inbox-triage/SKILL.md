---
name: inbox-triage
description: "Runs a full inbox triage using the knowledge base created by the 'inbox-setup' skill. Light-intake by design (most invocations skip questions and run with KB-default preferences); asks at most 2 grill-me override questions when invocation is outside normal cadence or includes category-skip intent. Searches recent emails, classifies them via the user's taxonomy, researches new senders, generates recommendations, drafts replies (NEVER sends), delivers a report in the user's preferred format, and updates the knowledge base with learnings. Designed to run on a recurring schedule (1-3x daily) or on demand. Use when the user wants their inbox processed, in any variation (e.g., 'triage my inbox', 'inbox triage', 'check my email', 'run email triage', 'process my inbox', 'what's new in my email', 'handle my email', 'email triage'). Requires the inbox-setup skill to have been run first."
license: MIT
metadata:
  source_spec: "megaprompts/07-inbox-triage-megaprompt.md"
  build_pattern: "Path B (direct conversion)"
  paired_with: "inbox-setup (consumes the 7-file KB it produces)"
  version: 1.0.0
---

# Inbox-Triage — Recurring Email Triage

> **Paired with `inbox-setup`.** This skill consumes the 7-file knowledge base that `inbox-setup` writes at `${WORKSPACE}/Email/`. The file contracts MUST match exactly. See [`references/kb_file_contract.md`](references/kb_file_contract.md) — this is the mirror of the setup-side contract, viewed from the read side.

Run on a recurring schedule (1–3x daily) or on demand. Classify recent emails, research new senders, generate decision recommendations, draft replies (**NEVER SEND**), deliver a clean report, and update the knowledge base with what was learned this run.

## Invocation Triggers

- "triage my inbox"
- "inbox triage"
- "check my email"
- "run email triage"
- "process my inbox"
- "what's new in my email"
- "handle my email"
- "email triage"

## Prerequisites

Required reads at start (fail-fast if missing):

**Core (required):**
- `${WORKSPACE}/Email/email-taxonomy.md` — classification + report preferences
- `${WORKSPACE}/Email/email-patterns.md` — voice, persona, templates, hard rules

**Optional core (read if exists):**
- `${WORKSPACE}/Email/evaluation-framework.md`
- `${WORKSPACE}/Email/rate-card.md`

**Evolving (read AND update every run):**
- `${WORKSPACE}/Email/blocklist.md`
- `${WORKSPACE}/Email/tracker.md`

**Output:**
- `${WORKSPACE}/Email/triage-log/<YYYY-MM-DD>-<run-label>.md` — per-run log

If any core required file is missing → **halt**, direct user to run `inbox-setup` first. Use `scripts/kb_reader.py` to perform the read + validation.

## DRAFTS ONLY — Never Send

> **This skill creates drafts. It NEVER sends.**

This is the safety property that makes the skill safe to run automatically. Stated multiple times in this skill body. Non-negotiable.

The `scripts/draft_safety_validator.py` enforces it post-run. Any send-shaped tool call in the action log fails validation. See [`references/drafts_only_safety.md`](references/drafts_only_safety.md) for the full discipline canon.

## Step 0: Grill-Me Intake (Light — 0–2 Optional Override Questions)

Inbox-triage is **light-intake by design** — it runs on a recurring cadence with preferences pre-baked into the knowledge base from `inbox-setup`. The grill-me discipline here is asking ONLY the override questions that matter THIS run.

### Q1 (optional, asked only when on-demand run is outside normal cadence)

> **Override the default 9-hour search window? Pick: yes (specify hours) / no (use default).**
>
> *Why I'm asking:* If you're running on-demand outside your normal 2x/day cadence, you may want a wider window (24h after a long break) or narrower (2h for a quick check).

Skip if cadence is normal.

### Q2 (optional, asked only when user invokes with category-skip intent)

> **Skip any categories this run? E.g., "skip newsletters", "skip financial".**
>
> *Why I'm asking:* Sometimes you just want to scan opportunities or just want to clear active threads. Category skip narrows the run scope.

Skip if user gave no category-skip signal.

**Stop condition:** Max 2 questions. Default invocations skip both questions and run with KB-default preferences. The skill is optimized for fast recurring execution; intake is the exception, not the norm.

## Step 1: Determine Search Window

Compute via current date math. Default lookback: **9 hours** (works for 2x/day cadence with slight overlap so emails between runs aren't missed).

Use `scripts/search_window_calculator.py --cadence <CADENCE> --now <ISO>`:

```
now = current_datetime
window_start = now - 9_hours   (default for 2x-daily)
run_label = "Morning" if now.hour < 12 else "Afternoon" if now.hour < 17 else "Evening"
```

Cadence-to-default-window mapping (override via Q1):

| Cadence (from email-taxonomy.md S1.Q5) | Default window |
|---|---|
| once daily | 26h |
| 2x daily | 9h |
| 3x daily | 6h |
| on-demand only | 24h (asks Q1) |

## Step 2: Email Search

Two queries (provider-agnostic adapter pattern):

- **Primary:** Inbox + sent after `window_start`
- **Secondary:** Starred unread (catch flagged items missed in primary)

Collect for each email: sender, subject, date, snippet, thread ID, labels.

Provider adapter mapping:

| Provider | Tool |
|---|---|
| Gmail | Gmail MCP |
| Outlook / Microsoft 365 | Outlook MCP |
| IMAP (Fastmail, ProtonMail, etc.) | IMAP MCP if available; halt otherwise |
| (no email tool available) | Halt with clear message: "No email tool registered for this session." |

## Step 3: Classification

Apply the taxonomy from `email-taxonomy.md`. For **lowest-priority** category (newsletters / automation / spam): skip thread reads entirely — context cost not worth it. For everything else: read full thread.

## Step 4: Sender Research

For senders not in tracker / blocklist / prior logs:

1. Check `blocklist.md` → if matched, auto-skip
2. Check `tracker.md` → if known thread, note existing context
3. For opportunity senders (per evaluation framework): web search for company legitimacy, social presence, intermediary status

**Skip research entirely** for: known senders (in tracker), internal email, automated notifications, obvious low-priority.

## Step 5: Recommendations

For decision-required emails, apply the framework from `evaluation-framework.md`. Categorize:

| Category | When | Output |
|---|---|---|
| **TAKE IT** | Meets criteria | Recommend engaging; draft reply (Step 6) |
| **WORTH CONSIDERING** | Has potential, needs user judgment | Surface key context; draft for user to edit |
| **PASS** | Doesn't meet criteria | Brief "why" (1–3 sentences); draft polite decline |
| **FLAG FOR REVIEW** | Unusual; needs direct user decision | Surface fully; NO draft (user decides response shape) |

Each: brief "why", relevant context, pricing/timeline comparison if applicable.

**Skip Step 5 entirely if no `evaluation-framework.md` exists.**

See [`references/triage_decision_framework.md`](references/triage_decision_framework.md) for the framework canon.

## Step 6: Drafts

For every reasonable reply candidate, create a draft using `email-patterns.md` voice rules.

**Draft for:** opportunity responses (TAKE IT / WORTH / PASS), active conversations needing reply, action items, important personal emails.

**Do NOT draft for:**
- Clearly no-response emails (newsletters, automation, FYI)
- Threads where user already replied
- Blocked senders (unless new info changes the calculus)

**Mechanics:**

- Draft only in the existing thread when possible (preserves context)
- Set `to`, `subject` (`Re: [original]`)
- **NEVER call any send operation. Only create drafts.**

The draft body MUST honor:
- Voice register from `email-patterns.md`
- Forbidden tokens (S3.Q2 pet peeves)
- Sign-off patterns
- Persona context
- Hard rules (S3.Q6 — non-negotiable)
- Reply length per `email-patterns.md`

If `evaluation-framework.md` exists, draft tone matches recommendation:
- TAKE IT → engaged + concrete next step
- WORTH → curious + 1-2 clarifying questions
- PASS → polite decline + brief reason (no hedging promises)
- FLAG → NO draft

## Step 7: Report Delivery

Honor user's preference from `email-taxonomy.md` "Report Preferences" section. Default: email draft to self with HTML.

**Subject:** `Inbox Triage — [Day], [Month Date] ([Run Label])`

**Sections (in order):**

1. **Overview** — 2–3 sentences. What happened? Anything urgent?
2. **Stats** — Counts: processed, drafts created, action needed, skipped.
3. **Action Needed** — Overdue items, decisions, drafts to review, deadlines.
4. **Quick Reference** — One line per email, alphabetical by sender. `**Sender** — one-sentence summary + recommendation`.
5. **Detailed Cards** — Opportunities, active threads, flags. Each: sender / subject / category, recommendation + reasoning, key context. **NO draft text previews** (drafts are already in email client for user to read there).
6. **Footer** — Generation timestamp + KB update summary.

**Formatting (if HTML):**

- **Inline CSS only** (Gmail strips `<style>`)
- Color-coded by recommendation:
  - green → TAKE IT
  - amber → WORTH CONSIDERING
  - red → PASS
  - purple → FLAG FOR REVIEW
  - blue → active conversation

## Step 8: Knowledge Base Update

**`blocklist.md`** (append new):

- New declined senders + reason + date
- New decline patterns from observed behavior (e.g., "all emails containing 'looking for backend engineers' from gmail addresses → cold recruiter pattern")
- Remove entries if user has overridden them (user replied to a "blocked" sender → unblock)

**`tracker.md`** (append + update):

- New follow-ups for emails needing future action
- Update existing follow-ups (deadline changed, status changed)
- Mark resolved items complete
- Flag overdue items
- Remove resolved items older than 30 days
- Add entry to update log

**Learning patterns to observe over runs:**

- Drafts sent as-is vs. edited vs. deleted → tone calibration signal
- PASS recommendations user overrides → framework adjustment signal
- Engaged vs. ignored emails → taxonomy refinement signal
- New decline patterns → blocklist additions

After 5+ runs, suggest KB improvements to user (e.g., "You always decline emails from X — add as auto-skip?").

## Step 9: Internal Log

Save to `${WORKSPACE}/Email/triage-log/[YYYY-MM-DD]-[run-label].md`:

- Emails processed with classifications
- Recommendations made
- Drafts created (with IDs / thread refs)
- KB updates made
- Follow-ups added / resolved
- Notable observations (patterns surfaced, edge cases handled)

The log is the audit trail for `scripts/draft_safety_validator.py` to scan for send operations post-run.

## Step 10: Empty Inbox Handling

Even with zero new emails:

1. Check `tracker.md` for items due today or overdue
2. Generate minimal report: "No new actionable emails since last run"
3. Flag any overdue items
4. Escalate per tracker rules

Skip Steps 3–6 entirely on empty inbox.

## Critical Rules (Stated Multiple Times)

1. **DRAFTS ONLY — NEVER SEND.** Non-negotiable. Stated again here.
2. **Privacy.** No passwords / credentials in KB. Reference threads by ID for sensitive content.
3. **Accuracy over speed.** When unsure, flag for review. A wrong auto-draft is worse than no draft.
4. **Respect the KB.** Documented preferences are source of truth. Don't override with judgment.
5. **Transparency.** Note every KB change in the triage log.
6. **First runs need oversight.** Document this expectation for the user.

## Error Handling

| Situation | Behavior |
|---|---|
| KB files missing | Halt; direct user to run `inbox-setup` |
| Email tool unavailable | Halt with clear message about required tool |
| Web search unavailable for sender research | Skip research step; note senders not researched |
| Draft creation fails | Skip that draft; note in log; report continues |
| Report delivery fails | Save report to file as fallback; notify user |
| User has 100+ new emails | Stay within reasonable limits; flag volume; offer to focus on priority categories only |
| Sender appears in both blocklist and tracker | Tracker wins (active conversation); note inconsistency in log |

## Portability

- **Claude Code CLI:** Native — uses Gmail / Outlook MCP, file tools for KB, web search for research.
- **Claude.ai web:** Works when email MCP connector is connected (Gmail MCP available). Skill must check tool availability before assuming. If no email tool: halt with clear message.

## Tooling

| Script | Role |
|---|---|
| `scripts/kb_reader.py` | Reads + validates the 7-file KB. Returns parsed structure. Halts with explicit error if required files missing. |
| `scripts/search_window_calculator.py` | Computes `window_start` from cadence + current time. Returns `run_label`. Honors Q1 override. |
| `scripts/draft_safety_validator.py` | Post-run scan of the action log for any send-shaped tool call. FAILs if detected. The deterministic enforcement of the NEVER-SEND rule. |

## References

- [`references/kb_file_contract.md`](references/kb_file_contract.md) — canonical 7-file contract (read perspective; mirrors `../inbox-setup/references/kb_file_contract.md`)
- [`references/triage_decision_framework.md`](references/triage_decision_framework.md) — TAKE IT / WORTH / PASS / FLAG taxonomy
- [`references/drafts_only_safety.md`](references/drafts_only_safety.md) — the NEVER-SEND discipline canon

## Anti-Patterns To Reject

- **Sending emails** (drafts only — non-negotiable)
- Operating without knowledge base files
- Storing passwords / credentials in KB
- Skipping the learning loop (KB updates) at end of run
- Overriding user's documented preferences with own judgment
- Reading lowest-priority threads (waste of context)
- Including draft text previews in report (drafts are already in email client)
- Provider lock-in without adapter pattern
- Silently failing on missing tools

---

**Version:** 1.0.0
**Source spec:** [`megaprompts/07-inbox-triage-megaprompt.md`](../../../../megaprompts/07-inbox-triage-megaprompt.md)
**Build pattern:** Path B (direct conversion). Paired with `inbox-setup`.
