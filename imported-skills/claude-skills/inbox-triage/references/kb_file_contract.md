# Knowledge Base File Contract (Read Perspective)

This reference is the **mirror** of `inbox-setup/references/kb_file_contract.md`, viewed from the read side. It answers exactly one decision: **what 7 files does `inbox-triage` read on every run, and what happens if they're missing or malformed?**

PR #657's cross-skill consistency audit verified that the 7 KB filenames align verbatim between the two megaprompts. This reference is the canonical read-side spec.

## The 7 Files at `${WORKSPACE}/Email/`

| File | Read perspective | What triage does with it |
|---|---|---|
| `email-taxonomy.md` | **required core read** | Classification rules + report preferences |
| `email-patterns.md` | **required core read** | Voice rules + hard rules + templates |
| `evaluation-framework.md` | optional core read | TAKE-IT / PASS signals + VIP list + decision tree |
| `rate-card.md` | optional core read | Pricing + negotiation posture for opportunity drafts |
| `blocklist.md` | required core read + **write** | Auto-skip rules; appended with new declines |
| `tracker.md` | required core read + **write** | Active follow-ups; appended with new + resolved |
| `triage-log/` | **write only** | Per-run logs written to `<date>-<label>.md` |

## Fail-Fast Behavior on Missing Files

The skill performs read validation **first**, before any other step. If validation fails:

```
HALT.
Knowledge base not found at ${WORKSPACE}/Email/.
Run /cs:inbox-setup first to build it.
The triage skill needs at minimum email-taxonomy.md and email-patterns.md to operate.
```

Use `scripts/kb_reader.py --workspace ${WORKSPACE}` to perform the read + validation. The script exits non-zero on missing required files.

### Required core (halt if any missing)

- `email-taxonomy.md`
- `email-patterns.md`
- `blocklist.md`
- `tracker.md`
- `triage-log/` (must be a directory)

### Optional core (read if exists; skip relevant step otherwise)

- `evaluation-framework.md` — if missing, Step 5 (Recommendations) is skipped
- `rate-card.md` — if missing, drafts don't include pricing/counter-offer logic

## What Triage Reads From Each File

### email-taxonomy.md (every run)

- All `### {Category Name}` headers under `## Categories`
- For each category: signals (trigger phrases, sender patterns, subject markers) + default action
- The `## Report Preferences` section (delivery format, detail level, top-of-report rules)

If categories section is empty or malformed → halt with "email-taxonomy.md has no usable categories. Re-run inbox-setup."

### email-patterns.md (every run)

- `## Voice Register` (formal / casual / in-between)
- `## Hard Rules` (non-negotiable in drafts)
- `## Pet Peeves` / "Forbidden Tokens" (NEVER appear in drafts)
- `## Sign-Offs` (rotate through these in drafts)
- `## Voice Patterns (Extracted from Samples)` if present
- `## Templates` if present (for repeated reply patterns)
- `## Voice Calibration Status` — if "samples not collected", lean conservative (medium-formal, short-paragraph) on early runs

### evaluation-framework.md (conditional)

- `## Gut Filter (First Check)` — applied first to opportunity emails
- `## TAKE-IT Signals` — auto-engage if ALL match
- `## PASS Signals (Instant Deal-Breakers)` — auto-decline if ANY match
- `## Decision Tree` — branch logic
- `## VIP List` — bypass PASS filters
- `## Negotiation Posture` — drives counter-offer tone

### rate-card.md (conditional)

- `## Standard Pricing` — drives auto-decline when offer < floor
- `## Terms` — payment, revisions, rush
- `## Counter-Offer Patterns` — when to push back, how

### blocklist.md (read + append)

- `## Sender / Domain Auto-Skip` — exact match auto-skip
- `## Decline Patterns` — regex / phrase match auto-skip
- `## Recently Removed (User Overrode)` — DON'T re-block these

**Triage appends:**
- New declined senders this run (with reason + date)
- New decline patterns from observed user-overrides
- Removes entries if user has overridden them

### tracker.md (read + update)

- `## Active Follow-Ups` table — surfaces in report's "Action Needed"
- `## Overdue` — flagged in every run until resolved
- `## Resolved (Recent)` — for context but not surfaced
- `## Update Log` — append-only history

**Triage updates:**
- Adds new follow-ups for emails needing future action
- Updates existing follow-ups (status / deadline)
- Marks items resolved when user replies / deadline passes
- Flags overdue items
- Removes resolved items older than 30 days
- Adds an entry to update log

### triage-log/ (write only)

Per-run log at `triage-log/<YYYY-MM-DD>-<run-label>.md`:

- Emails processed (count + classifications)
- Recommendations (with reasoning)
- Drafts created (with thread IDs)
- KB updates (with explicit before/after)
- Follow-ups added / resolved
- Notable observations

The log is the audit trail for `scripts/draft_safety_validator.py`. After every run, the validator scans the log for any send-shaped tool calls. If found → halt + alert user.

## Contract Drift Detection

Both megaprompts (06-inbox-setup, 07-inbox-triage) reference these 7 files verbatim. PR #657's audit grep-confirmed alignment. If drift is suspected:

```bash
# From repo root:
grep -A 0 'email-taxonomy\|email-patterns\|evaluation-framework\|rate-card\|blocklist\|tracker\|triage-log' \
  megaprompts/06-inbox-setup-megaprompt.md megaprompts/07-inbox-triage-megaprompt.md
```

Any divergence is a bug. Re-grill with `/cs:grill-with-docs` against both megaprompts to surface and fix.

## Why This Contract Is Strict

The integration boundary between the two skills lives ONLY in these 7 files. `inbox-setup` and `inbox-triage` never call each other directly — they communicate via files. That makes the contract:

- **Testable** — `scripts/kb_validator.py` (setup-side) and `scripts/kb_reader.py` (triage-side) can both validate independently.
- **Versionable** — when the contract evolves, version it explicitly. Don't silently change field names.
- **Failure-isolating** — if setup misbehaves, the bad KB files surface immediately on triage's first run rather than weeks later.

Strict contracts beat coordination overhead.
