# Knowledge Base File Contract (Write Perspective)

This reference answers exactly one decision: **what 7 files must `inbox-setup` produce, in what structure, so that `inbox-triage` can read them without ambiguity?**

This is the integration boundary between the paired skills. Any drift breaks the pair. PR #657's cross-skill consistency audit verified that the 7 KB filenames align verbatim between the two megaprompts; this reference is the canonical write-side spec. A mirror lives at `inbox-triage/references/kb_file_contract.md` (read perspective).

## The 7 Files at `${WORKSPACE}/Email/`

| File | Required? | Triggered by | Triage uses for |
|---|---|---|---|
| `email-taxonomy.md` | yes | Section 2 + Section 7 | classification + report preferences |
| `email-patterns.md` | yes | Section 3 | reply voice + templates + hard rules |
| `evaluation-framework.md` | conditional | Section 4 (only if S1 surfaced opportunities) | TAKE-IT / WORTH / PASS / FLAG decisions |
| `rate-card.md` | conditional | Section 4 (only if user has pricing) | negotiation posture + counter-offers |
| `blocklist.md` | yes (seeded) | Section 5 | auto-skip senders + decline patterns |
| `tracker.md` | yes (seeded) | Section 6 | active follow-ups + deadlines |
| `triage-log/` | yes (empty dir) | Section 6 | per-run logs (populated by triage) |

## File Specs (Write Side)

### email-taxonomy.md (required)

```markdown
# Email Taxonomy

## Categories

### {Category Name}
- Signals: {trigger phrases, sender patterns, subject markers}
- Default action: {classify / draft-reply / skip / flag-for-review}
- Typical volume: {N% of inbox}

### {Category 2}
...

## Report Preferences

- Delivery format: {email-draft-to-self | file-in-workspace | chat-summary-only}
- Detail level: {30-second-scan | detailed-breakdown | both}
- Always-shown-first: {overdue payments | VIP messages | custom rules}
```

**Generated at:** end of Section 2 (categories) + appended at end of Section 7 (Report Preferences).

### email-patterns.md (required)

```markdown
# Email Patterns

## Voice Register
{formal | casual | in-between}

## Pet Peeves (Forbidden Tokens)
- {phrase 1}
- {phrase 2}
- {phrase 3}

## Sign-Offs (Voice Fingerprints)
- {sign-off 1}
- {sign-off 2}
- ...

## Persona Context
{single-user | delegated (assistant replies as user) | multi-persona}

## Typical Reply Length
{one-liner | short-paragraph | longer}

## Hard Rules (Non-Negotiable in Every Draft)
- Never: {X}
- Always: {Y}

## Voice Patterns (Extracted from Samples)
- Opening phrases observed: {list}
- Sentence length distribution: {short / medium / long mix}
- Casual / formal markers: {list}

## Templates (Repeated Replies)
- {template 1 name}: {body}
- {template 2 name}: {body}
```

**Generated at:** end of Section 3. The "Voice Patterns" subsection comes from `scripts/voice_sample_analyzer.py` if samples were provided; otherwise marked `[calibration may need iteration]`.

### evaluation-framework.md (conditional)

```markdown
# Evaluation Framework (Opportunity Emails)

## Gut Filter (First Check)
{user's gut filter from S4.Q1}

## TAKE-IT Signals
- {signal 1}
- {signal 2}
- {signal 3}

## PASS Signals (Instant Deal-Breakers)
- {deal-breaker 1}
- {deal-breaker 2}
- {deal-breaker 3}

## Decision Tree

1. If sender in VIP list → TAKE IT (skip filter)
2. If any PASS signal matches → PASS (auto-decline draft)
3. If all TAKE-IT signals match → TAKE IT (auto-engage draft)
4. If partial TAKE-IT match → WORTH CONSIDERING
5. If unusual / ambiguous → FLAG FOR REVIEW

## VIP List (Bypass PASS Filters)
- {sender / domain 1}
- {sender / domain 2}
- ...

## Negotiation Posture
{firm | flexible | depends-on-context}
```

**Generated at:** end of Section 4. Skipped entirely if S1 surfaced no opportunity-email category.

### rate-card.md (conditional)

```markdown
# Rate Card

## Standard Pricing
- {service / offering 1}: {price}
- {service / offering 2}: {price}

## Terms
- Payment: {net X days | upfront | milestone}
- Revisions included: {N}
- Rush fee: {Y%}

## Negotiation Posture
{firm | flexible | depends-on-context}

## Counter-Offer Patterns
- If they offer < {floor}: {how to counter}
- If timeline is tight: {how to counter}
```

**Generated at:** end of Section 4. Skipped if user has no fixed pricing (S4.Q4 = "no fixed pricing").

### blocklist.md (required, seeded)

```markdown
# Blocklist

## Sender / Domain Auto-Skip
- {sender 1}: {reason} — added {date}
- {domain 1}: {reason} — added {date}

## Decline Patterns (Pattern-Match Auto-Skip)
- "{pattern phrase 1}": {reason}
- "{pattern phrase 2}": {reason}

## Recently Removed (User Overrode)
- {sender}: removed on {date} — user override
```

**Generated at:** end of Section 5 (initial seed). `inbox-triage` appends new declines + observed patterns on every run.

### tracker.md (required, seeded)

```markdown
# Tracker

## Active Follow-Ups

| Item | Context | Deadline | Status |
|---|---|---|---|
| {thread} | {one-line context} | {date} | pending |
| ... | ... | ... | ... |

## Overdue
- {thread}: missed deadline {date} — {context}

## Resolved (Recent)

## Update Log
- {date}: {what changed} — by {triage run | user}
```

**Generated at:** end of Section 6 (initial seed from S6.Q1-Q3). `inbox-triage` updates on every run.

### triage-log/ (required, empty directory)

Empty directory created at end of Section 6. `inbox-triage` writes per-run logs to `triage-log/<YYYY-MM-DD>-<run-label>.md`.

## Validation

Run `scripts/kb_validator.py --workspace ${WORKSPACE}` after Section 8 confirmation. It checks:

- All required files exist
- Conditional files exist iff their triggering section ran
- Each file has the expected H1 + section structure
- `triage-log/` is a directory (not a file)

## Why This Contract Matters

`inbox-triage` halts with a clear error if any required core file is missing. The contract is the integration boundary — both skills can be developed and tested independently, but they must agree on the file shape.

When updating either skill: update both sides of the contract simultaneously, or use `/cs:grill-with-docs` to detect drift between the two megaprompts before drift reaches code.
