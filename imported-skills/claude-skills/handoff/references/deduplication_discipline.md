# Deduplication Discipline for Handoffs

This reference answers exactly one decision: **what counts as duplication, and how do we replace it with a reference?**

Pair with `scripts/artifact_deduplicator.py` for automated detection.

## Matt Pocock's Non-Negotiable Rule

> "Do not duplicate content already captured in other artifacts (PRDs, plans, ADRs, issues, commits, diffs). Reference them by path or URL instead."
>
> — Matt Pocock, handoff SKILL.md

This is the most violated rule in handoffs. Duplication is seductive — copying content into the handoff feels comprehensive. But it creates 4 problems.

## Why Duplication Is Bad

### Problem 1: Drift

The handoff drifts from the source. If the PRD updates, the handoff is now wrong. The next agent reads stale info and makes wrong decisions.

### Problem 2: Bloat

Handoffs grow unbounded. A 500-line handoff is unusable — the next agent skims it and misses critical context.

### Problem 3: Ownership

When the handoff has its own version of the PRD content, ownership becomes unclear. Which version is canonical?

### Problem 4: Erosion of upstream artifacts

If handoffs duplicate PRD content, the PRD itself stops getting updated — "we'll just put it in the handoff." The upstream artifact rots.

## Five Categories of Common Duplication (How `artifact_deduplicator.py` Detects)

### Category 1: PRD content

**Signals:** headers like "Problem statement", "Solution", "Success metrics", "Out of scope", "User stories", "Acceptance criteria"

**Fix:** Replace the section with a link to the PRD file.

**Before:**
```markdown
## Problem statement
Users complain about slow auth. We need to make it fast.

## Solution
Implement OAuth2 with refresh tokens.

## Success metrics
- Login p95 < 500ms
- 0 OAuth errors per 10k requests
```

**After:**
```markdown
## Context
See full PRD: [docs/prd/auth-refactor.md](docs/prd/auth-refactor.md)
```

### Category 2: ADR content

**Signals:** "Status:", "Decision:", "Consequences:", "Context:", "Alternatives considered"

**Fix:** Replace with a link to the ADR.

**Before:**
```markdown
## Status: Accepted
Decision: Use Auth0 over Okta.
Consequences: $200/month cost; faster integration.
```

**After:**
```markdown
## Decisions locked in
See [ADR-0042](docs/adr/0042-auth-provider.md)
```

### Category 3: Issue content

**Signals:** "Steps to reproduce", "Expected behavior", "Actual behavior", "Environment:"

**Fix:** Issue reference is enough.

**Before:**
```markdown
## Bug
### Steps to reproduce
1. Login
2. Wait 10 seconds
3. Re-login
### Expected behavior
Stay logged in.
### Actual behavior
Session expires.
```

**After:**
```markdown
## Active bug
[#142 — Session expires after 10 seconds](https://github.com/.../issues/142)
```

### Category 4: Commit-message style content

**Signals:** Conventional Commit prefixes (feat:, fix:, docs:, chore:, refactor:) with multi-line body

**Fix:** Replace with commit SHA + URL.

**Before:**
```markdown
## What was shipped
feat: add OAuth2 support
This change adds OAuth2 to the auth middleware.
- Added refresh token handling
- Added expiry check
```

**After:**
```markdown
## What was shipped
[abc1234](https://github.com/.../commit/abc1234) feat: add OAuth2 support
```

### Category 5: Long code blocks

**Signals:** code blocks >20 lines — usually duplicating checked-in code

**Fix:** Link to file + line range + commit SHA.

**Before:**
````markdown
## The fix
```python
def authenticate(token):
    # 30 lines of code...
```
````

**After:**
```markdown
## The fix
[src/auth.py:42-80 @ abc1234](https://github.com/.../blob/abc1234/src/auth.py#L42-L80)
```

## What's NOT Duplication

Some content should live in the handoff and only the handoff:

- **Synthesis** — your interpretation across multiple artifacts ("the PRD says X but the issue suggests Y; reconciling here")
- **Current state** — "as of this moment, branch X is at commit Y" (changes too fast to capture elsewhere)
- **Next-session-specific instruction** — the focus + prompts tailored to what comes next
- **Open decisions** — decisions not yet captured in any artifact (because they're still open)
- **Quick links** — paths/URLs are duplication-OK; they're indexes, not content

## The "Could the Next Agent Find This Themselves?" Test

For every paragraph in the handoff, ask:
1. Is this content captured in a referenceable artifact (PRD, ADR, issue, commit, code)?
2. If yes — replace with a reference. Duplication.
3. If no — keep it in the handoff. This is original synthesis.

## How `artifact_deduplicator.py` Helps

The tool scans for the 5 signal categories above and flags candidates. It does NOT delete or rewrite — it surfaces findings for human review. The handoff author makes the final call (sometimes context demands a brief restatement; the tool's "FAIL" verdict is advisory).

Verdict thresholds:
- 0 findings → CLEAN
- 1-3 findings → WARN (review; sometimes intentional)
- >3 findings → FAIL (probably duplicating; refactor before handing off)

## Anti-Patterns

1. **Copying PRD content "for convenience"** — convenience for whom? The next agent has the PRD link.
2. **"Quick summary" of an ADR** — if the ADR needs a summary, fix the ADR.
3. **Inline code dumps** — git is the source of truth; commit SHA + path is enough.
4. **Issue descriptions copy-pasted** — `#NNN` is enough.
5. **Recreating diff content** — `git diff` is the source.

## When This Reference Doesn't Help

- **Standalone documentation** — handoff dedup rules don't apply to docs meant as primary sources
- **Customer-facing summaries** — duplication may be necessary for accessibility
- **Audit trails** — sometimes you need a frozen copy of content at a point in time

---

**Source authorities (non-exhaustive):**

- **Matt Pocock — handoff** (https://github.com/mattpocock/skills/, MIT) — the no-duplication rule
- **Hunt & Thomas — "The Pragmatic Programmer"** (1999) — DRY (Don't Repeat Yourself)
- **Fowler, M. — "Refactoring"** (1999, 2018) — duplication as code smell
- **DocOps + Lean Documentation Movement** — references > copies; canonical sources
- **Karpathy, A. — LLM Wiki pattern** — persistent vault as canonical store; sessions reference it
- **Git as source of truth principle** — commits + diffs are the historical record
- **API Versioning patterns (Stripe, Twilio)** — canonical-source + reference pattern at API level
