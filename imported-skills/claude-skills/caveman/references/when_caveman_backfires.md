# When Caveman Backfires

This reference answers exactly one decision: **when should caveman mode NOT be used, and what are the failure modes?**

Pair with `scripts/caveman_lint.py` — the linter detects exception-zone markers and softens its verdict accordingly.

## Matt Pocock's Auto-Clarity Exception (Verbatim)

> "Drop caveman temporarily for: security warnings, irreversible action confirmations, multi-step sequences where fragment order risks misread, user asks to clarify or repeats question. Resume caveman after clear part done."
>
> — Matt Pocock, caveman SKILL.md

This is the **non-negotiable** exception list. Compressing in these zones can cause user harm — not just token cost confusion.

## The Five Failure Modes

### 1. Compressed Security Warnings

**Failure:** `Warning: drop users table. Cannot undo.`
**Why bad:** Two compound failures:
1. Reader skims caveman text; warning blends into surrounding terse responses
2. Critical verb ("drop", "cannot undo") loses emphasis without sentence structure

**Correct:** Drop caveman entirely for warnings:

> **Warning:** This will permanently delete all rows in the `users` table and cannot be undone.

The full sentence + bold marker + explicit consequences make it unmissable.

### 2. Compressed Multi-Step Sequences

**Failure:** `npm install. npm test. npm build. deploy.`
**Why bad:** Fragment order = execution order. If reader misreads order, deploy can run before tests pass.

**Correct:** Number steps + use full sentences when order matters:

> 1. Install dependencies: `npm install`
> 2. Run tests: `npm test` — must pass before continuing
> 3. Build: `npm build`
> 4. Deploy: only after step 3 succeeds

### 3. Compressed Clarification Responses

**Failure:** User asks "Wait, what?" → Response: `Token expiry. Less-than. Fix.`
**Why bad:** User asked for clarification because original was unclear. Compressing further compounds the problem.

**Correct:** Drop caveman temporarily, explain fully, then resume:

> The original issue: the token expiry check uses `<` (strict less-than) instead of `<=` (less-than-or-equal). This means tokens at the exact expiry timestamp are rejected even though they should still be valid. The fix changes the operator from `<` to `<=`.
>
> [Resume caveman.]

### 4. Compressed Irreversible Action Confirmations

**Failure:** `rm -rf node_modules. Confirm.`
**Why bad:** "Confirm" loses weight without context. User may type "yes" reflexively.

**Correct:** Drop caveman, state explicitly:

> About to run `rm -rf node_modules` which permanently deletes the directory.
>
> Reply with the exact string "DELETE" to proceed, or "cancel" to abort.

The exact-string requirement breaks reflex confirmation.

### 5. Compressed First-Turn Responses

**Failure:** User's first message → Response in caveman.
**Why bad:** No shared context yet. Reader can't fill in caveman's gaps.

**Correct:** First turn establishes context fully. Activate caveman ONLY after user explicitly triggers it (per Matt's activation triggers: "caveman mode", "talk like caveman", `/caveman`, etc.).

## Less-Obvious Backfire Cases

### Caveman in Code Review

Caveman compression on code-review feedback can lose nuance:

**Failure:** `Bug L42. Var name bad. Refactor.`
**Why bad:** Three findings, no specificity. Engineer can't tell what to fix.

**Better:** `L42: var name "x" → "userIndex". L67: off-by-one in loop bound.`

The fix: caveman compresses sentence STRUCTURE, not technical SPECIFICITY.

### Caveman in Estimates / Forecasts

Hedging is fluff per Matt's rules. But hedging carries information in estimates:

**Failure:** `Done by Friday.` (when uncertain)
**Why bad:** Reads as commitment, but actual confidence was 60%.

**Correct:** Caveman exception for probability claims. State confidence explicitly:

> Friday delivery — 60% confidence. Risks: API spec churn.

### Caveman in Multi-Stakeholder Threads

Caveman is for technical peer-to-peer (or peer-to-self) communication. When non-technical stakeholders are reading:

**Failure:** `Auth bug. Fix shipping.`
**Why bad:** PM/CEO/non-engineer reader can't decode "Fix shipping" — is shipping affected?

**Correct:** Drop caveman in stakeholder communication. Save it for technical conversations.

## Detection Patterns (How `caveman_lint.py` Helps)

The lint tool detects these markers as exception-zone signals:

- `**Warning:**` markdown bold + word
- `destructive`
- `irreversible`
- `cannot be undone`

When present, the linter softens FAIL → WARN. This isn't perfect — manual review still required for stakeholder mismatches + first-turn responses.

## Resuming Caveman After Exception

Matt's rule: "Resume caveman after clear part done."

Pattern:

> **Warning:** [full sentence warning].
>
> [empty line]
>
> Caveman resume. [terse fragment continues].

The explicit "Caveman resume." marker signals the reader that compression resumes. This is critical when the response is long enough that the reader might lose track of which mode they're in.

## Tooling Recommendation

When in doubt:
1. Run `caveman_lint.py` on the proposed response
2. If FAIL → consider rewriting (banned vocab present)
3. If WARN with exception context → check whether the exception is genuine
4. If CLEAN → ship

## When This Reference Doesn't Help

- **Brevity in writing generally** — different concern; see editing references
- **Code minification** — different mode; this is about prose around code
- **API response compression** — gzip/brotli, not prose compression

---

**Source authorities (non-exhaustive):**

- **Matt Pocock — caveman** (https://github.com/mattpocock/skills/, MIT) — the auto-clarity exception list
- **Nielsen Norman Group — Error message design** — when verbosity in errors helps vs hurts
- **FAA Human Factors research on cockpit warnings** — emphasis + redundancy in safety-critical communications
- **Krug, S. — "Don't Make Me Think"** (2000) — when brevity becomes ambiguity
- **Schneier, B. — Communication on security warnings** — why brevity in security messages is dangerous
- **Larson, W. — "An Elegant Puzzle"** (2019) — engineering manager communication patterns
- **Rommetveit, R. — Linguistic shared context** — when compression depends on shared frame
