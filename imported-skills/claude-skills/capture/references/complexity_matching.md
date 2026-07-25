# Complexity Matching — Compressed vs Full 4-Section Output

This reference answers exactly one decision: **when does capture use the full 4-section format vs the compressed format, and what does each look like in practice?**

Pair with `scripts/complexity_estimator.py` for the deterministic recommendation.

## The Core Rule

> **Match output complexity to input complexity.**

A 30-item dump with natural clusters needs the full 4-section structure to be useful. A 5-item dump of unrelated todos drowns in that structure — the format becomes ceremony, not signal. Force-fitting structure on a small dump makes the skill feel bureaucratic.

## When to Use Each Format

| Signal | Recommended format |
|---|---|
| 8+ items AND natural clustering exists (3+ items share a theme) | Full 4-section |
| 8+ items but NO clustering (all unrelated todos) | Compressed (with explicit "no clusters" note) |
| 5–7 items, mixed kinds, some clustering | Either — judgment call. Lean compressed unless clusters are strong. |
| ≤5 items, unrelated | Compressed |
| ≤5 items but all related to one project | Compressed with single project header |
| Workspace inaccessible AND ≤5 items | Compressed with no Section 3 (still note "no workspace accessible") |

`complexity_estimator.py` returns `format=full` or `format=compressed` based on item count + clustering signal. Use it as the seed; override with judgment when context warrants.

## Format A: Full 4-Section

Use for substantive dumps with real structure. Roughly:

```
## Projects & Ideas

### {Project A in user's voice}
- {component}
- {component}
- Q: {open question}
- Decide: {decision}

### {Project B}
- ...

## Tasks

- {task} [Project: A]
- {task}
- Decide: {decision}
- Resolve: {open question}

## Connections

- {file/folder}: {real workspace match}
- (or) "No connections found — workspace inventory clean."
- (or) "No workspace accessible from here..."

## How I Can Help

- {concrete offer: what + where}
- {concrete offer: what + where}

**Which of these should I tackle?**
```

## Format B: Compressed

Use for small or unrelated dumps. Roughly:

```
## What I heard

- {item}
- {item}
- {item}
- Decide: {decision}
- Resolve: {open question}

## How I can help

- {concrete offer: what + where}
- {concrete offer: what + where}

Which should I tackle?
```

Notice what's gone in compressed:
- No project headers (nothing to cluster)
- No separate Tasks section (the list IS the tasks)
- No Connections section as a separate header (if there's a real connection, fold it inline as a parenthetical: `- fix the auth bug (relates to src/auth/login.ts:42)`)
- Same Section 4 discipline (concrete offers + directive question)

## Worked Examples

### Example 1: Full 4-section (12 items, 2 clusters)

**Dump:**
> "Ok so dump time. Q3 launch is approaching — need to nail down pricing, draft the launch email, brief Sarah on the marketing angle. Also ferret app keeps nagging me — should I talk to my cofounder about it, or is it just procrastination? Need to sketch the matching algorithm if it's serious. Also: fix the damn auth bug, rewrite the login form because it's ugly, write tests for both. Oh and I should probably do my Q3 OKRs before launch."

**Extracted items:** 11
**Clusters:** Q3 Launch (4 items), Ferret App (3 items), Auth (3 items), OKRs (1 item)
**Recommendation:** `format=full` (clear clustering, 11 items)

**Output:**

```
## Projects & Ideas

### Q3 Launch
- Nail down pricing
- Draft launch email
- Brief Sarah on the marketing angle
- Decide: Q3 OKRs (do before launch)

### Ferret App
- Talk to cofounder OR decide it's procrastination
- Sketch matching algorithm (if serious)
- Decide: serious project or shelf?

### Auth Fixes
- Fix the auth bug
- Rewrite the login form (it's ugly)
- Write tests for the bug fix + login rewrite

## Tasks

- Nail down Q3 pricing  [Project: Q3 Launch]
- Draft Q3 launch email  [Project: Q3 Launch]
- Brief Sarah on Q3 marketing angle  [Project: Q3 Launch]
- Talk to cofounder about ferret app  [Project: Ferret App]
- Sketch ferret matching algo  [Project: Ferret App]
- Fix auth bug  [Project: Auth Fixes]
- Rewrite login form  [Project: Auth Fixes]
- Write tests for auth + login  [Project: Auth Fixes]
- Do Q3 OKRs (before launch)
- Decide: ferret app — serious or shelf?

## Connections

(workspace inventory results go here — only verified matches)

## How I Can Help

- I can draft the Q3 launch email as a 1-pager. Output: chat reply.
- I can pull together a pricing-options matrix from your existing pricing docs. Output: `docs/q3-pricing-options.md`.
- I can scaffold the ferret matching algorithm sketch (input → match score). Output: `docs/ferret-algo-sketch.md`.

**Which of these should I tackle?**
```

### Example 2: Compressed (5 unrelated items)

**Dump:**
> "Quick: email Sarah, fix that test that's been flaky, decide between Postgres and Mongo for the new service, dentist appointment, finish reading the article on RAG."

**Extracted items:** 5
**Clusters:** none (all unrelated)
**Recommendation:** `format=compressed`

**Output:**

```
## What I heard

- Email Sarah
- Fix the flaky test
- Decide: Postgres or Mongo for the new service
- Dentist appointment
- Finish reading the RAG article

## How I can help

- I can draft the email to Sarah if you tell me what it's about. Output: chat reply.
- I can investigate the flaky test (likely racing condition; happy to reproduce). Output: chat analysis + fix PR if you want.
- I can pull a Postgres-vs-Mongo decision matrix scoped to your service requirements. Output: chat reply or `docs/db-decision.md`.

Which should I tackle?
```

Notice the dentist appointment + RAG article aren't in "How I can help" — there's nothing meaningful to offer on those. That's correct: don't pad Section 4 with offers for things that don't need help.

### Example 3: Compressed but workspace-aware (small + connection inline)

**Dump:**
> "auth bug is back, need to look at the login flow again, also I want to add 2FA finally."

**Extracted items:** 3
**Clusters:** all auth-related but only 3 items
**Recommendation:** `format=compressed`

**Output:**

```
## What I heard (Auth)

- Auth bug is back (relates to `src/auth/login.ts` based on workspace inventory)
- Look at login flow again
- Add 2FA

## How I can help

- I can reproduce the auth bug from the symptoms — what's the failure mode? Output: chat repro + fix.
- I can sketch a 2FA implementation matching your existing auth pattern (TOTP via the same provider you use). Output: `docs/2fa-sketch.md`.

Which should I tackle?
```

Notice the workspace connection got folded inline as a parenthetical instead of a separate Section 3 header. That's the compressed-with-context pattern.

## Operational Checklist

Before delivering output:

- [ ] Run `complexity_estimator.py` (or apply the Signal table above)
- [ ] If `format=compressed`, do NOT force the 4-section format
- [ ] If `format=full`, ensure the clusters are real (3+ items per cluster) — don't invent clusters to fill the format
- [ ] Either way, Section 4 ("How I can help") MUST have concrete offers with what + where
- [ ] Either way, end with the directive question

## Why This Matters

A skill that returns the same format regardless of input is a template, not a skill. The reason capture is useful is that it adapts to the dump's actual shape. When a 5-item list comes back wrapped in 4 elaborate empty-feeling sections, the user learns to distrust the skill. When a 30-item dump comes back as a flat compressed list, the user learns the skill can't actually handle complexity.

Match the output to the input, every time.
