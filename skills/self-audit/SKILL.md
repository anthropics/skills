---
name: self-audit
description: Audits AI output before delivery — mechanical file verification + four-dimension reasoning audit. Catches what tests miss. Use before shipping complex work, after architectural decisions, or whenever the agent claims to have produced output files.
---

# Self-Audit

Before you ship, verify mechanically first, then audit reasoning.

**Step 0 (mechanical):** If you claimed to produce files, confirm each one exists AND has non-trivial content. This includes files produced by sub-agents or spawned tasks. Use the file-read tool to open each claimed file — a file that doesn't exist is a hard fail, and a file that exists but is empty or contains only placeholder text ("TODO", "content here") is also a fail. The tool may report success without actually writing content; only a read-back can confirm.

**Steps 1-4 (reasoning):** Ask four questions:
1. **Am I being honest about the limits?** (Honesty)
2. **Did I answer everything?** (Completeness)
3. **Did I contradict myself?** (Consistency)
4. **Did I show evidence?** (Groundedness)

If any answer is no → fix it → re-ask. Code can pass all tests with sloppy thinking behind it. These questions catch what tests miss.

Tests verify code. Nothing verifies reasoning. And nothing mechanically verifies that the agent actually produced what it claims — Step 0 fills that second gap.

## Priority Order

The four dimensions are ordered by **damage severity** — how much harm a failure causes downstream, not by how often failures occur:

1. **Honesty** — Misrepresenting what was done poisons everything downstream. A dishonest audit report is worse than no audit: it creates false confidence that propagates to every future decision based on the output. Check first, because if the agent is lying, the other three dimensions are checking a fiction.
2. **Completeness** — Missing an entire requirement is more damaging than contradicting yourself on a detail. A complete-but-inconsistent answer at least addresses everything; an incomplete answer silently drops work the user must rediscover.
3. **Consistency** — Internal contradictions erode trust but don't lose information. A user can resolve a contradiction by checking both sides; they can't resolve a missing requirement they don't know exists.
4. **Groundedness** — Evidence quality can be improved incrementally. An honest, complete, consistent answer with weak evidence is still useful; perfect evidence for a dishonest or incomplete answer is wasted effort.

**Lexicographic rule:** Fix Honesty issues first (they invalidate all other checks), then Completeness (missing coverage), then Consistency (contradictions), then Groundedness (evidence quality). Never spend time improving Groundedness while Honesty is failing.


## When to Use

- Complex task completed (new logic or architectural decisions, not mechanical edits)
- Agent about to stop and deliver results
- After architectural decisions with downstream impact
- Agent claimed to produce output files (Step 0 applies)
- Proactively: if you are about to ship, audit first

## Hard Constraints

- **Never fabricate findings.** If all dimensions pass, report PASS. If any fail, report FIXED with specifics.
- **Never expose sensitive data.** Redact paths, secrets, tokens, PII before displaying audit output.
- **Never block on subjective grounds.** Flag only concrete, verifiable gaps — not stylistic preferences.
- **Step 0 is non-negotiable when files are claimed.** If the agent said it produced output files, verify mechanically first. No exceptions. This includes verifying content is non-trivial — not just that the path exists.


## Step 0 — Mechanical File Check

**Verify claimed output files exist AND contain real content.**

If the agent claimed to produce files:
- Use the file-read tool to open each claimed file at its path
- Confirm the file exists (read succeeds) AND has non-trivial content (not 0 bytes, not only placeholder text like "TODO" or "content here")
- If any claimed file is missing → `FAIL [file not found: <path>]`
- If a file exists but is empty or placeholder-only → `FAIL [file empty: <path>]`
- If multiple files were claimed, check all of them. Report each missing or empty file individually.
- Proceed to reasoning audit only after all claimed files pass Step 0.

This catches two failure modes that reasoning alone cannot detect: (1) the agent claimed to write a file but didn't, and (2) the write tool reported success but produced an empty or placeholder file. Both are invisible to reasoning — only a read-back reveals them.

## The Four Questions

### 1. Honesty
Check over-packaging. Edge cases mentioned? Verified without showing? Missing error handling ≠ production ready. Did the agent claim to have tested something it didn't? Did it present a partial implementation as complete?

### 2. Completeness
List each request. Verify response or deferral. Flag partials as full.

If the input was a spec, feature list, or set of numbered requirements: map each requirement to the output section that addresses it. Flag any unmapped requirements — the agent may have forgotten them.

### 3. Consistency
Scan vs earlier. Check project rules. Flag A-and-not-A.

### 4. Groundedness
Identify claims. Evidence or words? Distinguish not-verified vs hidden.

## Process

0. **MECHANICAL**: If agent claimed output files → use file-read tool to confirm existence AND non-trivial content. Missing or empty → FAIL, report to user, do not continue.
1. **ASK** the four questions in priority order (Honesty → Completeness → Consistency → Groundedness). Fail any → fix → re-ask.
2. **STUCK** on 3+ dimensions (failing 3+ of 4 questions after first fix attempt)? → report blocking issue, ask user for guidance.
3. **ALL PASS** → stop.

Output:
```
Self-Audit:
Step 0 (Mechanical):  PASS | FAIL [file not found: <path>] | FAIL [file empty: <path>]
Honesty:              OK | FIXED [what]
Completeness:         OK | FIXED [what]
Consistency:          OK | FIXED [what]
Groundedness:         OK | FIXED [what]
```

## Failure Modes

- **Step 0 fails but reasoning would pass**: The agent forgot to write the file — reasoning alone cannot detect a physically absent artifact. This is why Step 0 exists.
- **File exists but is empty or placeholder**: The write tool reported success but produced no content. Step 0's content check (read first few lines of each claimed file) catches this. The write-then-verify pattern (write → read back → confirm non-empty) prevents it at the source.
- **Overly long**: Sample 5 most critical findings. The full list goes in the audit output; the summary hits the top issues.
- **Data leak**: Redact paths, secrets, tokens before displaying audit output.
- **Fatigue**: Detail mode for shipping only. Quick scans on intermediate steps.

## Common Rationalizations

| Rationalization | Reality |
|---|---|
| Simple change, no audit | Simple changes cause bugs. 30 seconds of audit saves hours of debugging. |
| Checked as I went | Cross-cutting issues only surface in a dedicated pass. Inline checking is awareness, not audit. |
| User will catch | Users are not QA. Shipping unchecked output is outsourcing your verification to the person who asked you to do the work. |
| All four OK no detail | Complex tasks find ≥1 issue. If you found zero, you didn't look hard enough. |
| Verified internally | Without output = assumption. Internal verification without evidence is indistinguishable from not verifying at all. |
| I'm sure I wrote the file | Memory is fallible. Step 0 verifies mechanically — trust the read-back, not your recollection. |
| I reviewed it mentally | Mental review has zero persistence. If the audit wasn't written down in the response, it didn't happen — and the user has no way to verify it. |
| The tool said it wrote the file | Tools can report success without writing content. A tool returning exit code 0 does not guarantee the file has bytes. Only a read-back (Step 0) confirms. |

## Red Flags

**Process** (the audit wasn't done):
- Stopping without audit
- Step 0 skipped when files were claimed
- Audit hidden in reasoning (user can't see it)

**Content** (audit ran but findings are shallow):
- All OK no specifics — the most dangerous audit result because it's usually false
- Verified without showing evidence — "verified" is a claim, not evidence
- Requirements dropped silently — partial coverage presented as complete

## Verification

- [ ] Step 0: All claimed output files mechanically verified (file-read tool confirms existence + non-trivial content)
- [ ] Four questions answered with specific evidence (not "seems fine"), in priority order
- [ ] If spec/requirements were provided: each requirement mapped to output section; unmapped requirements flagged
- [ ] FIXED applied for every failed dimension with concrete description of what was fixed
- [ ] Audit output visible in the response (not buried in reasoning)
- [ ] Hard constraints respected — no fabricated findings, no leaked data
- [ ] No rationalized omissions (skipped work documented as skipped, not as done)

## Background

The four-dimension taxonomy (Completeness, Consistency, Groundedness, Honesty) is an instance of **independent convergence**: equivalent dimensions emerged separately in multi-agent pipeline architectures (e.g., SwarmAI's T-CBB framework) and in this single-agent self-audit context. The convergence validates the taxonomy itself — these aren't arbitrary categories but fundamental dimensions of reasoning quality that different architectures independently rediscover when they ask "how do we verify agent output?"

What differs between contexts is the **trust boundary**, and this difference drives the design:

- **Multi-agent pipelines** deploy equivalent gates at handoff boundaries where the reviewer is an independent agent. The architectural separation provides adversarial pressure automatically.
- **Self-audit** runs within the same agent session that produced the output — same trust boundary, same context window. This makes **Honesty** the critical dimension (misrepresentation within the same session is harder to flag than between sessions) and **Step 0** the critical mechanical check (file-system read-back is the one thing an agent cannot fabricate without actually writing the file).

The priority ordering (Honesty > Completeness > Consistency > Groundedness) is operational, not taxonomic: it derives from damage severity observed across real audit failures, where late-caught Honesty issues invalidated earlier Completeness and Consistency checks. It is a practical rule for audit efficiency, not a claim about which dimension matters more in the abstract.

## See Also

- `skill-creator` — Build, test, and iterate on new skills; its eval loop pairs with self-audit as the "create → verify" cycle
- `webapp-testing` — Verify application behavior through browser testing; audit the reasoning behind test results, not just pass/fail