# Challenge Gate — Bug Validity Review

## Purpose

The challenge gate is a self-adversarial review that every confirmed bug must survive before receiving a writeup and regression test. It catches false positives, over-classified feature gaps, and findings where pattern-matching overrode common sense.

The gate can be invoked two ways:

1. **During a playbook run** — automatically applied to bugs matching trigger patterns (see below).
2. **Standalone** — pointed at a `quality/` directory from a prior run to challenge specific bugs. Example: `"Read quality/writeups/BUG-042.md and the source code it references. Run the challenge gate on this bug."`

## The two-round challenge

For each bug under review, run exactly two rounds. Each round uses a fresh sub-agent so the challenger has no investment in the finding.

### Round 1: "Does this strike you as a real bug?"

Provide the sub-agent with:
- The bug writeup (or BUGS.md entry if no writeup yet)
- The actual source code at the cited file:line (read it fresh — do not trust the writeup's code snippet)
- All comments within 10 lines above and below the cited location
- The project's README section on the relevant feature (if any)

Prompt the sub-agent:

> You are reviewing a bug report filed against an open-source project. Read the source code and the bug report below. Then answer: **does this strike you as a real bug?**
>
> **Before analyzing anything, apply common sense.** Step back from the details and ask yourself: if you showed this code and this bug report to a senior developer who has never seen either before, would they say "yes, that's a bug" — or would they say "that's obviously not a bug"? If the answer is obviously not a bug, say so immediately and explain why. Do not rationalize your way past a common-sense answer. The goal of this review is to catch findings where pattern-matching overrode judgment.
>
> Then consider:
> - Is the developer aware of this behavior? (Look for comments, TODO markers, design decision notes, WHY annotations, OODA references.)
> - Is this a documented limitation or intentional trade-off? (Check if other code paths handle this differently by design, not by accident.)
> - Would the project maintainer respond "that's not a bug, that's how it works" or "that's a known limitation we documented"?
> - Is the "expected behavior" in the bug report actually required by any spec, or is it the auditor's opinion about what the code should do?
> - Is this development scaffolding? Values with names like "change-me", "placeholder", "example", "default", "TODO" are not defects — they are self-documenting markers that exist to make the project buildable during development. A feature that is disabled by default and uses placeholder values is an incomplete feature, not a vulnerability.
>
> Give your honest assessment. If it's a real bug, say so and explain why. If it's not, say so and explain why. A finding can be "not a bug" even if the code could be improved — the question is whether a reasonable maintainer would accept this as a defect report.

### Round 2: Targeted follow-up

Based on the Round 1 response, generate a single pointed follow-up question. The goal is to stress-test whatever position the sub-agent took in Round 1.

**If Round 1 said "real bug":** The follow-up should challenge the finding from the maintainer's perspective. Use a fresh sub-agent with this framing:

> You are the maintainer of this project. A contributor filed this bug report. You wrote the code being criticized. Read the code, the bug report, and the Round 1 assessment below.
>
> Write the single most compelling argument for why this is NOT a bug. Consider: intentional design decisions, documented limitations, deployment context, common patterns in this language/framework, and whether the "expected behavior" is actually specified anywhere authoritative.
>
> Then, after making that argument, state whether you still believe it's a real bug or whether the argument convinced you it's not.

**If Round 1 said "not a bug":** The follow-up should challenge the dismissal. Use a fresh sub-agent with this framing:

> You are a security researcher reviewing this codebase. Another reviewer dismissed this finding as "not a bug." Read the code, the bug report, and the Round 1 dismissal below.
>
> Write the single most compelling argument for why this IS a real bug despite the dismissal. Consider: edge cases the dismissal didn't address, downstream consequences, what happens when the code interacts with other components, and whether "intentional" and "correct" are the same thing.
>
> Then, after making that argument, state whether you believe the finding should be confirmed or dismissed.

### Verdict

After both rounds, assign one of three verdicts:

- **CONFIRMED** — Both rounds agree it's a real bug, or Round 2's challenge failed to undermine Round 1's confirmation. The bug proceeds to writeup and regression test as normal.
- **DOWNGRADED** — The bug is real but the severity was inflated. Adjust severity and update the writeup. Common case: a CRITICAL that should be MEDIUM, or a security finding that's actually a code quality issue.
- **REJECTED** — The finding is not a bug. It's a documented design choice, intentional scaffolding, a known limitation, the auditor's opinion rather than a spec violation, or something that common sense says is obviously not a defect. Remove the bug ID. If useful, record it in a "Reviewed and dismissed" appendix in BUGS.md with the challenge reasoning.

Write the verdict and both rounds' reasoning to `quality/challenge/BUG-NNN-challenge.md`. This file is the audit trail — it shows reviewers that each finding was stress-tested.

## Auto-trigger patterns

During a playbook run, automatically apply the challenge gate to any bug matching one or more of these patterns. These patterns are where false positives concentrate:

| Pattern | Why it triggers | Example |
|---------|----------------|---------|
| **Security-class finding** (credential leak, auth bypass, injection) | Severity calibration auto-escalates these; the model is incentivized to defend them | BUG-041: "hardcoded JWT secret" that was a development placeholder |
| **Code contains design-decision comments at the cited location** | WHY comments, OODA references, TODO-with-explanation, or design decision docs within 10 lines of the cited code suggest the developer made a conscious choice | BUG-007/008: `// WHY-OODA81: Batch upload uses "default" workspace` |
| **The "expected behavior" has no spec basis** | Bug's spec_basis field says "code inconsistency" rather than citing a spec document, or the requirement was invented by the auditor (Tier 3 / REQ-NNN created during the run) | BUG-041: REQ-019 was created by the auditor, not derived from project docs |
| **Another code path handles the same concern differently** | If text_upload does X but file_upload doesn't, that might be a real inconsistency — or it might be intentional divergence. The challenge sorts out which. | BUG-001/002: text_upload merges source_ids, file_upload overwrites — challenge confirms this is a real bug because text_upload has an explicit fix comment |
| **The finding is about missing functionality rather than incorrect behavior** | "This handler doesn't do X" is often a feature gap, not a bug. The challenge checks whether X was ever promised. | BUG-009/029: batch upload "missing" graph writes that were never part of the batch upload's documented scope |

The pattern list is intentionally conservative — it triggers on categories with historically high false-positive rates. Bugs that don't match any pattern skip the challenge gate and proceed directly to writeup.

To add new patterns: append a row to the table above with the pattern description, the reasoning, and a concrete example from a prior run.

## Standalone invocation

When invoked standalone (not during a playbook run), the challenge gate:

1. Reads the specified bug writeup from `quality/writeups/BUG-NNN.md`
2. Reads the source code at the cited file:line (fresh read, not from the writeup)
3. Runs both rounds as described above
4. Writes the verdict to `quality/challenge/BUG-NNN-challenge.md`
5. If the verdict is REJECTED, suggests removing the bug from BUGS.md and tdd-results.json

Example prompt for standalone use:
```
Read the quality playbook skill at .github/skills/SKILL.md and .github/skills/references/challenge_gate.md.
Run the challenge gate on BUG-042 using the writeup at quality/writeups/BUG-042.md
and the source code in this repo.
```

## Token budget

Each bug costs roughly 2 sub-agent calls. For a typical run with 5-10 auto-triggered bugs, that's 10-20 sub-agent calls. This is significantly cheaper than a full iteration cycle and catches the highest-value false positives.

For runs with many security findings (>15 auto-triggered), consider batching: run Round 1 on all triggered bugs first, then only run Round 2 on bugs where Round 1 was ambiguous or where the confidence was low.
