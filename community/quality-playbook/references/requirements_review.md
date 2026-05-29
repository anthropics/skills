# Requirements Review Protocol

## Overview

This is the template for `quality/REVIEW_REQUIREMENTS.md`. The playbook generates this file alongside the requirements pipeline output. It provides three modes for reviewing requirements interactively after generation.

## Generated file template

The playbook should generate the following as `quality/REVIEW_REQUIREMENTS.md`:

---

```markdown
# Requirements Review Protocol: [Project Name]

## How to use

This protocol helps you review the generated requirements for completeness and accuracy. Run it with any AI model — the review is self-contained and reads from the files in `quality/`.

**Before starting:** Make sure `quality/REQUIREMENTS.md` exists (from the pipeline) and that you've read the Project Overview and Use Cases sections at the top.

### Choose a review mode

**Mode 1 — Self-guided review.** You pick which use cases to examine. Best when you already know which areas of the project need the most scrutiny.

**Mode 2 — Fully guided review.** The AI walks you through every use case in order, drilling into each linked requirement. Best for a thorough first review.

**Mode 3 — Cross-model audit.** A different AI model fact-checks the completeness report by verifying that every domain marked COVERED actually has requirements addressing the checklist item. Best run with a different model than the one that generated the requirements.

All three modes track progress in `quality/REFINEMENT_HINTS.md`.

---

## Mode 1: Self-guided review

Read `quality/REQUIREMENTS.md` and present the user with a numbered list of use cases:

```
Use cases in REQUIREMENTS.md:
1. [x] Use Case 1: [name] (reviewed)
2. [ ] Use Case 2: [name]
3. [ ] Use Case 3: [name]
...
```

Check `quality/REFINEMENT_HINTS.md` for review progress — use cases marked `[x]` have already been reviewed. Present the list and ask the user which use case to examine.

When the user picks a use case:
1. Show the use case (actor, steps, postconditions, alternative paths)
2. List the linked REQ-NNN numbers
3. Ask: "Want to drill into any of these requirements, or does this use case look complete?"

When drilling into a requirement:
1. Show the full requirement (summary, user story, conditions of satisfaction, alternative paths)
2. Ask: "Does this capture the right behavior? Anything missing or wrong?"
3. Record feedback in REFINEMENT_HINTS.md under the use case heading

After reviewing a use case, mark it `[x]` in REFINEMENT_HINTS.md and return to the use case list.

Also offer: "Are there any cross-cutting concerns or requirements NOT linked to a use case that you'd like to review?"

---

## Mode 2: Fully guided review

Same as Mode 1, but instead of asking the user to pick, start at Use Case 1 and proceed sequentially.

For each use case:
1. Present the use case overview
2. Walk through each linked requirement one by one
3. For each requirement, ask: "Does this look right? Anything missing?"
4. Record any feedback in REFINEMENT_HINTS.md
5. Mark the use case as reviewed
6. Move to the next use case

After all use cases:
1. Present the Cross-Cutting Concerns section
2. Ask: "Any concerns about threading, null handling, errors, compatibility, or configuration composition?"
3. Ask: "Are there any requirements you expected to see that aren't here?"
4. Record feedback and present a summary of all hints collected

---

## Mode 3: Cross-model audit

Read `quality/COMPLETENESS_REPORT.md` and `quality/REQUIREMENTS.md`. For each domain in the completeness report:

1. Read the domain checklist item (from the report's domain coverage section)
2. Read each cited REQ-NNN
3. Verify: does this requirement actually address the domain checklist item?
4. If the citation is wrong (the requirement covers something else), flag it as a gap

Also check:
- Are there requirements that don't appear in any use case's Requirements list? If so, flag as potentially orphaned.
- Does every use case's alternative paths section have corresponding requirements for the error/edge cases it mentions?
- Do the cross-cutting concerns reference requirements that actually exist and address the stated concern?

Write findings to `quality/REFINEMENT_HINTS.md` under a `## Cross-Model Audit` heading:

```
## Cross-Model Audit
Date: [date]
Model: [model name]

### Verified domains
- Null handling: CONFIRMED (REQ-054, REQ-055 correctly address null semantics)
- ...

### Gaps found
- Entry points: COMPLETENESS_REPORT cites REQ-100, REQ-101 but these are about
  pretty printing, not entry point contracts. JsonStreamParser has no coverage.
- ...

### Orphaned requirements
- REQ-NNN is not linked to any use case
- ...
```

Present findings to the user and ask which gaps should be addressed in a refinement pass.

---

## REFINEMENT_HINTS.md format

The review protocol creates and maintains this file:

```markdown
# Refinement Hints

## Review Progress
- [x] Use Case 1: [name] — reviewed, no issues
- [x] Use Case 2: [name] — reviewed, see feedback below
- [ ] Use Case 3: [name]
- [ ] Use Case 4: [name]
...

## Cross-Cutting Concerns
- [ ] Threading model — not yet reviewed
- [ ] Null contract — not yet reviewed
- [ ] Error philosophy — not yet reviewed
- [ ] Backward compatibility — not yet reviewed
- [ ] Configuration composition — not yet reviewed

## Feedback

### Use Case 2: [name]
- REQ-NNN: [specific feedback about what's missing or wrong]
- General: [broader observation about this use case's coverage]

### Cross-Model Audit
[if Mode 3 was run]

## Additional hints
[freeform feedback from the user, not tied to a specific use case]
```

This file serves dual purpose: it tracks review progress (so the user can resume across sessions) AND accumulates feedback that the refinement pass reads.
```
