# Requirements Refinement Protocol

## Overview

This is the template for `quality/REFINE_REQUIREMENTS.md`. The playbook generates this file alongside the requirements pipeline output. It provides a structured process for updating requirements based on review feedback, and can be run with any model.

## Generated file template

The playbook should generate the following as `quality/REFINE_REQUIREMENTS.md`:

---

```markdown
# Requirements Refinement Protocol: [Project Name]

## How to use

This protocol reads feedback from `quality/REFINEMENT_HINTS.md` and updates `quality/REQUIREMENTS.md` to close identified gaps. It can be run with any AI model — the protocol is self-contained.

**Multi-model refinement:** You can run this protocol multiple times with different models. Each run backs up the current version, makes targeted improvements, bumps the minor version, and logs the changes. Run as many models as you want until you hit diminishing returns.

---

## Before starting

1. Read `quality/REFINEMENT_HINTS.md` — this contains the review feedback to address.
2. Read `quality/REQUIREMENTS.md` — the current requirements to update.
3. Read `quality/CONTRACTS.md` — for contract-level detail when adding new conditions.
4. Read `quality/VERSION_HISTORY.md` — to determine the current version number.

## Step 1: Backup and version

1. Read the current version from `quality/VERSION_HISTORY.md`.
2. Copy all files in `quality/` to `quality/history/vX.Y/` (current version number).
3. Bump the minor version: v1.2 becomes v1.3.
4. Update the version stamp at the top of `quality/REQUIREMENTS.md`.

## Step 2: Process feedback

Read each item in REFINEMENT_HINTS.md and categorize it:

- **Gap — missing requirement:** A behavioral contract or domain area has no requirement. Create a new requirement using the 7-field template.
- **Gap — missing condition:** An existing requirement doesn't cover a specific scenario. Add a condition of satisfaction to the existing requirement.
- **Gap — missing use case coverage:** A use case doesn't link to a requirement that governs one of its steps. Add the REQ-NNN to the use case's Requirements line.
- **Sharpening — vague condition:** A condition of satisfaction is too vague to test. Rewrite it with concrete pass/fail criteria.
- **Correction — wrong content:** A requirement states something incorrect. Fix the specific field.
- **Cross-model audit finding:** A domain was marked COVERED in the completeness report but the cited requirements don't actually address it. Add the missing requirements.
- **Removal (user-directed only):** The user explicitly states a requirement is incorrect and should be removed (e.g., "REQ-047 is incorrect because X — remove it"). Only process removals when the hint clearly comes from the user, not from an automated pass. Log the removal and reason in the change report.

## Step 3: Make changes

For each feedback item:

1. **New requirements:** Add at the end of the appropriate category section. Continue the existing numbering sequence. Follow the 7-field template exactly.
2. **Modified requirements:** Edit the specific field that needs changing. Do not rewrite requirements that aren't flagged.
3. **Use case updates:** Add newly created REQ numbers to the relevant use case's Requirements line.
4. **Cross-cutting concerns:** If new requirements affect cross-cutting concerns, update those sections.

### Rules

- **Do not delete or weaken existing requirements during automated refinement.** Every requirement that exists today must exist after refinement with at least the same conditions of satisfaction — unless the user has explicitly marked a requirement for removal with a reason. User-directed removals are the only exception.
- **Do not renumber existing requirements.** New requirements get the next available number. This preserves traceability across versions.
- **Do not restructure the document.** The narrative pass already established the structure. Refinement is surgical — add, sharpen, or fix individual items.
- **Each change must be traceable to a feedback item.** Don't make changes that weren't asked for.

## Step 4: Report changes

After all changes, append a summary to `quality/REFINEMENT_HINTS.md`:

```
## Refinement Pass — v[new version]
Date: [date]
Model: [model name]

### Changes made
- REQ-NNN (NEW): [brief description] — addresses feedback: "[quoted hint]"
- REQ-NNN: Added condition of satisfaction for [what] — addresses feedback: "[quoted hint]"
- REQ-NNN: Sharpened condition #N: [what changed] — addresses feedback: "[quoted hint]"
- Use Case N: Added REQ-NNN to requirements list

### Feedback items not addressed
- "[quoted hint]" — reason: [why this wasn't actionable or was out of scope]

### Summary
Added N new requirements, modified N existing requirements, updated N use cases.
Total requirements: N (was N).
```

## Step 5: Update version history

Add a row to `quality/VERSION_HISTORY.md`:

```
| vX.Y | YYYY-MM-DD | [model] | [author] | N | [summary of changes] |
```

## Step 6: Update completeness report

If new requirements were added that address domain checklist gaps, update the relevant domain entries in `quality/COMPLETENESS_REPORT.md` to cite the new REQ numbers.

---

## Running multiple refinement passes

Each pass follows the same protocol:
1. Read the latest REFINEMENT_HINTS.md (which now includes the previous pass's report)
2. Focus only on feedback items marked "not addressed" or new feedback added since the last pass
3. Backup, bump version, make changes, report

The user can add new hints between passes by editing REFINEMENT_HINTS.md directly. The next refinement pass picks them up automatically.

The user can also run a fresh cross-model audit (Mode 3 of the review protocol) between refinement passes to find new gaps that the previous refinement didn't catch. This creates a review → refine → review → refine cycle that converges on completeness.
```
