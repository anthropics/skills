# Team Collaboration Protocol

## Purpose

Guidelines for coordinating multi-person academic research teams using the pipeline. Claude Code runs as a single-user session; this protocol documents the **human coordination layer** that wraps around pipeline executions.

---

## Role Definitions

| Role | Pipeline Stages | Responsibilities |
|------|----------------|-----------------|
| Research Lead | Stage 1 (RESEARCH) | Defines RQ, manages literature search, approves synthesis, sets theoretical framework |
| Lead Author | Stage 2 (WRITE), Stage 4/4' (REVISE) | Writes/revises paper, makes final content decisions, owns the manuscript |
| Methods Specialist | Stage 1 (methodology), Stage 2 (methods section) | Ensures methodological rigor, validates statistical analysis, reviews data integrity |
| Review Coordinator | Stage 3/3' (REVIEW) | Manages simulated review process, distributes feedback, facilitates revision coaching |
| Integration Lead | All stages | Ensures consistency across stages, manages handoffs, resolves cross-stage conflicts |

### Role Assignment Rules

- One person may hold multiple roles (common in small teams)
- Research Lead and Lead Author are the minimum required roles (can be the same person)
- Integration Lead is recommended for teams of 3+
- Methods Specialist is strongly recommended for empirical papers
- All role assignments should be documented at pipeline intake

---

## Handoff Protocol

For each stage transition, the following handoff procedure applies:

### Stage 1 -> Stage 2 (Research -> Write)

| Item | Detail |
|------|--------|
| **Who hands off** | Research Lead |
| **Who receives** | Lead Author |
| **Materials** | RQ Brief, Bibliography, Synthesis Report (conforming to Schemas 1-3 in `shared/handoff_schemas.md`) |
| **Approval needed** | Research Lead confirms synthesis is complete and RQ is finalized |
| **Handoff checklist** | All Material Passports (Schema 9) attached; Bibliography minimum source count met; Synthesis has 3+ themes |

### Stage 2 -> Stage 2.5 (Write -> Integrity)

| Item | Detail |
|------|--------|
| **Who hands off** | Lead Author |
| **Who receives** | Integration Lead (or Lead Author if no Integration Lead) |
| **Materials** | Paper Draft (conforming to Schema 4) |
| **Approval needed** | Lead Author confirms draft is ready for verification |
| **Handoff checklist** | All sections complete; reference list formatted; word count within target range |

### Stage 2.5 -> Stage 3 (Integrity -> Review)

| Item | Detail |
|------|--------|
| **Who hands off** | Integration Lead |
| **Who receives** | Review Coordinator |
| **Materials** | Verified Paper Draft + Integrity Report (Schema 5) |
| **Approval needed** | Integrity verdict is PASS; any PASS_WITH_CONDITIONS items acknowledged |
| **Handoff checklist** | Integrity Report attached; all SERIOUS/MEDIUM issues resolved |

### Stage 3 -> Stage 4 (Review -> Revise)

| Item | Detail |
|------|--------|
| **Who hands off** | Review Coordinator |
| **Who receives** | Lead Author + Methods Specialist (if methodology issues) |
| **Materials** | Review Report (Schema 6) + Revision Roadmap (Schema 7) |
| **Approval needed** | Review Coordinator confirms roadmap is complete; Lead Author reviews before starting |
| **Handoff checklist** | All revision items categorized and prioritized; coaching session completed (or skipped by Lead Author) |

### Stage 4 -> Stage 3' (Revise -> Re-Review)

| Item | Detail |
|------|--------|
| **Who hands off** | Lead Author |
| **Who receives** | Review Coordinator |
| **Materials** | Revised Draft + Response to Reviewers (Schema 8) |
| **Approval needed** | Lead Author confirms all addressable items are handled |
| **Handoff checklist** | Response to Reviewers covers every roadmap item; new references verified |

### Stage 4.5 -> Stage 5 (Final Integrity -> Finalize)

| Item | Detail |
|------|--------|
| **Who hands off** | Integration Lead |
| **Who receives** | Lead Author |
| **Materials** | Final Verified Draft + Final Integrity Report |
| **Approval needed** | Integrity verdict PASS with zero issues |
| **Handoff checklist** | All previous integrity issues confirmed resolved; Material Passport updated to VERIFIED |

---

## Version Control

### Git Branching Strategy

```
main
  |-- paper/draft-v1          (Stage 2 output)
  |-- paper/post-integrity-v1 (Stage 2.5 output)
  |-- paper/post-review-v1    (Stage 4 output)
  |-- paper/final-v1          (Stage 5 output)
```

### Tagging Convention

| Tag | When | Example |
|-----|------|---------|
| `v0.1-draft` | After Stage 2 completion | First complete draft |
| `v0.2-post-integrity` | After Stage 2.5 PASS | Draft verified for integrity |
| `v0.3-post-review` | After Stage 4 completion | First revision complete |
| `v0.4-post-rereview` | After Stage 4' completion (if applicable) | Second revision complete |
| `v1.0-final` | After Stage 5 completion | Final manuscript |

### Rules

- Never overwrite; always create a new version
- All versions are preserved for audit trail
- Version labels must match the Material Passport `version_label` field (Schema 9 in `shared/handoff_schemas.md`)
- Each team member's changes should be attributable (use git author info)

---

## Conflict Resolution

| Conflict Type | Resolution Authority | Escalation Path |
|--------------|---------------------|-----------------|
| Content disagreements | Lead Author has final say | If unresolved: Research Lead mediates |
| Methodological disagreements | Methods Specialist has final say | If unresolved: cite literature precedent |
| Scope disagreements | Research Lead has final say | If unresolved: team vote |
| Formatting/style disagreements | Lead Author has final say | Follow target journal guidelines |
| Integrity findings disagreements | Integration Lead has final say | Cannot override SERIOUS findings |

### Disagreement Documentation

All disagreements must be documented in the revision tracking:

```markdown
## Disagreement Record

**Date**: [date]
**Stage**: [stage]
**Parties**: [who disagreed]
**Issue**: [what the disagreement was about]
**Resolution**: [how it was resolved]
**Authority**: [who made the final call]
**Rationale**: [why this decision was made]
```

---

## Communication Templates

### 1. Handoff Notification

```markdown
## Handoff: Stage [X] -> Stage [Y]

**From**: [Role] ([Name])
**To**: [Role] ([Name])
**Date**: [date]

**Materials Delivered**:
- [Material 1] (version: [version_label])
- [Material 2] (version: [version_label])

**Status Summary**:
[1-2 sentence summary of what was accomplished and any open items]

**Action Required**:
[What the receiving person needs to do next]

**Deadline**: [if applicable]
```

### 2. Review Request

```markdown
## Review Request: [Paper Title]

**From**: [Review Coordinator]
**To**: [Team / External Reviewer]
**Date**: [date]

**Paper Version**: [version_label]
**Word Count**: [N]
**Review Type**: [Internal simulated / External journal / Team peer review]

**Focus Areas**:
1. [specific area to focus on]
2. [specific area to focus on]

**Deadline**: [date]
**Return Format**: [Use Schema 6 format from shared/handoff_schemas.md]
```

### 3. Revision Assignment

```markdown
## Revision Assignment: [Paper Title]

**From**: [Review Coordinator]
**To**: [Lead Author / Methods Specialist]
**Date**: [date]

**Revision Round**: [N]
**Total Items**: [N] (must_fix: [N], should_fix: [N], consider: [N])

**Your Assignments**:
- [REV-001]: [brief description] — assigned to [name]
- [REV-003]: [brief description] — assigned to [name]

**Deadline**: [date]
**Coordination Notes**: [any dependencies between revision items]
```

---

## Workflow for Teams

### Small Team (2-3 people)

```
Person A (Research Lead + Lead Author):
  - Runs Stage 1 (RESEARCH) with their Claude session
  - Runs Stage 2 (WRITE) with their Claude session
  - Receives revision items, runs Stage 4/4'
  - Runs Stage 5 (FINALIZE)

Person B (Methods Specialist + Review Coordinator):
  - Reviews Stage 1 methodology output
  - Reviews Stage 2 methods section
  - Manages Stage 3/3' review process
  - Handles specific methodology revision items

Handoff: via shared folder or git repo
Materials: conform to schemas in shared/handoff_schemas.md
```

### Large Team (4+ people)

```
Add Integration Lead role:
  - Monitors all stage transitions
  - Validates handoff completeness
  - Resolves cross-stage inconsistencies
  - Maintains pipeline state document (shared with all team members)
```

---

## Limitations

- Claude Code runs as a single-user session; this protocol documents the HUMAN coordination layer
- Each team member runs their own pipeline stages independently in separate Claude sessions
- Handoff materials (conforming to schemas in `shared/handoff_schemas.md`) ensure consistency across sessions
- Real-time co-editing is not supported; use git or shared documents for synchronization
- Pipeline state tracking is per-session; the Integration Lead must manually synchronize state across sessions
- The pipeline does not enforce team role permissions; discipline is maintained by convention
