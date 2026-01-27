---
name: rfc-architect
description: Design and structure technical RFCs, design documents, and decision records. Use when users need to write technical proposals, architecture decision records (ADRs), design docs, or technical specifications that require stakeholder input and approval. Triggers on requests like "write an RFC", "create a design doc", "architecture decision record", "technical proposal", or "document this design decision".
---

# RFC Architect

Create structured technical decision documents that clearly communicate proposals, trade-offs, and rationale.

## Document Types

### RFC (Request for Comments)
Formal proposal seeking feedback before implementation. Used for significant changes.

### Design Doc
Technical specification for how something will be built. More implementation-focused.

### ADR (Architecture Decision Record)
Lightweight record of a specific decision and its context. Good for building decision history.

## RFC Template

```markdown
# RFC: [Title]

**Status**: Draft | In Review | Accepted | Rejected | Superseded
**Author(s)**: [Names]
**Created**: [Date]
**Last Updated**: [Date]
**Reviewers**: [Names]

## Summary

[2-3 sentences describing what this RFC proposes]

## Motivation

### Problem Statement
[What problem are we solving? Why now?]

### Goals
- [Goal 1]
- [Goal 2]

### Non-Goals
- [Explicitly out of scope]

## Proposal

### Overview
[High-level description of the proposed solution]

### Detailed Design

#### [Component/Aspect 1]
[Technical details, diagrams if helpful]

#### [Component/Aspect 2]
[Continue for each major component]

### API/Interface Changes
[If applicable: new endpoints, function signatures, etc.]

```python
# Example code or pseudocode
```

## Alternatives Considered

### Alternative 1: [Name]
**Description**: [What this option looks like]
**Pros**:
- [Advantage]
**Cons**:
- [Disadvantage]
**Why not chosen**: [Reason]

### Alternative 2: [Name]
[Same structure]

## Trade-offs and Risks

| Decision | Trade-off |
|----------|-----------|
| [Choice] | [What we give up for what we gain] |

### Risks
- **Risk 1**: [Description] — Mitigation: [How we'll address it]
- **Risk 2**: [Description] — Mitigation: [How we'll address it]

## Migration/Rollout Strategy

### Phase 1: [Name]
- [Steps]
- Success criteria: [How we know it worked]

### Phase 2: [Name]
[Continue as needed]

### Rollback Plan
[How to undo if needed]

## Dependencies

- [System/team this depends on]
- [External service]

## Open Questions

- [ ] [Question needing resolution before proceeding]
- [ ] [Another question]

## References

- [Link to related doc]
- [Prior art / inspiration]
```

## ADR Template (Lightweight)

For recording decisions without full RFC process:

```markdown
# ADR-[NUMBER]: [Title]

**Date**: [Date]
**Status**: Proposed | Accepted | Deprecated | Superseded by ADR-XXX

## Context

[What situation led to this decision? What constraints exist?]

## Decision

[What did we decide? State it clearly.]

## Consequences

### Positive
- [Benefit 1]
- [Benefit 2]

### Negative
- [Trade-off 1]
- [Trade-off 2]

### Neutral
- [Other implications]
```

## Decision Matrix

When comparing options, use a decision matrix:

```markdown
## Evaluation Matrix

| Criteria (weight) | Option A | Option B | Option C |
|-------------------|----------|----------|----------|
| Performance (3)   | 3 (9)    | 2 (6)    | 3 (9)    |
| Simplicity (2)    | 2 (4)    | 3 (6)    | 1 (2)    |
| Cost (2)          | 1 (2)    | 2 (4)    | 3 (6)    |
| Team familiarity (1) | 3 (3) | 2 (2)    | 1 (1)    |
| **Total**         | **18**   | **18**   | **18**   |

Scoring: 1 = Poor, 2 = Adequate, 3 = Excellent
Weighted score in parentheses
```

## Writing Effective Sections

### Motivation

Bad:
> We should use Kafka.

Good:
> Our current message queue drops messages under peak load (3x in the past month),
> causing data inconsistencies that require manual intervention. We need a more
> reliable messaging system that can handle our projected 10x traffic growth.

### Alternatives

Always include at least:
1. **Do nothing** - What happens if we don't act?
2. **Minimal change** - Smallest intervention that might work
3. **Proposed solution** - Your recommendation
4. **Ambitious option** - If resources were unlimited

### Trade-offs

Make trade-offs explicit:

```markdown
## Trade-offs

We're choosing **consistency over availability**: During network partitions,
the system will reject writes rather than risk data inconsistency.

We're choosing **simplicity over flexibility**: Using a fixed schema means
less runtime configuration but requires code changes for new fields.
```

## Review Process Guidance

### Before Review
- [ ] All sections complete (mark unknowns explicitly)
- [ ] Diagrams clear without explanation
- [ ] Alternatives genuinely considered
- [ ] Dependencies identified and owners notified
- [ ] Open questions are real blockers, not padding

### During Review
Expect feedback on:
- Missing alternatives
- Underestimated risks
- Unclear migration path
- Missing stakeholder concerns

### After Acceptance
- Update status to "Accepted"
- Create implementation tasks
- Share final version widely
- Archive for future reference

## Common Patterns

### The "Strangler Fig" Migration

```markdown
## Migration Strategy

We'll incrementally replace the old system:

1. **Proxy Phase**: New system proxies to old
   - Duration: 2 weeks
   - Rollback: Disable proxy

2. **Parallel Phase**: Both systems process, compare results
   - Duration: 4 weeks
   - Success: <0.1% discrepancy

3. **Cutover Phase**: New system primary, old as fallback
   - Duration: 2 weeks
   - Rollback: Swap traffic back

4. **Retirement**: Decommission old system
   - After 30 days of stable operation
```

### The "Feature Flag" Rollout

```markdown
## Rollout Strategy

1. **Internal**: Enable for employees (1 week)
2. **Canary**: 1% of production traffic (1 week)
3. **Gradual**: 10% → 50% → 100% (2 weeks each)

Rollback: Disable feature flag (immediate)
```

## Anti-Patterns to Avoid

| Anti-Pattern | Problem | Instead |
|--------------|---------|---------|
| "Obviously we should..." | Assumes consensus | State reasoning explicitly |
| No alternatives | Looks predetermined | Always show options considered |
| Vague migration | Scares stakeholders | Break into concrete phases |
| No rollback plan | Single point of failure | Always have an undo strategy |
| Hidden trade-offs | Erodes trust | Make downsides explicit |

## Naming Conventions

### RFC Numbers
- Sequential: RFC-001, RFC-002
- Or date-based: RFC-2024-03-AUTH

### ADR Numbers
- Sequential: ADR-0001, ADR-0002
- Keep a central index

### File Organization
```
docs/
├── rfcs/
│   ├── RFC-001-new-auth-system.md
│   └── RFC-002-database-migration.md
└── adrs/
    ├── 0001-use-postgresql.md
    └── 0002-adopt-typescript.md
```
