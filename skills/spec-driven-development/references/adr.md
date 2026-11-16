# Architecture Decision Records (ADR)

Specs capture decisions per feature. Some decisions outlive their feature —
they bind future features too. Those get an ADR, at repo level (e.g.
`docs/decisions/`), **before** new work builds on them.

When to write one: choosing a database, a transport, an architectural pattern,
a directory convention, a security posture — anything a future feature must
respect or would silently break. If a design document's rejected alternative
keeps coming back in later discussions, promote it to an ADR.

## Template

```markdown
# ADR-NNNN: <short title of the decision>

- **Date:** YYYY-MM-DD
- **Status:** proposed | accepted | superseded by ADR-XXXX
- **Feature:** <feature name, or "project-level">

## Context

What forces are in play — technical, organizational, deadlines. State the problem,
not the solution.

## Decision

The decision itself, in one or two sentences, active voice.

## Alternatives considered

For each alternative: what it was, why it was rejected (one or two lines).

## Consequences

What becomes easier, what becomes harder, what must now be true. Include the
reversibility cost ("cheap to reverse" / "expensive — revisit before changing").
```

## Rules

- IDs are stable and never reused; a replaced decision is `superseded by
  ADR-XXXX`, not deleted.
- State the problem in Context before the Decision — an ADR that starts with
  the answer cannot be reviewed.
- Reversibility cost is mandatory: the reader must know what changing this
  later will cost.
