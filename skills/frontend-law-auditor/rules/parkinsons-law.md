# Rule: Parkinson's Law

## Why this law matters
- Mechanism: work expands to fill available time and scope.
- User risk when violated: feature creep degrades core usability.

## Failure signals
- non-critical features added into core release path.
- added complexity without measurable user-value gain.

## Audit checks
- release scope stays aligned to primary user goals.
- `scope_creep_signals == false`.

## Typical fixes
- enforce MVP boundaries and defer optional enhancements.
- require measurable hypothesis for new UI complexity.

## Acceptance criteria
- leaner release with stable core flow outcomes.
- fewer regressions from late-stage additions.

## Related metrics
- `scope_creep_signals`
