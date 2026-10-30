# Rule: Miller's Law

## Why this law matters
- Mechanism: working memory can hold only limited chunks at once.
- User risk when violated: overload, errors, and form abandonment.

## Failure signals
- long dense forms or giant option blocks.
- users repeatedly scroll/backtrack to re-parse content.

## Audit checks
- information chunk count stays in manageable range.
- `chunk_count` stays within 3 to 9 where possible.

## Typical fixes
- split long tasks into step-based flows.
- group fields/options into meaningful sections.

## Acceptance criteria
- improved completion rate for long flows.
- reduced correction loops in complex forms.

## Related metrics
- `chunk_count`
- `screen_choice_count`
