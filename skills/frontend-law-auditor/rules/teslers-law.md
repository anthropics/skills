# Rule: Tesler's Law

## Why this law matters
- Mechanism: complexity cannot be removed, only shifted.
- User risk when violated: users carry implementation complexity and fail more often.

## Failure signals
- manual entry required where system could infer/assist.
- inconsistent free-text data creates downstream cleanup burden.

## Audit checks
- system provides smart defaults, autocomplete, and structured controls.
- `system_handles_complexity == true`.

## Typical fixes
- replace free text with pickers/masks where appropriate.
- normalize data structures behind the scenes.

## Acceptance criteria
- lower input effort and lower invalid-entry rate.
- improved consistency of captured data.

## Related metrics
- `system_handles_complexity`
- `input_tolerant_parsing`
