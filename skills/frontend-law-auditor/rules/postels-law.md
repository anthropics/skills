# Rule: Postel's Law

## Why this law matters
- Mechanism: robust systems accept varied human input and emit normalized output.
- User risk when violated: brittle validation and avoidable dead-end errors.

## Failure signals
- common input variants are rejected.
- errors are vague and non-actionable.

## Audit checks
- tolerant parsing is implemented for common formats.
- inline error guidance is specific and recoverable.

## Typical fixes
- accept common date/phone/address variants and normalize.
- rewrite errors to include cause and exact recovery path.

## Acceptance criteria
- fewer validation dead-ends and retries.
- improved form completion and reduced support tickets.

## Related metrics
- `input_tolerant_parsing`
- `inline_validation_clear`
