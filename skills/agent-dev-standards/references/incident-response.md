# Incident Response

When an Agent degrades in production, follow this runbook.

## Trigger Conditions

| Signal | Threshold | Action |
|--------|-----------|--------|
| Cache hit rate drop | > 10% in 7 days | Freeze prompt version |
| Error rate spike | > 15% in 1 hour | Rollback to last golden |
| Cost per call spike | > 5x baseline | Rollback, investigate |
| User complaint rate | > 3 reports/day | Trigger golden test suite |

## Runbook

1. **Freeze**: Pin all prompt versions to current. No new changes until incident resolved.
2. **Diagnose**: Compare current golden test scores against baseline. Identify which dimension(s) degraded.
3. **Rollback**: Revert to last known good version (previous major/minor).
4. **Verify**: Run golden test suite on rolled-back version. Confirm scores >= baseline.
5. **Root cause**: Link the degradation to a specific change (prompt version, tool change, dependency upgrade).
6. **Remediate**: Fix the root cause, re-run golden suite, promote new version.
