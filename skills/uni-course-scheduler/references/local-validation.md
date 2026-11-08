# Local Validation Contract

After generating the Excel workbook, run `scripts/validate_schedule.py` to verify
the output meets all quality requirements.

## Usage

```bash
python3 scripts/validate_schedule.py <excel_file.xlsx>
```

## Checks

| ID | Name | Rule |
|----|------|------|
| time_conflict | Time Conflict Detection | No two sessions overlap in time on the same day. |
| lunch_break | Lunch Break Preservation | The 12:00-13:00 slot is free on every scheduled day. |
| daily_density | Daily Course Density | No day exceeds 6 hours of total class time. |
| credit_total | Credit Total Validation | Total recommended/planned credits are within the typical semester range for the education system. |
| required_coverage | Required Course Coverage | At least one Required course appears in the schedule. |
| missing_fields | Missing Field Detection | No more than 10% of critical fields are marked "NOT_FOUND". |

## Output Format

The validator prints a markdown report:

```markdown
# Schedule Validation Report

**Generated:** 2026-08-03T14:49:41.417288
**Overall:** PASS
**Checks:** 6/6 passed

## Checks

| ID | Name | Result | Details |
|----|------|--------|---------|
| time_conflict | Time Conflict Detection | PASS | No conflicts detected. |
| ...
```

## Failure Handling

If any check fails, the report shows FAIL with details. The Agent should:
1. Report the failure to the student
2. Attempt to fix the issue (e.g., reschedule a conflicting course)
3. Re-run the validator
4. Only deliver the Excel file when all checks pass
