# RRULE Guide

The `expand_rrule` tool expands RFC 5545 recurrence rules into concrete event instances using Truth Engine — deterministic computation, not LLM inference.

## Common Patterns

| Pattern | RRULE | Example |
|---------|-------|---------|
| Every weekday | `FREQ=WEEKLY;BYDAY=MO,TU,WE,TH,FR` | Daily standup |
| Biweekly Monday | `FREQ=WEEKLY;INTERVAL=2;BYDAY=MO` | Sprint planning |
| Monthly on 15th | `FREQ=MONTHLY;BYMONTHDAY=15` | Payroll |
| Last Friday of month | `FREQ=MONTHLY;BYDAY=FR;BYSETPOS=-1` | Monthly review |
| Third Tuesday | `FREQ=MONTHLY;BYDAY=TU;BYSETPOS=3` | Board meeting |
| Yearly Feb 29 | `FREQ=YEARLY;BYMONTH=2;BYMONTHDAY=29` | Leap year event |

## Input Format

```json
{
  "rrule": "FREQ=WEEKLY;BYDAY=MO,WE,FR",
  "dtstart": "2026-03-01T09:00:00",
  "timezone": "America/New_York",
  "duration_minutes": 60,
  "count": 10
}
```

**Important**: `dtstart` is a **local datetime** (no timezone suffix). The `timezone` parameter determines how it maps to UTC. `UNTIL` values in the RRULE must be in UTC when a timezone is specified.

## 5 Edge Cases Where LLMs Fail

### 1. DST Transitions

"Third Tuesday of March 2026" (spring-forward on March 8):
- Pre-DST: UTC offset -05:00 → Post-DST: -04:00
- LLMs often produce wrong UTC time or skip the month

Truth Engine: Correct UTC conversion across the DST boundary.

### 2. BYSETPOS=-1 (Last Occurrence)

`FREQ=MONTHLY;BYDAY=FR;BYSETPOS=-1` means "last Friday of the month."
- Months have 4 or 5 Fridays — the last one varies
- LLMs frequently return the first Friday instead

Truth Engine: Correctly identifies the last occurrence in every month.

### 3. EXDATE with Timezones

Excluding specific dates requires exact timezone matching:
- `EXDATE` values must match the generated instances exactly
- LLMs often ignore EXDATE entirely or apply it to wrong dates

Truth Engine: Exact matching with timezone-aware comparison.

### 4. INTERVAL with BYDAY

`FREQ=WEEKLY;INTERVAL=2;BYDAY=MO,WE,FR` means every-other-week on Mon/Wed/Fri.
- `INTERVAL=2` applies to weeks, not individual days
- LLMs frequently generate every-week occurrences

Truth Engine: Correct interval application to the frequency unit.

### 5. Leap Year Recurrence

`FREQ=YEARLY;BYMONTH=2;BYMONTHDAY=29` should only produce instances in leap years.
- 2028, 2032, 2036... are leap years
- LLMs often generate Feb 28 or Mar 1 in non-leap years

Truth Engine: Only produces instances when Feb 29 exists.
