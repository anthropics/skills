# Postmortem: [Issue Title]

## Issue Overview

**What happened:** [Brief description of what went wrong]

**Impact scope:** [Which services/features/users were affected]

---

## Where It Went Wrong

[Describe specifically where the problem occurred, including:]
- The system/service/feature that failed
- The specific location (code module, configuration, process, etc.)
- The symptoms (error messages, abnormal behavior, etc.)

**Examples:**
- User login service exhausted connection pool during peak hours
- Database migration script missing index creation step
- New feature release didn't check dependency service version compatibility

---

## Why It Went Wrong

### Immediate Cause

[The direct cause that led to the problem]

### Root Cause

[The root cause identified through 5 Whys analysis]

**Why existing safeguards didn't prevent this:**
- [Gaps or deficiencies in monitoring/testing/processes]

### Causal Chain

```
[Symptom]
  ↓
[Immediate Cause]
  ↓
[Root Cause]
```

---

## Impact

### User Impact

- [What users experienced/observed]
- [Affected features/services]

### Business Impact

- [Business metrics impact, if applicable]

### Technical Impact

- [System performance, stability, or other technical consequences]

---

## Resolution

### Immediate Fixes

1. [Emergency measures taken]

### Long-term Solutions

1. [Long-term measures to prevent recurrence]

---

## Action Items

[Each action item should be: Actionable (verb + outcome), Specific (narrow scope), Bounded (clear completion criteria)]

| Action Item | Owner | Priority | Status |
|-------------|-------|----------|--------|
| [Specific, actionable item] | [Owner] | [High/Medium/Low] | [Open/In Progress/Done] |

**Priority Actions:** [List 2-3 most critical action items that address the root cause]

---

## Pre-Release Checklist

**Before future releases, verify these issues are resolved or prevented:**

- [ ] [Check item 1: Related to this issue]
- [ ] [Check item 2: Related to this issue]
- [ ] [Check item 3: Related to this issue]

**Examples:**
- [ ] Does the database migration script include all necessary index creation?
- [ ] Is dependency service version compatibility checked before new feature releases?
- [ ] Are appropriate monitoring and alerts in place?

---

## Lessons Learned

### What Went Well

1. [Positive aspects of the incident response]

### What Could Be Improved

1. [Areas for improvement]

### Systemic Improvements

1. [Systemic changes needed, such as processes, tools, documentation]

---

## Related Links

- [Related code changes]
- [Related documentation]
- [Related monitoring/logs]

---

*This postmortem follows blameless principles, focusing on systems, processes, and roles rather than individuals to promote learning and continuous improvement.*
