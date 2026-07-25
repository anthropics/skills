# Incident Report: [INC-YYYY-NNNN] [Title]

**Severity:** SEV[1-4]
**Status:** [Active | Mitigated | Resolved]
**Incident Commander:** [Name]
**Date:** [YYYY-MM-DD]

---

## Executive Summary

[2-3 sentence summary of the incident: what happened, impact scope, resolution status. Written for executive audience — no jargon, focus on business impact.]

---

## Impact Statement

| Metric | Value |
|--------|-------|
| **Duration** | [X hours Y minutes] |
| **Affected Users** | [number or percentage] |
| **Failed Transactions** | [number] |
| **Revenue Impact** | $[amount] |
| **Data Loss** | [Yes/No — if yes, detail below] |
| **SLA Impact** | [X.XX% availability for period] |
| **Affected Regions** | [list regions] |
| **Affected Services** | [list services] |

### Customer-Facing Impact

[Describe what customers experienced: error messages, degraded functionality, complete outage. Be specific about which user journeys were affected.]

---

## Timeline

| Time (UTC) | Phase | Event |
|------------|-------|-------|
| HH:MM | Detection | [First alert or report] |
| HH:MM | Declaration | [Incident declared, channel created] |
| HH:MM | Investigation | [Key investigation findings] |
| HH:MM | Mitigation | [Mitigation action taken] |
| HH:MM | Resolution | [Permanent fix applied] |
| HH:MM | Closure | [Incident closed, monitoring confirmed stable] |

### Key Decision Points

1. **[HH:MM] [Decision]** — [Rationale and outcome]
2. **[HH:MM] [Decision]** — [Rationale and outcome]

### Timeline Gaps

[Note any periods >15 minutes without logged events. These represent potential blind spots in the response.]

---

## Root Cause Analysis

### Root Cause

[Clear, specific statement of the root cause. Not "human error" — describe the systemic failure.]

### Contributing Factors

1. **[Factor Category: Process/Tooling/Human/Environment]** — [Description]
2. **[Factor Category]** — [Description]
3. **[Factor Category]** — [Description]

### 5-Whys Analysis

**Why did the service degrade?**
→ [Answer]

**Why did [answer above] happen?**
→ [Answer]

**Why did [answer above] happen?**
→ [Answer]

**Why did [answer above] happen?**
→ [Answer]

**Why did [answer above] happen?**
→ [Root systemic cause]

---

## Response Metrics

| Metric | Value | Target | Status |
|--------|-------|--------|--------|
| **MTTD** (Mean Time to Detect) | [X min] | <5 min | [Met/Missed] |
| **Time to Declare** | [X min] | <10 min | [Met/Missed] |
| **Time to Mitigate** | [X min] | <60 min (SEV1) | [Met/Missed] |
| **MTTR** (Mean Time to Resolve) | [X min] | <4 hr (SEV1) | [Met/Missed] |
| **Postmortem Timeliness** | [X hours] | <72 hr | [Met/Missed] |

---

## Action Items

| # | Priority | Action | Owner | Deadline | Type | Status |
|---|----------|--------|-------|----------|------|--------|
| 1 | P1 | [Action description] | [owner] | [date] | Detection | Open |
| 2 | P1 | [Action description] | [owner] | [date] | Prevention | Open |
| 3 | P2 | [Action description] | [owner] | [date] | Prevention | Open |
| 4 | P2 | [Action description] | [owner] | [date] | Process | Open |

### Action Item Types

- **Detection**: Improve ability to detect this class of issue faster
- **Prevention**: Prevent this class of issue from occurring
- **Mitigation**: Reduce impact when this class of issue occurs
- **Process**: Improve response process and coordination

---

## Lessons Learned

### What Went Well

- [Specific positive outcome from the response]
- [Specific positive outcome]

### What Didn't Go Well

- [Specific area for improvement]
- [Specific area for improvement]

### Where We Got Lucky

- [Things that could have made this worse but didn't]

---

## Communication Log

| Time (UTC) | Channel | Audience | Summary |
|------------|---------|----------|---------|
| HH:MM | Status Page | External | [Summary of update] |
| HH:MM | Slack #exec | Internal | [Summary of update] |
| HH:MM | Email | Customers | [Summary of notification] |

---

## Participants

| Name | Role |
|------|------|
| [Name] | Incident Commander |
| [Name] | Operations Lead |
| [Name] | Communications Lead |
| [Name] | Subject Matter Expert |

---

## Appendix

### Related Incidents

- [INC-YYYY-NNNN] — [Brief description of related incident]

### Reference Links

- [Link to monitoring dashboard]
- [Link to deployment logs]
- [Link to incident channel archive]

---

*This report follows the blameless postmortem principle. The goal is systemic improvement, not individual accountability. All contributing factors should trace to process, tooling, or environmental gaps that can be addressed with concrete action items.*
