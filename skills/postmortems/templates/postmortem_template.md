# Postmortem: [Incident Title]

**Incident ID:** [INC-YYYY-MMDD-NNN]  
**Date:** [YYYY-MM-DD]  
**Duration:** [X hours Y minutes]  
**Severity:** [Level 1/2/3/4]  
**Status:** [Resolved/Resolved with follow-up]

---

## Executive Summary

[2-3 sentence overview of the incident, impact, root cause, and key actions]

**Impact:** [Brief impact statement]

**Root Cause:** [Brief root cause statement]

**Key Actions:** [Top 2-3 most important action items]

---

## Incident Details

### Basic Information

- **Incident ID:** [INC-YYYY-MMDD-NNN]
- **Title:** [Descriptive title]
- **Date:** [YYYY-MM-DD]
- **Start Time:** [HH:MM UTC]
- **End Time:** [HH:MM UTC]
- **Duration:** [X hours Y minutes]
- **Severity Level:** [1/2/3/4]
- **Affected Services:** [List services/systems]
- **Postmortem Lead:** [Name/Role]
- **Postmortem Date:** [YYYY-MM-DD]

### Severity Level

[ ] **Level 1 - Critical**: Complete service outage or severe degradation affecting all users
[ ] **Level 2 - High**: Significant service degradation affecting large portion of users
[ ] **Level 3 - Medium**: Moderate impact affecting subset of users or features
[ ] **Level 4 - Low**: Minor impact with workaround available

---

## Impact

### User Impact

- **Affected Users:** [Number or percentage]
- **User-Facing Symptoms:** [What users experienced]
- **Geographic Impact:** [If applicable]
- **Feature Impact:** [Which features were affected]

### Business Impact

- **Revenue Impact:** [If applicable]
- **SLA Breaches:** [If applicable]
- **Customer Complaints:** [Number or description]
- **Reputation Impact:** [If applicable]

### Technical Metrics

- **Error Rate:** [Percentage or absolute numbers]
- **Latency Increase:** [If applicable]
- **Throughput Reduction:** [If applicable]
- **Data Loss:** [If applicable]
- **Other Metrics:** [Custom metrics relevant to the incident]

---

## Timeline

[Chronological sequence of events. Use role-based language, not names.]

| Time (UTC) | Event | Actor | Details |
|------------|-------|-------|---------|
| HH:MM | First alert/detection | [Role, e.g., "On-call engineer"] | [What was detected] |
| HH:MM | Investigation started | [Role] | [Initial investigation steps] |
| HH:MM | Communication sent | [Role] | [Internal/external communication] |
| HH:MM | Mitigation attempt #1 | [Role] | [What was tried] |
| HH:MM | Status update | [Role] | [Update content] |
| HH:MM | Root cause identified | [Role] | [What was found] |
| HH:MM | Fix deployed | [Role] | [Fix description] |
| HH:MM | Incident resolved | [Role] | [Resolution confirmation] |

### Key Decisions

1. **[Time]**: [Decision made] - [Rationale]
2. **[Time]**: [Decision made] - [Rationale]
3. **[Time]**: [Decision made] - [Rationale]

---

## Root Cause Analysis

### Immediate Cause

[What directly caused the incident to occur]

### Contributing Factors

1. **[Factor 1]**: [Description]
2. **[Factor 2]**: [Description]
3. **[Factor 3]**: [Description]

### Root Cause(s)

[The underlying system, process, or design issue that allowed the incident to occur]

**Why existing safeguards didn't prevent it:**

[Explanation of why monitoring, testing, processes, or other safeguards failed to prevent or catch this issue]

### Causal Chain

```
[Immediate Symptom]
  ↓
[Immediate Cause]
  ↓
[Contributing Factor]
  ↓
[Root Cause]
```

### 5 Whys Analysis

1. **Why did [symptom] occur?**  
   → [Answer]

2. **Why did [answer 1] happen?**  
   → [Answer]

3. **Why did [answer 2] happen?**  
   → [Answer]

4. **Why did [answer 3] happen?**  
   → [Answer]

5. **Why did [answer 4] happen?**  
   → [Root cause]

---

## Resolution

### How the Incident Was Resolved

[Step-by-step description of how the incident was resolved]

### Immediate Mitigation Steps

1. **[Action]**: [Description]
2. **[Action]**: [Description]
3. **[Action]**: [Description]

### Long-Term Fixes Applied

1. **[Fix]**: [Description]
2. **[Fix]**: [Description]

---

## Action Items

[Each action item should be: Actionable (verb + outcome), Specific (narrow scope), Bounded (clear completion criteria)]

### Investigate This Incident

| ID | Action | Owner | Priority | Deadline | Status |
|----|--------|-------|----------|----------|--------|
| AI-1 | [Actionable, specific, bounded action] | [Name] | [High/Medium/Low] | [Date] | [Open/In Progress/Done] |

### Mitigate This Incident

| ID | Action | Owner | Priority | Deadline | Status |
|----|--------|-------|----------|----------|--------|
| AI-2 | [Actionable, specific, bounded action] | [Name] | [High/Medium/Low] | [Date] | [Open/In Progress/Done] |

### Repair Damage from This Incident

| ID | Action | Owner | Priority | Deadline | Status |
|----|--------|-------|----------|----------|--------|
| AI-3 | [Actionable, specific, bounded action] | [Name] | [High/Medium/Low] | [Date] | [Open/In Progress/Done] |

### Detect Future Incidents

| ID | Action | Owner | Priority | Deadline | Status |
|----|--------|-------|----------|----------|--------|
| AI-4 | [Actionable, specific, bounded action] | [Name] | [High/Medium/Low] | [Date] | [Open/In Progress/Done] |

### Mitigate Future Incidents

| ID | Action | Owner | Priority | Deadline | Status |
|----|--------|-------|----------|----------|--------|
| AI-5 | [Actionable, specific, bounded action] | [Name] | [High/Medium/Low] | [Date] | [Open/In Progress/Done] |

### Prevent Future Incidents

| ID | Action | Owner | Priority | Deadline | Status |
|----|--------|-------|----------|--------|--------|
| AI-6 | [Actionable, specific, bounded action] | [Name] | [High/Medium/Low] | [Date] | [Open/In Progress/Done] |

**Priority Actions:** [List the 2-3 most critical action items that address the root cause]

---

## Lessons Learned

### What Went Well

1. **[Positive aspect]**: [Description]
2. **[Positive aspect]**: [Description]
3. **[Positive aspect]**: [Description]

### What Could Be Improved

1. **[Area for improvement]**: [Description]
2. **[Area for improvement]**: [Description]
3. **[Area for improvement]**: [Description]

### Systemic Improvements Needed

1. **[Systemic change]**: [Description]
2. **[Systemic change]**: [Description]

---

## Related Incidents

- [Link to related incident #1]
- [Link to related incident #2]

---

## Appendices

### A. Relevant Logs

[Links to or excerpts from relevant logs]

### B. Graphs and Metrics

[Links to dashboards, graphs, or screenshots showing the incident]

### C. Configuration Changes

[If applicable, document configuration changes made during or after the incident]

### D. References

- [Link to monitoring dashboard]
- [Link to runbook used]
- [Link to related documentation]
- [Link to code changes]

---

## Approval

**Postmortem Lead:** [Name] - [Date]

**Service Owner:** [Name] - [Date]

**Approver:** [Name] - [Date]

---

## Follow-Up

**Next Review Date:** [Date]

**Action Item Review:** [Date]

---

*This postmortem follows blameless postmortem principles. We focus on systems, processes, and roles rather than individuals to create a culture of learning and continuous improvement.*
