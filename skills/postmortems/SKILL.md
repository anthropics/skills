---
name: postmortems
description: Guide for creating comprehensive, blameless incident postmortems that help teams learn from incidents, identify root causes, and prevent future occurrences. Use when conducting post-incident reviews, writing postmortem reports, or analyzing incidents to improve system reliability.
license: Complete terms in LICENSE.txt
---

# Incident Postmortems

A comprehensive guide for creating effective, blameless postmortems that help teams learn from incidents and improve system reliability.

## When to use this skill

Use this skill when:
- Conducting post-incident reviews after system outages or incidents
- Writing postmortem reports for incidents with severity level 2 or higher
- Analyzing incidents to identify root causes and preventive measures
- Creating action items to mitigate and prevent future incidents
- Documenting incident timelines and impact
- Facilitating blameless postmortem meetings

## Overview

A postmortem is a written record of an incident that describes:
- The incident's impact
- The actions taken to mitigate or resolve the incident
- The incident's root cause
- Follow-up actions to prevent the incident from recurring

Postmortems should be **blameless** - focusing on systems, processes, and roles rather than individuals. This creates a culture of learning and continuous improvement.

## Postmortem Process

### 1. Determine When to Write a Postmortem

**Trigger thresholds:**
- Any incident with severity level 1 or 2 (critical or high)
- Incidents that caused significant user impact
- Incidents that exposed systemic issues
- Incidents that required escalation or major remediation efforts

**Timeline:**
- Schedule postmortem meeting within 24-48 hours of incident resolution
- Complete postmortem report within 5 business days of the meeting

### 2. Assemble the Postmortem Team

**Key participants:**
- Incident commander/responder
- On-call engineer(s) involved
- Service owners
- Subject matter experts relevant to the incident
- Anyone who made key decisions during the incident

**Roles:**
- **Postmortem Lead**: Facilitates the meeting and writes the report
- **Timeline Scribe**: Documents the chronological sequence of events
- **Action Item Owner**: Tracks and assigns follow-up actions

### 3. Conduct the Postmortem Meeting

**Meeting structure:**

1. **Opening (5 minutes)**
   - State that this is a blameless postmortem
   - Explain why blameless postmortems are important
   - Set ground rules: focus on systems and processes, not individuals

2. **Timeline Construction (20-30 minutes)**
   - Build a chronological timeline of events
   - Include: first alert, detection, communication, mitigation attempts, resolution
   - Use role-based language (e.g., "the on-call engineer") not names
   - Document all key decisions and actions

3. **Impact Assessment (10 minutes)**
   - Quantify user impact (affected users, duration, error rates)
   - Document business impact (revenue, SLA breaches, customer complaints)
   - Record technical metrics (downtime, error rates, performance degradation)

4. **Root Cause Analysis (20-30 minutes)**
   - Use "5 Whys" technique to dig deeper
   - Identify contributing factors, not just the immediate cause
   - Consider: system design, process gaps, monitoring gaps, human factors
   - Frame in terms of systems and processes, not individual actions

5. **Action Items (20-30 minutes)**
   - Generate actionable, specific, bounded action items
   - Categorize by: investigate, mitigate, repair, detect, mitigate future, prevent
   - Assign owners and deadlines
   - Prioritize actions that address root causes

6. **Closing (5 minutes)**
   - Summarize key learnings
   - Confirm action item assignments
   - Schedule follow-up review if needed

### 4. Write the Postmortem Report

**Report structure:**

Use the template in `templates/postmortem_template.md` as a starting point. The report should include:

1. **Executive Summary**
   - Brief overview of the incident
   - Impact summary
   - Root cause summary
   - Key actions

2. **Incident Details**
   - Incident ID and title
   - Date and duration
   - Severity level
   - Affected services/systems

3. **Impact**
   - User impact (quantified)
   - Business impact
   - Technical metrics

4. **Timeline**
   - Chronological sequence of events
   - Key decisions and actions
   - Communication milestones

5. **Root Cause Analysis**
   - Immediate cause
   - Contributing factors
   - Root cause(s)
   - Why existing safeguards didn't prevent it

6. **Resolution**
   - How the incident was resolved
   - Immediate mitigation steps taken
   - Long-term fixes applied

7. **Action Items**
   - Categorized by type (investigate, mitigate, repair, detect, mitigate future, prevent)
   - Each action should be:
     - **Actionable**: Phrase as a sentence starting with a verb
     - **Specific**: Define scope narrowly
     - **Bounded**: Indicate how to tell when it's finished
   - Include owner, priority, and deadline

8. **Lessons Learned**
   - What went well
   - What could be improved
   - Systemic improvements needed

9. **Appendices**
   - Relevant logs, graphs, or screenshots
   - Links to related incidents or documentation

## Blameless Postmortem Principles

**Core principles:**
- Assume good intentions on the part of all staff
- Never blame people for faults
- Focus on systems, processes, and roles, not individuals
- Ask "why did the system allow this" not "why did this person do this"

**Techniques for creating personal safety:**
- Open meetings by stating this is a blameless postmortem and why
- Refer to individuals by role (e.g., "the on-call engineer") not name
- Frame timeline, causal chain, and mitigations in context of systems and processes
- Use "second stories" - alternative explanations that focus on systemic factors

**Example reframing:**
- ❌ "John deployed the buggy code"
- ✅ "The deployment process allowed code without sufficient tests to reach production"

## Action Item Categories

When creating action items, work through these categories to ensure comprehensive coverage:

| Category | Question to Ask | Examples |
|----------|----------------|----------|
| **Investigate this incident** | "What happened to cause this incident and why?" | Logs analysis, diagramming request path, reviewing heap dumps |
| **Mitigate this incident** | "What immediate actions did we take to resolve this specific event?" | Rolling back, cherry-picking, pushing configs, communicating with users |
| **Repair damage from this incident** | "How did we resolve immediate or collateral damage?" | Restoring data, fixing machines, removing traffic re-routes |
| **Detect future incidents** | "How can we decrease time to accurately detect similar failures?" | Monitoring, alerting, plausibility checks on input/output |
| **Mitigate future incidents** | "How can we decrease severity/duration of future incidents like this?" | Graceful degradation, dropping non-critical results, failing open, dashboards, playbooks |
| **Prevent future incidents** | "How can we prevent a recurrence of this sort of failure?" | Stability improvements, thorough unit tests, input validation, provisioning changes |

**Action item wording guidelines:**

| From (Poor) | To (Good) | Why |
|------------|-----------|-----|
| Investigate monitoring for this scenario | Add alerting for all cases where this service returns >1% errors | Actionable: specific verb and outcome |
| Fix the issue that caused the outage | Handle invalid postal code in user address form input safely | Specific: narrow scope defined |
| Make sure engineer checks database schema | Add automated pre-submit check for schema changes | Bounded: clear completion criteria |

## Root Cause Analysis Techniques

### 5 Whys

Ask "why" five times to dig deeper into root causes:

1. Why did the service fail? → Database connection timeout
2. Why did the connection timeout? → Connection pool exhausted
3. Why was the pool exhausted? → Long-running queries blocking connections
4. Why were there long-running queries? → Missing index on frequently queried column
5. Why was the index missing? → Database migration script didn't include index creation

### Causal Chain

Build a chain of causation from the immediate symptom to the root cause:

```
Symptom → Immediate Cause → Contributing Factor → Root Cause
```

### Systems Thinking

Consider multiple layers:
- **Technical**: Code, infrastructure, configuration
- **Process**: Deployment, monitoring, on-call procedures
- **Organizational**: Training, documentation, communication

## Third-Party Dependencies

When incidents involve third-party services, use this framework:

1. **Did the 3rd party violate our expectations?**
   - Review and agree with their RCA
   - Or adjust our expectations and increase resilience
   - Or find alternative solutions if expectations are unacceptable

2. **Did the 3rd party meet expectations, but our service failed anyway?**
   - Our service needs to increase resilience

3. **Do we not have clear expectations?**
   - Establish expectations with the 3rd party
   - Share expectations with teams so they can build appropriate resilience

## Postmortem Approval

**Approval process:**
- Postmortems should be reviewed and approved by service owners or managers
- Approval indicates:
  - Agreement with findings, including root cause
  - Agreement that action items adequately address the root cause
- Approvers may request additional actions or identify gaps

**Approval workflow:**
1. Postmortem lead completes draft
2. Share with participants for review
3. Submit to approver(s)
4. Address feedback and revise
5. Final approval and publication

## Postmortem Metrics

Track these metrics to measure postmortem effectiveness:

- **Time to postmortem**: Time from incident resolution to postmortem meeting
- **Time to report**: Time from meeting to completed report
- **Action item completion rate**: Percentage of action items completed on time
- **Incident recurrence rate**: Frequency of similar incidents
- **Postmortem quality score**: Subjective assessment of report completeness and usefulness

## Best Practices

### Do's

✅ **Do** schedule postmortems quickly (24-48 hours)
✅ **Do** include diverse perspectives (not just engineers)
✅ **Do** focus on systems and processes
✅ **Do** create specific, actionable, bounded action items
✅ **Do** follow up on action items
✅ **Do** share postmortems widely for learning
✅ **Do** use templates for consistency
✅ **Do** quantify impact with metrics
✅ **Do** document what went well, not just what went wrong

### Don'ts

❌ **Don't** blame individuals
❌ **Don't** skip postmortems for "small" incidents
❌ **Don't** create vague action items
❌ **Don't** let action items languish without follow-up
❌ **Don't** make postmortems private by default
❌ **Don't** focus only on technical causes
❌ **Don't** rush through root cause analysis
❌ **Don't** create postmortems that are too long or too short

## Templates

Use the template in `templates/postmortem_template.md` when writing postmortems. The template includes:
- All required sections
- Example content for each section
- Guidance on what to include
- Formatting guidelines

## Keywords

postmortem, post-mortem, incident review, post-incident review, blameless postmortem, root cause analysis, incident analysis, outage analysis, incident report, 5 whys, action items, incident response, reliability, SRE
