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

**Timeline (team practice reference):**
- Teams typically schedule postmortem meetings within 24-48 hours of incident resolution
- Postmortem reports are usually completed within 5 business days of the meeting
- When assisting with postmortems, help create reports promptly while details are fresh

### 2. Gather Postmortem Information

When helping with a postmortem, ensure you have information from:

**Key sources:**
- Incident commander/responder notes
- On-call engineer(s) involved
- Service owners
- Subject matter experts relevant to the incident
- Anyone who made key decisions during the incident

**Information to collect:**
- Chronological sequence of events
- Decisions made and actions taken
- Impact metrics and measurements
- System logs, monitoring data, or error reports
- Communication records (internal and external)

**Note:** If you're helping organize a postmortem, teams typically involve these roles, but as an AI assistant, focus on synthesizing and documenting the information provided rather than coordinating team participation.

### 3. Postmortem Analysis and Documentation

When helping with postmortems, structure your analysis around these key areas:

1. **Timeline Construction**
   - Build a chronological timeline of events from available information
   - Include: first alert, detection, communication, mitigation attempts, resolution
   - Use role-based language (e.g., "the on-call engineer") not names
   - Document all key decisions and actions mentioned

2. **Impact Assessment**
   - Quantify user impact (affected users, duration, error rates) from provided data
   - Document business impact (revenue, SLA breaches, customer complaints) if available
   - Record technical metrics (downtime, error rates, performance degradation)

3. **Root Cause Analysis**
   - Use "5 Whys" technique to dig deeper into causes
   - Identify contributing factors, not just the immediate cause
   - Consider: system design, process gaps, monitoring gaps, human factors
   - Frame in terms of systems and processes, not individual actions

4. **Action Items Generation**
   - Generate actionable, specific, bounded action items
   - Categorize by: investigate, mitigate, repair, detect, mitigate future, prevent
   - Suggest owners and deadlines based on context
   - Prioritize actions that address root causes

5. **Summary and Learnings**
   - Summarize key learnings from the incident
   - Highlight what went well and what could be improved
   - Identify systemic improvements needed

**Note:** If you're helping facilitate an actual postmortem meeting, teams typically follow a structured agenda with time allocations, but as an AI assistant, focus on helping document and analyze the information provided rather than managing meeting logistics.

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

## Postmortem Review and Approval

**Review considerations:**
- When helping create postmortems, ensure the report is ready for review by service owners or managers
- A complete postmortem should demonstrate:
  - Clear agreement on findings, including root cause
  - Action items that adequately address the root cause
- Be prepared to revise based on feedback from approvers who may request additional actions or identify gaps

**Typical review workflow (for reference):**
1. Complete postmortem draft
2. Share with participants for review
3. Submit to approver(s) for approval
4. Address feedback and revise as needed
5. Final approval and publication

**Note:** Approval processes vary by organization. When assisting, focus on creating comprehensive, well-structured postmortems that facilitate review and approval rather than managing the approval workflow itself.

## Postmortem Metrics

Track these metrics to measure postmortem effectiveness:

- **Time to postmortem**: Time from incident resolution to postmortem meeting
- **Time to report**: Time from meeting to completed report
- **Action item completion rate**: Percentage of action items completed on time
- **Incident recurrence rate**: Frequency of similar incidents
- **Postmortem quality score**: Subjective assessment of report completeness and usefulness

## Best Practices

### Do's

✅ **Do** help create postmortems promptly while details are fresh (teams typically aim for 24-48 hours after resolution)
✅ **Do** incorporate diverse perspectives when information is available (not just engineering views)
✅ **Do** focus on systems and processes
✅ **Do** create specific, actionable, bounded action items
✅ **Do** help track and document action items (follow-up is typically handled by teams)
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
