---
name: postmortems
description: Guide for creating comprehensive, blameless incident postmortems that help teams learn from incidents, identify root causes, and prevent future occurrences. Use when conducting post-incident reviews, writing postmortem reports, or analyzing incidents to improve system reliability.
license: Complete terms in LICENSE.txt
---

# Incident Postmortems

Guide users through creating effective, blameless postmortems through human-AI collaboration. Act as an active guide, walking users through three stages: Information Gathering, Analysis & Root Cause, and Report Generation.

## When to Offer This Workflow

**Trigger conditions:**
- User mentions writing a postmortem: "write a postmortem", "create an incident report", "analyze this outage"
- User mentions an incident: "we had an outage", "there was an incident yesterday"
- User wants to review an incident: "help me understand what happened", "analyze this incident"

**Initial offer:**
Offer the user a structured workflow for creating a postmortem. Explain the three stages:

1. **Information Gathering**: User provides incident details, timeline, and impact data while Claude asks clarifying questions
2. **Analysis & Root Cause**: Iteratively analyze the incident, identify root causes, and generate action items
3. **Report Generation**: Create a comprehensive postmortem report using the template

Explain that this approach ensures completeness, blameless analysis, and actionable outcomes. Ask if they want to try this workflow or prefer to work freeform.

If user declines, work freeform. If user accepts, proceed to Stage 1.

## Stage 1: Information Gathering

**Goal:** Collect all relevant incident information to enable thorough analysis.

### Initial Questions

Start by asking for basic incident information:

1. What happened? (Brief description)
2. When did it occur? (Start time, end time, duration)
3. What was the severity level? (If unknown, help assess based on impact)
4. Which services/systems were affected?
5. How was the incident detected?
6. How was it resolved?

Inform them they can answer in shorthand or provide information however works best.

### Timeline Construction

Ask for a chronological sequence of events. Encourage them to provide:
- First detection/alert
- Investigation steps
- Mitigation attempts
- Key decisions made
- Resolution steps

**What to do:**
- Organize scattered information into a coherent timeline
- Identify gaps and ask clarifying questions
- Use role-based language (e.g., "the on-call engineer") not names
- Highlight key decisions and turning points

### Impact Assessment

Request impact metrics:
- User impact (affected users, error rates, feature degradation)
- Business impact (revenue, SLA breaches, customer complaints)
- Technical metrics (downtime, latency, throughput)

**What to do:**
- Quantify impact from provided data
- Structure metrics clearly
- Help identify what metrics might be missing

### Additional Information

Ask if they have:
- System logs, monitoring dashboards, or error reports
- Communication records (internal updates, customer notifications)
- Relevant code changes, configuration changes, or deployments
- Related incidents or similar past incidents

**If integrations are available** (e.g., monitoring tools, incident management systems), mention these can be used to pull in data directly.

**Exit condition:**
Sufficient information when you have a clear timeline, impact metrics, and resolution details. You should be able to understand what happened, when, and the consequences.

**Transition:**
Ask if there's any more information they want to provide, or if it's time to move on to analysis.

## Stage 2: Analysis & Root Cause

**Goal:** Identify root causes, contributing factors, and generate comprehensive action items.

### Root Cause Analysis

Analyze root causes using techniques from [references/root-cause-analysis.md](references/root-cause-analysis.md). Based on information provided in the conversation:

1. **Synthesize available information**: Review what the user has shared about the incident
2. **Apply 5 Whys**: Analyze the chain of "whys" from available information, ask targeted questions only when information is missing
3. **Build Causal Chain**: Construct symptom → immediate cause → contributing factor → root cause
4. **Apply Systems Thinking**: Consider technical, process, and organizational layers

**What to do:**
- Analyze root causes proactively from conversation context
- Present your analysis and ask for confirmation or clarification
- Only ask targeted questions about specific gaps, not the entire chain
- Help identify contributing factors beyond immediate cause
- Frame causes in terms of systems and processes, not individuals
- Suggest alternative explanations and "second stories"

**Blameless principles:**
- Always reframe individual actions in terms of system/process failures
- Use role-based language, not names
- Ask "why did the system allow this" not "why did this person do this"

If user provides information that blames individuals, automatically reframe it in blameless terms.

### Action Items Generation

Generate action items using guidelines from [references/action-items.md](references/action-items.md).

**What to do:**
- Generate actionable, specific, bounded action items
- Categorize by: investigate, mitigate, repair, detect, mitigate future, prevent
- Ensure comprehensive coverage across all categories
- Suggest owners and deadlines based on context (user can adjust)
- Prioritize actions that address root causes

**Action item quality:**
- **Actionable**: Phrase as a sentence starting with a verb
- **Specific**: Define scope narrowly
- **Bounded**: Indicate how to tell when it's finished

### Lessons Learned

Help identify:
- What went well during the incident response
- What could be improved
- Systemic improvements needed

**Exit condition:**
Root cause identified, action items generated across all categories, and lessons learned captured.

**Transition:**
Ask if they want to refine the analysis or action items, or if ready to generate the report.

## Stage 3: Report Generation

**Goal:** Create a comprehensive, well-structured postmortem report.

### Report Structure

Use the template in `templates/postmortem_template.md` as a starting point. The simplified template focuses on:

1. Issue Overview
2. Where It Went Wrong
3. Why It Went Wrong (Root Cause Analysis)
4. Impact
5. Resolution
6. Action Items
7. Pre-Release Checklist (for future release reviews)
8. Lessons Learned

### Drafting the Report

**If access to artifacts is available:**
Use `create_file` to create an artifact with the complete postmortem report.

**If no access to artifacts:**
Create a markdown file in the working directory (e.g., `postmortem-YYYY-MM-DD.md`).

Fill in all sections based on the information gathered and analysis completed. Ensure:
- Consistency and completeness
- Professional formatting
- Blameless language throughout
- Clear, actionable language

### Review and Refinement

After drafting, ask user to review the report. Request feedback on:
- Accuracy of information
- Completeness of analysis
- Quality of action items
- Clarity and tone

Use `str_replace` to make edits based on feedback. Never reprint the whole doc.

**Continue iterating** until user is satisfied.

### Final Checks

Before completion, review the entire document for:
- Flow and consistency
- Redundancy or contradictions
- Blameless language
- Actionable, specific action items
- Complete root cause analysis

**Exit condition:**
User is satisfied with the postmortem report and it's ready for sharing.

## Tips for Effective Guidance

**Tone:**
- Be direct and procedural
- Explain rationale briefly when it affects user behavior
- Don't try to "sell" the approach - just execute it

**Handling Deviations:**
- If user wants to skip a stage: Ask if they want to skip this and work freeform
- If user seems frustrated: Acknowledge and suggest ways to move faster
- Always give user agency to adjust the process

**Information Management:**
- Throughout, if information is missing, proactively ask
- Don't let gaps accumulate - address them as they come up
- Help organize scattered information as it's provided

**Quality over Speed:**
- Don't rush through stages
- Each iteration should make meaningful improvements
- The goal is a postmortem that actually helps prevent future incidents

## References

- **Root Cause Analysis**: See [references/root-cause-analysis.md](references/root-cause-analysis.md) for detailed techniques
- **Action Items**: See [references/action-items.md](references/action-items.md) for categories and guidelines
- **Template**: Use `templates/postmortem_template.md` when generating reports

## Keywords

postmortem, post-mortem, incident review, post-incident review, blameless postmortem, root cause analysis, incident analysis, outage analysis, incident report, 5 whys, action items, incident response, reliability, SRE
