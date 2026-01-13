---
name: postmortems
description: Guide for creating comprehensive, blameless incident postmortems that help teams learn from incidents, identify root causes, and prevent future occurrences. Use when conducting post-incident reviews, writing postmortem reports, or analyzing incidents to improve system reliability.
license: Complete terms in LICENSE.txt
---

# Incident Postmortems

A comprehensive guide for creating effective, blameless postmortems through human-AI collaboration. This skill helps you analyze incidents, identify root causes, and generate actionable postmortem reports.

## When to use this skill

Use this skill when:
- Conducting post-incident reviews after system outages or incidents
- Writing postmortem reports for incidents with severity level 2 or higher
- Analyzing incidents to identify root causes and preventive measures
- Creating action items to mitigate and prevent future incidents
- Documenting incident timelines and impact
- Synthesizing information from multiple sources into a structured postmortem

## Overview

A postmortem is a written record of an incident that describes:
- The incident's impact
- The actions taken to mitigate or resolve the incident
- The incident's root cause
- Follow-up actions to prevent the incident from recurring

Postmortems should be **blameless** - focusing on systems, processes, and roles rather than individuals. This creates a culture of learning and continuous improvement.

## How This Skill Works: Human-AI Collaboration

This skill enables a collaborative workflow where:
- **You provide**: Incident information, context, data, and decisions
- **AI helps**: Analyze, structure, synthesize, generate insights, and create comprehensive reports

The AI will guide you through gathering information, help you think through root causes, generate well-structured action items, and produce a complete postmortem report.

## Postmortem Workflow

### Step 1: Determine If a Postmortem Is Needed

**When to create a postmortem:**
- Any incident with severity level 1 or 2 (critical or high)
- Incidents that caused significant user impact
- Incidents that exposed systemic issues
- Incidents that required escalation or major remediation efforts

**What the AI will do:**
- Help you assess if an incident warrants a postmortem
- Suggest appropriate severity levels based on impact
- Identify if systemic issues were exposed

**What you provide:**
- Basic incident information (severity, duration, affected services)

### Step 2: Gather Incident Information

**What you should provide:**

The AI will help you collect and organize information from various sources:

**Essential information:**
- Chronological sequence of events (timeline)
- What was detected and when
- Actions taken during the incident
- How the incident was resolved
- Impact metrics (users affected, error rates, downtime)

**Helpful additional information:**
- System logs, monitoring dashboards, or error reports
- Communication records (internal updates, customer notifications)
- Decisions made during the incident and rationale
- Relevant code changes, configuration changes, or deployments
- Related incidents or similar past incidents

**What the AI will do:**
- Help you identify what information might be missing
- Organize scattered information into a coherent structure
- Ask clarifying questions to fill gaps
- Synthesize information from multiple sources
- Create a structured timeline from raw data

**How to provide information:**
- Share information as you have it (logs, screenshots, notes, etc.)
- Describe events in chronological order or as they come to mind
- The AI will help organize and structure it
- You can provide information incrementally - the AI will help piece it together

### Step 3: Analyze and Structure the Information

**What the AI will do:**

1. **Timeline Construction**
   - Build a chronological timeline from the information you provide
   - Identify gaps and ask clarifying questions
   - Organize events into: detection → investigation → mitigation attempts → resolution
   - Use role-based language (e.g., "the on-call engineer") not names
   - Highlight key decisions and turning points

2. **Impact Assessment**
   - Quantify user impact from the metrics you provide
   - Calculate business impact if data is available
   - Structure technical metrics clearly
   - Help identify what metrics might be missing

3. **Root Cause Analysis**
   - Guide you through "5 Whys" analysis interactively
   - Help identify contributing factors beyond the immediate cause
   - Consider multiple layers: technical, process, organizational
   - Frame causes in terms of systems and processes, not individuals
   - Suggest alternative explanations and "second stories"

4. **Action Items Generation**
   - Generate actionable, specific, bounded action items
   - Categorize by: investigate, mitigate, repair, detect, mitigate future, prevent
   - Help prioritize actions that address root causes
   - Suggest owners and deadlines based on context (you can adjust)
   - Ensure comprehensive coverage across all categories

5. **Lessons Learned**
   - Help identify what went well
   - Surface what could be improved
   - Identify systemic improvements needed

**What you do:**
- Provide information and context
- Answer clarifying questions
- Review and refine the AI's analysis
- Validate root cause analysis
- Adjust action items as needed

### Step 4: Generate the Postmortem Report

**What the AI will do:**
- Use the template in `templates/postmortem_template.md` as a starting point
- Generate a complete, well-structured postmortem report
- Fill in all sections based on the information and analysis
- Ensure consistency and completeness
- Format the report professionally

**What you do:**
- Review the generated report
- Provide feedback and corrections
- Add any missing information
- Refine language and tone as needed
- Approve the final version

**Report structure:**
1. Executive Summary
2. Incident Details
3. Impact (User, Business, Technical)
4. Timeline
5. Root Cause Analysis
6. Resolution
7. Action Items (categorized)
8. Lessons Learned
9. Appendices

## Blameless Postmortem Principles

**Core principles the AI will follow:**
- Assume good intentions on the part of all staff
- Never blame people for faults
- Focus on systems, processes, and roles, not individuals
- Ask "why did the system allow this" not "why did this person do this"

**How the AI applies these:**
- Reframe individual actions in terms of system/process failures
- Use role-based language (e.g., "the on-call engineer") not names
- Frame timeline, causal chain, and mitigations in context of systems and processes
- Suggest "second stories" - alternative explanations that focus on systemic factors

**Example reframing the AI will do:**
- ❌ "John deployed the buggy code"
- ✅ "The deployment process allowed code without sufficient tests to reach production"

If you provide information that blames individuals, the AI will help reframe it in blameless terms.

## Root Cause Analysis Techniques

The AI will guide you through these techniques:

### 5 Whys

The AI will help you dig deeper by asking "why" iteratively:

**Example interaction:**
- You: "The service failed"
- AI: "Why did the service fail?"
- You: "Database connection timeout"
- AI: "Why did the connection timeout?"
- You: "Connection pool exhausted"
- AI: "Why was the pool exhausted?"
- ... (continues until root cause)

### Causal Chain

The AI will help you build a chain of causation:
```
Symptom → Immediate Cause → Contributing Factor → Root Cause
```

### Systems Thinking

The AI will help you consider multiple layers:
- **Technical**: Code, infrastructure, configuration
- **Process**: Deployment, monitoring, on-call procedures
- **Organizational**: Training, documentation, communication

The AI will prompt you to think about each layer and identify gaps.

## Action Item Categories

The AI will generate action items across these categories to ensure comprehensive coverage:

| Category | What the AI Asks | Examples the AI Might Generate |
|----------|-----------------|-------------------------------|
| **Investigate this incident** | "What happened to cause this incident and why?" | "Analyze logs from [timeframe] to identify all error patterns" |
| **Mitigate this incident** | "What immediate actions did we take to resolve this specific event?" | "Roll back deployment v1.2.3 to v1.2.2" |
| **Repair damage from this incident** | "How did we resolve immediate or collateral damage?" | "Restore corrupted user data from backup timestamped [date]" |
| **Detect future incidents** | "How can we decrease time to accurately detect similar failures?" | "Add alerting for all cases where this service returns >1% errors" |
| **Mitigate future incidents** | "How can we decrease severity/duration of future incidents like this?" | "Implement graceful degradation when database connections exceed 80% capacity" |
| **Prevent future incidents** | "How can we prevent a recurrence of this sort of failure?" | "Add automated pre-submit check for schema changes" |

**Action item quality:**
The AI will ensure each action item is:
- **Actionable**: Phrase as a sentence starting with a verb
- **Specific**: Define scope narrowly
- **Bounded**: Indicate how to tell when it's finished

**Example improvements the AI will make:**
- ❌ "Investigate monitoring for this scenario"
- ✅ "Add alerting for all cases where this service returns >1% errors"

## Third-Party Dependencies

When incidents involve third-party services, the AI will help you work through this framework:

1. **Did the 3rd party violate our expectations?**
   - Help review and assess their RCA
   - Suggest adjusting expectations and increasing resilience
   - Identify alternative solutions if expectations are unacceptable

2. **Did the 3rd party meet expectations, but our service failed anyway?**
   - Help identify where our service needs to increase resilience
   - Suggest specific resilience improvements

3. **Do we not have clear expectations?**
   - Help establish expectations with the 3rd party
   - Suggest how to share expectations with teams

## Interactive Workflow Examples

### Example 1: Starting from Scratch

**You:** "I need to write a postmortem for an incident that happened yesterday. The database went down for 2 hours."

**AI (using this skill):**
- Asks about severity and impact
- Requests timeline information
- Helps gather details incrementally
- Structures the information as you provide it
- Guides root cause analysis
- Generates action items
- Creates the full report

### Example 2: You Have Some Information

**You:** "Here's our incident timeline and some logs. Can you help me create a postmortem?"

**AI (using this skill):**
- Analyzes the provided information
- Identifies gaps and asks clarifying questions
- Helps structure the timeline
- Guides root cause analysis
- Generates comprehensive action items
- Creates the report

### Example 3: Refining an Existing Draft

**You:** "I have a rough postmortem draft. Can you help improve it?"

**AI (using this skill):**
- Reviews the draft
- Identifies missing sections or information
- Suggests improvements to root cause analysis
- Helps refine action items
- Ensures blameless language
- Polishes the final report

## Best Practices for Using This Skill

### Do's

✅ **Do** provide information incrementally - the AI can help organize it as you go
✅ **Do** share raw data (logs, metrics, screenshots) - the AI can help extract insights
✅ **Do** answer clarifying questions - they help the AI create a better analysis
✅ **Do** review and refine the AI's suggestions - your domain knowledge is crucial
✅ **Do** provide context about your systems and processes - it helps the AI generate better action items
✅ **Do** use the template structure - it ensures completeness
✅ **Do** focus on systems and processes in your input - the AI will help maintain blameless language
✅ **Do** quantify impact with metrics when possible - the AI can help structure them

### Don'ts

❌ **Don't** blame individuals in your input - the AI will help reframe, but it's better to start blameless
❌ **Don't** skip root cause analysis - the AI will guide you through it
❌ **Don't** create vague action items - the AI will help make them specific and actionable
❌ **Don't** focus only on technical causes - the AI will prompt you to consider process and organizational factors
❌ **Don't** rush through the analysis - take time to work through the 5 Whys with the AI
❌ **Don't** skip the "what went well" section - the AI will help identify positive learnings

## Templates

The AI will use the template in `templates/postmortem_template.md` when generating reports. The template includes:
- All required sections
- Example content structure for each section
- Guidance on what to include
- Formatting guidelines

You can ask the AI to customize the template structure if your organization has specific requirements.

## Keywords

postmortem, post-mortem, incident review, post-incident review, blameless postmortem, root cause analysis, incident analysis, outage analysis, incident report, 5 whys, action items, incident response, reliability, SRE
