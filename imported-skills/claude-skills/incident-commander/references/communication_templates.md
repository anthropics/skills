# Incident Communication Templates

## Overview

This document provides standardized communication templates for incident response. These templates ensure consistent, clear communication across different severity levels and stakeholder groups.

## Template Usage Guidelines

### General Principles
1. **Be Clear and Concise** - Use simple language, avoid jargon
2. **Be Factual** - Only state what is known, avoid speculation
3. **Be Timely** - Send updates at committed intervals
4. **Be Actionable** - Include next steps and expected timelines
5. **Be Accountable** - Include contact information for follow-up

### Template Selection
- Choose templates based on incident severity and audience
- Customize templates with specific incident details
- Always include next update time and contact information
- Escalate template types as severity increases

---

## SEV1 Templates

### Initial Alert - Internal Teams

**Subject:** 🚨 [SEV1] CRITICAL: {Service} Complete Outage - Immediate Response Required

```
CRITICAL INCIDENT ALERT - IMMEDIATE ATTENTION REQUIRED

Incident Summary:
- Service: {Service Name}
- Status: Complete Outage
- Start Time: {Timestamp}
- Customer Impact: {Impact Description}
- Estimated Affected Users: {Number/Percentage}

Immediate Actions Needed:
✓ Incident Commander: {Name} - ASSIGNED
✓ War Room: {Bridge/Chat Link} - JOIN NOW
✓ On-Call Response: {Team} - PAGED
⏳ Executive Notification: In progress
⏳ Status Page Update: Within 15 minutes

Current Situation:
{Brief description of what we know}

What We're Doing:
{Immediate response actions being taken}

Next Update: {Timestamp - 15 minutes from now}

Incident Commander: {Name}
Contact: {Phone/Slack}

THIS IS A CUSTOMER-IMPACTING INCIDENT REQUIRING IMMEDIATE ATTENTION
```

### Executive Notification - SEV1

**Subject:** 🚨 URGENT: Customer-Impacting Outage - {Service}

```
EXECUTIVE ALERT: Critical customer-facing incident

Service: {Service Name}
Impact: {Customer impact description}
Duration: {Current duration} (started {start time})
Business Impact: {Revenue/SLA/compliance implications}

Customer Impact Summary:
- Affected Users: {Number/percentage}
- Revenue Impact: {$ amount if known}
- SLA Status: {Breach status}
- Customer Escalations: {Number if any}

Response Status:
- Incident Commander: {Name} ({contact})
- Response Team Size: {Number of engineers}
- Root Cause: {If known, otherwise "Under investigation"}
- ETA to Resolution: {If known, otherwise "Investigating"}

Executive Actions Required:
- [ ] Customer communication approval needed
- [ ] Legal/compliance notification: {If applicable}
- [ ] PR/Media response preparation: {If needed}
- [ ] Resource allocation decisions: {If escalation needed}

War Room: {Link}
Next Update: {15 minutes from now}

This incident meets SEV1 criteria and requires executive oversight.

{Incident Commander contact information}
```

### Customer Communication - SEV1

**Subject:** Service Disruption - Immediate Action Being Taken

```
We are currently experiencing a service disruption affecting {service description}.

What's Happening:
{Clear, customer-friendly description of the issue}

Impact:
{What customers are experiencing - be specific}

What We're Doing:
We detected this issue at {time} and immediately mobilized our engineering team. We are actively working to resolve this issue and will provide updates every 15 minutes.

Current Actions:
• {Action 1 - customer-friendly description}
• {Action 2 - customer-friendly description}
• {Action 3 - customer-friendly description}

Workaround:
{If available, provide clear steps}
{If not available: "We are working on alternative solutions and will share them as soon as available."}

Next Update: {Timestamp}
Status Page: {Link}
Support: {Contact information if different from usual}

We sincerely apologize for the inconvenience and are committed to resolving this as quickly as possible.

{Company Name} Team
```

### Status Page Update - SEV1

**Status:** Major Outage

```
{Timestamp} - Investigating

We are currently investigating reports of {service} being unavailable. Our team has been alerted and is actively investigating the cause.

Affected Services: {List of affected services}
Impact: {Customer-facing impact description}

We will provide an update within 15 minutes.
```

```
{Timestamp} - Identified

We have identified the cause of the {service} outage. Our engineering team is implementing a fix.

Root Cause: {Brief, customer-friendly explanation}
Expected Resolution: {Timeline if known}

Next update in 15 minutes.
```

```
{Timestamp} - Monitoring

The fix has been implemented and we are monitoring the service recovery. 

Current Status: {Recovery progress}
Next Steps: {What we're monitoring}

We expect full service restoration within {timeframe}.
```

```
{Timestamp} - Resolved

{Service} is now fully operational. We have confirmed that all functionality is working as expected.

Total Duration: {Duration}
Root Cause: {Brief summary}

We apologize for the inconvenience. A full post-incident review will be conducted and shared within 24 hours.
```

---

## SEV2 Templates

### Team Notification - SEV2

**Subject:** ⚠️ [SEV2] {Service} Performance Issues - Response Team Mobilizing

```
SEV2 INCIDENT: Performance degradation requiring active response

Incident Details:
- Service: {Service Name}
- Issue: {Description of performance issue}
- Start Time: {Timestamp}
- Affected Users: {Percentage/description}
- Business Impact: {Impact on business operations}

Current Status:
{What we know about the issue}

Response Team:
- Incident Commander: {Name} ({contact})
- Primary Responder: {Name} ({team})
- Supporting Teams: {List of engaged teams}

Immediate Actions:
✓ {Action 1 - completed}
⏳ {Action 2 - in progress}
⏳ {Action 3 - next step}

Metrics:
- Error Rate: {Current vs normal}
- Response Time: {Current vs normal}  
- Throughput: {Current vs normal}

Communication Plan:
- Internal Updates: Every 30 minutes
- Stakeholder Notification: {If needed}
- Status Page Update: {Planned/not needed}

Coordination Channel: {Slack channel}
Next Update: {30 minutes from now}

Incident Commander: {Name} | {Contact}
```

### Stakeholder Update - SEV2

**Subject:** [SEV2] Service Performance Update - {Service}

```
Service Performance Incident Update

Service: {Service Name}
Duration: {Current duration}
Impact: {Description of user impact}

Current Status:
{Brief status of the incident and response efforts}

What We Know:
• {Key finding 1}
• {Key finding 2}
• {Key finding 3}

What We're Doing:
• {Response action 1}
• {Response action 2}
• {Monitoring/verification steps}

Customer Impact:
{Realistic assessment of what users are experiencing}

Workaround:
{If available, provide steps}

Expected Resolution:
{Timeline if known, otherwise "Continuing investigation"}

Next Update: {30 minutes}
Contact: {Incident Commander information}

This incident is being actively managed and does not currently require escalation.
```

### Customer Communication - SEV2 (Optional)

**Subject:** Temporary Service Performance Issues

```
We are currently experiencing performance issues with {service name} that may affect your experience.

What You Might Notice:
{Specific symptoms users might experience}

What We're Doing:
Our team identified this issue at {time} and is actively working on a resolution. We expect to have this resolved within {timeframe}.

Workaround:
{If applicable, provide simple workaround steps}

We will update our status page at {link} with progress information.

Thank you for your patience as we work to resolve this issue quickly.

{Company Name} Support Team
```

---

## SEV3 Templates

### Team Assignment - SEV3

**Subject:** [SEV3] Issue Assignment - {Component} Issue

```
SEV3 Issue Assignment

Service/Component: {Affected component}
Issue: {Description}
Reported: {Timestamp}
Reporter: {Person/system that reported}

Issue Details:
{Detailed description of the problem}

Impact Assessment:
- Affected Users: {Scope}
- Business Impact: {Assessment}
- Urgency: {Business hours response appropriate}

Assignment:
- Primary: {Engineer name}
- Team: {Responsible team}
- Expected Response: {Within 2-4 hours}

Investigation Plan:
1. {Investigation step 1}
2. {Investigation step 2}
3. {Communication checkpoint}

Workaround:
{If known, otherwise "Investigating alternatives"}

This issue will be tracked in {ticket system} as {ticket number}.

Team Lead: {Name} | {Contact}
```

### Status Update - SEV3

**Subject:** [SEV3] Progress Update - {Component}

```
SEV3 Issue Progress Update

Issue: {Brief description}
Assigned to: {Engineer/Team}
Investigation Status: {Current progress}

Findings So Far:
{What has been discovered during investigation}

Next Steps:
{Planned actions and timeline}

Impact Update:
{Any changes to scope or urgency}

Expected Resolution:
{Timeline if known}

This issue continues to be tracked as SEV3 with no escalation required.

Contact: {Assigned engineer} | {Team lead}
```

---

## SEV4 Templates

### Issue Documentation - SEV4

**Subject:** [SEV4] Issue Documented - {Description}

```
SEV4 Issue Logged

Description: {Clear description of the issue}
Reporter: {Name/system}
Date: {Date reported}

Impact:
{Minimal impact description}

Priority Assessment:
This issue has been classified as SEV4 and will be addressed in the normal development cycle.

Assignment:
- Team: {Responsible team}
- Sprint: {Target sprint}
- Estimated Effort: {Story points/hours}

This issue is tracked as {ticket number} in {system}.

Product Owner: {Name}
```

---

## Escalation Templates

### Severity Escalation

**Subject:** ESCALATION: {Original Severity} → {New Severity} - {Service}

```
SEVERITY ESCALATION NOTIFICATION

Original Classification: {Original severity}
New Classification: {New severity}  
Escalation Time: {Timestamp}
Escalated By: {Name and role}

Escalation Reasons:
• {Reason 1 - scope expansion/duration/impact}
• {Reason 2}
• {Reason 3}

Updated Impact:
{New assessment of customer/business impact}

Updated Response Requirements:
{New response team, communication frequency, etc.}

Previous Response Actions:
{Summary of actions taken under previous severity}

New Incident Commander: {If changed}
Updated Communication Plan: {New frequency/recipients}

All stakeholders should adjust response according to {new severity} protocols.

Incident Commander: {Name} | {Contact}
```

### Management Escalation

**Subject:** MANAGEMENT ESCALATION: Extended {Severity} Incident - {Service}

```
Management Escalation Required

Incident: {Service} {brief description}
Original Severity: {Severity}
Duration: {Current duration}
Escalation Trigger: {Duration threshold/scope change/customer escalation}

Current Status:
{Brief status of incident response}

Challenges Encountered:
• {Challenge 1}
• {Challenge 2}
• {Resource/expertise needs}

Business Impact:
{Updated assessment of business implications}

Management Decision Required:
• {Decision 1 - resource allocation/external expertise/communication}
• {Decision 2}

Recommended Actions:
{Incident Commander's recommendations}

This escalation follows standard procedures for {trigger type}.

Incident Commander: {Name}
Contact: {Phone/Slack}
War Room: {Link}
```

---

## Resolution Templates

### Resolution Confirmation - All Severities

**Subject:** RESOLVED: [{Severity}] {Service} Incident - {Brief Description}

```
INCIDENT RESOLVED

Service: {Service Name}
Issue: {Brief description}
Duration: {Total duration}
Resolution Time: {Timestamp}

Resolution Summary:
{Brief description of how the issue was resolved}

Root Cause:
{Brief explanation - detailed PIR to follow}

Impact Summary:
- Users Affected: {Final count/percentage}
- Business Impact: {Final assessment}
- Services Affected: {List}

Resolution Actions Taken:
• {Action 1}
• {Action 2}
• {Verification steps}

Monitoring:
We will continue monitoring {service} for {duration} to ensure stability.

Next Steps:
• Post-incident review scheduled for {date}
• Action items to be tracked in {system}
• Follow-up communication: {If needed}

Thank you to everyone who participated in the incident response.

Incident Commander: {Name}
```

### Customer Resolution Communication

**Subject:** Service Restored - Thank You for Your Patience

```
Service Update: Issue Resolved

We're pleased to report that the {service} issues have been fully resolved as of {timestamp}.

What Was Fixed:
{Customer-friendly explanation of the resolution}

Duration:
The issue lasted {duration} from {start time} to {end time}.

What We Learned:
{Brief, high-level takeaway}

Our Commitment:
We are conducting a thorough review of this incident and will implement improvements to prevent similar issues in the future. A summary of our findings and improvements will be shared {timeframe}.

We sincerely apologize for any inconvenience this may have caused and appreciate your patience while we worked to resolve the issue.

If you continue to experience any problems, please contact our support team at {contact information}.

Thank you,
{Company Name} Team
```

---

## Template Customization Guidelines

### Placeholders to Always Replace
- `{Service}` / `{Service Name}` - Specific service or component
- `{Timestamp}` - Specific date/time in consistent format
- `{Name}` / `{Contact}` - Actual names and contact information
- `{Duration}` - Actual time durations
- `{Link}` - Real URLs to war rooms, status pages, etc.

### Language Guidelines
- Use active voice ("We are investigating" not "The issue is being investigated")
- Be specific about timelines ("within 30 minutes" not "soon")
- Avoid technical jargon in customer communications
- Include empathy in customer-facing messages
- Use consistent terminology throughout incident lifecycle

### Timing Guidelines
| Severity | Initial Notification | Update Frequency | Resolution Notification |
|----------|---------------------|------------------|------------------------|
| SEV1 | Immediate (< 5 min) | Every 15 minutes | Immediate |
| SEV2 | Within 15 minutes | Every 30 minutes | Within 15 minutes |
| SEV3 | Within 2 hours | At milestones | Within 1 hour |
| SEV4 | Within 1 business day | Weekly | When resolved |

### Audience-Specific Considerations

#### Engineering Teams
- Include technical details
- Provide specific metrics and logs
- Include coordination channels
- List specific actions and owners

#### Executive/Business
- Focus on business impact
- Include customer and revenue implications
- Provide clear timeline and resource needs
- Highlight any external factors (PR, legal, compliance)

#### Customers
- Use plain language
- Focus on customer impact and workarounds
- Provide realistic timelines
- Include support contact information
- Show empathy and accountability

---

**Last Updated:** February 2026  
**Next Review:** May 2026  
**Owner:** Incident Management Team