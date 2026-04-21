# Incident Communication Templates

## Initial Alert (Internal)

```
🚨 SECURITY INCIDENT - [SEVERITY]

Time Detected: [TIMESTAMP UTC]
Type: [Brief description]
Impact: [Estimated scope]
Status: [Investigating/Contained/Resolved]

Incident Commander: [Name]
War Room: [Link/Channel]

DO NOT discuss externally until cleared.
```

## First Public Statement (After Containment)

```
Security Notice

We are aware of [brief description of issue] affecting [scope].

What happened:
- [Factual, confirmed information only]

What we're doing:
- [Immediate actions taken]
- [Investigation status]

What you should do:
- [Specific user actions if needed]
- [Where to get updates]

We will provide updates as we learn more.
```

## Progress Update

```
Security Update - [Date/Time] UTC

Current Status: [Investigating/Contained/Resolved]

Since our last update:
- [New confirmed information]
- [Actions taken]

Next steps:
- [What's being worked on]

Estimated next update: [Timeframe]
```

## Incident Resolved Statement

```
Security Incident Resolution

The security incident reported on [date] has been resolved.

Summary:
- [What happened]
- [Root cause]
- [Impact - be specific about affected users/funds]

Actions Taken:
- [Immediate fixes]
- [Long-term improvements]
- [User remediation if applicable]

Lessons Learned:
- [Brief, without exposing vulnerabilities]

We apologize for any inconvenience and thank the community for their patience.

Full post-mortem: [Link when available]
```

## Post-Mortem Report Structure

```markdown
# Incident Post-Mortem: [Title]

**Date**: [Incident date]
**Duration**: [Start to resolution]
**Severity**: [Critical/High/Medium/Low]
**Author**: [Team/Individual]

## Executive Summary
[2-3 sentences summarizing what happened and impact]

## Timeline
- [Timestamp]: [Event]
- [Timestamp]: [Event]
...

## Root Cause
[Technical explanation of vulnerability/failure]

## Impact
- Users affected: [Number]
- Funds at risk: [Amount]
- Funds lost: [Amount]
- Services disrupted: [List]

## Response
[What actions were taken and when]

## Resolution
[How the issue was fixed]

## Lessons Learned
1. [Learning point]
2. [Learning point]

## Action Items
- [ ] [Preventive measure] - Owner: [Name] - Due: [Date]
- [ ] [Process improvement] - Owner: [Name] - Due: [Date]
```

## User Notification (If Funds Lost)

```
Important Notice Regarding Your Account

We regret to inform you that your account was affected by the security incident on [date].

Impact to your account:
- [Specific details]

What we're doing:
- [Compensation plan if applicable]
- [Timeline]

What you should do:
- [Required actions]
- [Support contact]

We sincerely apologize for this incident. [Contact info for questions]
```
