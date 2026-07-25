# Incident Severity Classification Matrix

## Overview

This document defines the severity classification system used for incident response. The classification determines response requirements, escalation paths, and communication frequency.

## Severity Levels

### SEV1 - Critical Outage

**Definition:** Complete service failure affecting all users or critical business functions

#### Impact Criteria
- Customer-facing services completely unavailable
- Data loss or corruption affecting users
- Security breaches with customer data exposure
- Revenue-generating systems down
- SLA violations with financial penalties
- > 75% of users affected

#### Response Requirements
| Metric | Requirement |
|--------|-------------|
| **Response Time** | Immediate (0-5 minutes) |
| **Incident Commander** | Assigned within 5 minutes |
| **War Room** | Established within 10 minutes |
| **Executive Notification** | Within 15 minutes |
| **Public Status Page** | Updated within 15 minutes |
| **Customer Communication** | Within 30 minutes |

#### Escalation Path
1. **Immediate**: On-call Engineer → Incident Commander
2. **15 minutes**: VP Engineering + Customer Success VP
3. **30 minutes**: CTO
4. **60 minutes**: CEO + Full Executive Team

#### Communication Requirements
- **Frequency**: Every 15 minutes until resolution
- **Channels**: PagerDuty, Phone, Slack, Email, Status Page
- **Recipients**: All engineering, executives, customer success
- **Template**: SEV1 Executive Alert Template

---

### SEV2 - Major Impact

**Definition:** Significant degradation affecting subset of users or non-critical functions

#### Impact Criteria
- Partial service degradation (25-75% of users affected)
- Performance issues causing user frustration
- Non-critical features unavailable
- Internal tools impacting productivity
- Data inconsistencies not affecting user experience
- API errors affecting integrations

#### Response Requirements
| Metric | Requirement |
|--------|-------------|
| **Response Time** | 15 minutes |
| **Incident Commander** | Assigned within 30 minutes |
| **Status Page Update** | Within 30 minutes |
| **Stakeholder Notification** | Within 1 hour |
| **Team Assembly** | Within 30 minutes |

#### Escalation Path
1. **Immediate**: On-call Engineer → Team Lead
2. **30 minutes**: Engineering Manager
3. **2 hours**: VP Engineering
4. **4 hours**: CTO (if unresolved)

#### Communication Requirements
- **Frequency**: Every 30 minutes during active response
- **Channels**: PagerDuty, Slack, Email
- **Recipients**: Engineering team, product team, relevant stakeholders
- **Template**: SEV2 Major Impact Template

---

### SEV3 - Minor Impact

**Definition:** Limited impact with workarounds available

#### Impact Criteria
- Single feature or component affected
- < 25% of users impacted
- Workarounds available
- Performance degradation not significantly impacting UX
- Non-urgent monitoring alerts
- Development/test environment issues

#### Response Requirements
| Metric | Requirement |
|--------|-------------|
| **Response Time** | 2 hours (business hours) |
| **After Hours Response** | Next business day |
| **Team Assignment** | Within 4 hours |
| **Status Page Update** | Optional |
| **Internal Notification** | Within 2 hours |

#### Escalation Path
1. **Immediate**: Assigned Engineer
2. **4 hours**: Team Lead
3. **1 business day**: Engineering Manager (if needed)

#### Communication Requirements
- **Frequency**: At key milestones only
- **Channels**: Slack, Email
- **Recipients**: Assigned team, team lead
- **Template**: SEV3 Minor Impact Template

---

### SEV4 - Low Impact

**Definition:** Minimal impact, cosmetic issues, or planned maintenance

#### Impact Criteria
- Cosmetic bugs
- Documentation issues
- Logging or monitoring gaps
- Performance issues with no user impact
- Development/test environment issues
- Feature requests or enhancements

#### Response Requirements
| Metric | Requirement |
|--------|-------------|
| **Response Time** | 1-2 business days |
| **Assignment** | Next sprint planning |
| **Tracking** | Standard ticket system |
| **Escalation** | None required |

#### Communication Requirements
- **Frequency**: Standard development cycle updates
- **Channels**: Ticket system
- **Recipients**: Product owner, assigned developer
- **Template**: Standard issue template

## Classification Guidelines

### User Impact Assessment

| Impact Scope | Description | Typical Severity |
|--------------|-------------|------------------|
| **All Users** | 100% of users affected | SEV1 |
| **Major Subset** | 50-75% of users affected | SEV1/SEV2 |
| **Significant Subset** | 25-50% of users affected | SEV2 |
| **Limited Users** | 5-25% of users affected | SEV2/SEV3 |
| **Few Users** | < 5% of users affected | SEV3/SEV4 |
| **No User Impact** | Internal only | SEV4 |

### Business Impact Assessment

| Business Impact | Description | Severity Boost |
|-----------------|-------------|----------------|
| **Revenue Loss** | Direct revenue impact | +1 severity level |
| **SLA Breach** | Contract violations | +1 severity level |
| **Regulatory** | Compliance implications | +1 severity level |
| **Brand Damage** | Public-facing issues | +1 severity level |
| **Security** | Data or system security | +2 severity levels |

### Duration Considerations

| Duration | Impact on Classification |
|----------|--------------------------|
| **< 15 minutes** | May reduce severity by 1 level |
| **15-60 minutes** | Standard classification |
| **1-4 hours** | May increase severity by 1 level |
| **> 4 hours** | Significant severity increase |

## Decision Tree

```
1. Is this a security incident with data exposure?
   → YES: SEV1 (regardless of user count)
   → NO: Continue to step 2

2. Are revenue-generating services completely down?
   → YES: SEV1
   → NO: Continue to step 3

3. What percentage of users are affected?
   → > 75%: SEV1
   → 25-75%: SEV2
   → 5-25%: SEV3
   → < 5%: SEV4

4. Apply business impact modifiers
5. Consider duration factors
6. When in doubt, err on higher severity
```

## Examples

### SEV1 Examples
- Payment processing system completely down
- All user authentication failing
- Database corruption causing data loss
- Security breach with customer data exposed
- Website returning 500 errors for all users

### SEV2 Examples
- Payment processing slow (30-second delays)
- Search functionality returning incomplete results
- API rate limits causing partner integration issues
- Dashboard displaying stale data (> 1 hour old)
- Mobile app crashing for 40% of users

### SEV3 Examples
- Single feature in admin panel not working
- Email notifications delayed by 1 hour
- Non-critical API endpoint returning errors
- Cosmetic UI bug in settings page
- Development environment deployment failing

### SEV4 Examples
- Typo in help documentation
- Log format change needed for analysis
- Non-critical performance optimization
- Internal tool enhancement request
- Test data cleanup needed

## Escalation Triggers

### Automatic Escalation
- SEV1 incidents automatically escalate every 30 minutes if unresolved
- SEV2 incidents escalate after 2 hours without significant progress
- Any incident with expanding scope increases severity
- Customer escalation to support triggers severity review

### Manual Escalation
- Incident Commander can escalate at any time
- Technical leads can request escalation
- Business stakeholders can request severity review
- External factors (media attention, regulatory) trigger escalation

## Communication Templates

### SEV1 Executive Alert
```
Subject: 🚨 CRITICAL INCIDENT - [Service] Complete Outage

URGENT: Customer-facing service outage requiring immediate attention

Service: [Service Name]
Start Time: [Timestamp]
Impact: [Description of customer impact]
Estimated Affected Users: [Number/Percentage]
Business Impact: [Revenue/SLA/Brand implications]

Incident Commander: [Name] ([Contact])
Response Team: [Team members engaged]

Current Status: [Brief status update]
Next Update: [Timestamp - 15 minutes from now]
War Room: [Bridge/Chat link]

This is a customer-impacting incident requiring executive awareness.
```

### SEV2 Major Impact
```
Subject: ⚠️ [SEV2] [Service] - Major Performance Impact

Major service degradation affecting user experience

Service: [Service Name]
Start Time: [Timestamp] 
Impact: [Description of user impact]
Scope: [Affected functionality/users]

Response Team: [Team Lead] + [Team members]
Status: [Current mitigation efforts]
Workaround: [If available]

Next Update: 30 minutes
Status Page: [Link if updated]
```

## Review and Updates

This severity matrix should be reviewed quarterly and updated based on:
- Incident response learnings
- Business priority changes
- Service architecture evolution
- Regulatory requirement changes
- Customer feedback and SLA updates

**Last Updated:** February 2026  
**Next Review:** May 2026  
**Owner:** Engineering Leadership