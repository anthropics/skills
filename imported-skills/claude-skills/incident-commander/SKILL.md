---
name: "incident-commander"
description: "Comprehensive incident response framework from detection through resolution and post-incident review. Battle-tested SRE/DevOps practices: severity classification, timeline reconstruction, structured post-incident analysis. Use when declaring an incident, coordinating multi-team response during an outage, leading a post-mortem, or setting up on-call practices for a new service."
---

# Incident Commander Skill

**Category:** Engineering Team  
**Tier:** POWERFUL  
**Author:** Claude Skills Team  
**Version:** 1.0.0  
**Last Updated:** February 2026

## Overview

Incident response framework for **availability/reliability incidents** (outages, degradations, failed deploys): severity classification, timeline reconstruction, and post-incident review.

**This is NOT security incident triage.** For security events (ransomware, intrusion, data exfiltration, IOC analysis, NIST SP 800-61 forensics), route to `incident-response`. Both skills use SEV1-SEV4 labels; this one scores operational impact (users, revenue, SLA), while `incident-response` classifies attack types and forensic handling.

## Key Features

- **Automated Severity Classification** - Intelligent incident triage based on impact and urgency metrics
- **Timeline Reconstruction** - Transform scattered logs and events into coherent incident narratives
- **Post-Incident Review Generation** - Structured PIRs with multiple RCA frameworks
- **Communication Templates** - Pre-built templates for stakeholder updates and escalations
- **Runbook Integration** - Generate actionable runbooks from incident patterns

## Skills Included

### Core Tools

1. **Incident Classifier** (`incident_classifier.py`)
   - Analyzes incident descriptions and outputs severity levels
   - Recommends response teams and initial actions
   - Generates communication templates based on severity

2. **Timeline Reconstructor** (`timeline_reconstructor.py`)
   - Processes timestamped events from multiple sources
   - Reconstructs chronological incident timeline
   - Identifies gaps and provides duration analysis

3. **PIR Generator** (`pir_generator.py`)
   - Creates comprehensive Post-Incident Review documents
   - Applies multiple RCA frameworks (5 Whys, Fishbone, Timeline)
   - Generates actionable follow-up items

## Incident Response Framework

### Severity Classification System

#### SEV1 - Critical Outage
**Definition:** Complete service failure affecting all users or critical business functions

**Characteristics:**
- Customer-facing services completely unavailable
- Data loss or corruption affecting users
- Security breaches with customer data exposure
- Revenue-generating systems down
- SLA violations with financial penalties

**Response Requirements:**
- Immediate escalation to on-call engineer
- Incident Commander assigned within 5 minutes
- Executive notification within 15 minutes
- Public status page update within 15 minutes
- War room established
- All hands on deck if needed

**Communication Frequency:** Every 15 minutes until resolution

#### SEV2 - Major Impact
**Definition:** Significant degradation affecting subset of users or non-critical functions

**Characteristics:**
- Partial service degradation (>25% of users affected)
- Performance issues causing user frustration
- Non-critical features unavailable
- Internal tools impacting productivity
- Data inconsistencies not affecting user experience

**Response Requirements:**
- On-call engineer response within 15 minutes
- Incident Commander assigned within 30 minutes
- Status page update within 30 minutes
- Stakeholder notification within 1 hour
- Regular team updates

**Communication Frequency:** Every 30 minutes during active response

#### SEV3 - Minor Impact
**Definition:** Limited impact with workarounds available

**Characteristics:**
- Single feature or component affected
- <25% of users impacted
- Workarounds available
- Performance degradation not significantly impacting UX
- Non-urgent monitoring alerts

**Response Requirements:**
- Response within 2 hours during business hours
- Next business day response acceptable outside hours
- Internal team notification
- Optional status page update

**Communication Frequency:** At key milestones only

#### SEV4 - Low Impact
**Definition:** Minimal impact, cosmetic issues, or planned maintenance

**Characteristics:**
- Cosmetic bugs
- Documentation issues
- Logging or monitoring gaps
- Performance issues with no user impact
- Development/test environment issues

**Response Requirements:**
- Response within 1-2 business days
- Standard ticket/issue tracking
- No special escalation required

**Communication Frequency:** Standard development cycle updates

### Incident Commander Role

#### Primary Responsibilities

1. **Command and Control**
   - Own the incident response process
   - Make critical decisions about resource allocation
   - Coordinate between technical teams and stakeholders
   - Maintain situational awareness across all response streams

2. **Communication Hub**
   - Provide regular updates to stakeholders
   - Manage external communications (status pages, customer notifications)
   - Facilitate effective communication between response teams
   - Shield responders from external distractions

3. **Process Management**
   - Ensure proper incident tracking and documentation
   - Drive toward resolution while maintaining quality
   - Coordinate handoffs between team members
   - Plan and execute rollback strategies if needed

4. **Post-Incident Leadership**
   - Ensure thorough post-incident reviews are conducted
   - Drive implementation of preventive measures
   - Share learnings with broader organization

#### Decision-Making Framework

**Emergency Decisions (SEV1/2):**
- Incident Commander has full authority
- Bias toward action over analysis
- Document decisions for later review
- Consult subject matter experts but don't get blocked

**Resource Allocation:**
- Can pull in any necessary team members
- Authority to escalate to senior leadership
- Can approve emergency spend for external resources
- Make call on communication channels and timing

**Technical Decisions:**
- Lean on technical leads for implementation details
- Make final calls on trade-offs between speed and risk
- Approve rollback vs. fix-forward strategies
- Coordinate testing and validation approaches

### Communication Templates

#### Initial Incident Notification (SEV1/2)

```
Subject: [SEV{severity}] {Service Name} - {Brief Description}

Incident Details:
- Start Time: {timestamp}
- Severity: SEV{level}
- Impact: {user impact description}
- Current Status: {investigating/mitigating/resolved}

Technical Details:
- Affected Services: {service list}
- Symptoms: {what users are experiencing}
- Initial Assessment: {suspected root cause if known}

Response Team:
- Incident Commander: {name}
- Technical Lead: {name}
- SMEs Engaged: {list}

Next Update: {timestamp}
Status Page: {link}
War Room: {bridge/chat link}

---
{Incident Commander Name}
{Contact Information}
```

#### Executive Summary (SEV1)

```
Subject: URGENT - Customer-Impacting Outage - {Service Name}

Executive Summary:
{2-3 sentence description of customer impact and business implications}

Key Metrics:
- Time to Detection: {X minutes}
- Time to Engagement: {X minutes} 
- Estimated Customer Impact: {number/percentage}
- Current Status: {status}
- ETA to Resolution: {time or "investigating"}

Leadership Actions Required:
- [ ] Customer communication approval
- [ ] PR/Communications coordination  
- [ ] Resource allocation decisions
- [ ] External vendor engagement

Incident Commander: {name} ({contact})
Next Update: {time}

---
This is an automated alert from our incident response system.
```

#### Customer Communication Template

```
We are currently experiencing {brief description of issue} affecting {scope of impact}. 

Our engineering team was alerted at {time} and is actively working to resolve the issue. We will provide updates every {frequency} until resolved.

What we know:
- {factual statement of impact}
- {factual statement of scope}
- {brief status of response}

What we're doing:
- {primary response action}
- {secondary response action}

Workaround (if available):
{workaround steps or "No workaround currently available"}

We apologize for the inconvenience and will share more information as it becomes available.

Next update: {time}
Status page: {link}
```

### Stakeholder Management

#### Stakeholder Classification

**Internal Stakeholders:**
- **Engineering Leadership** - Technical decisions and resource allocation
- **Product Management** - Customer impact assessment and feature implications
- **Customer Support** - User communication and support ticket management
- **Sales/Account Management** - Customer relationship management for enterprise clients
- **Executive Team** - Business impact decisions and external communication approval
- **Legal/Compliance** - Regulatory reporting and liability assessment

**External Stakeholders:**
- **Customers** - Service availability and impact communication
- **Partners** - API availability and integration impacts
- **Vendors** - Third-party service dependencies and support escalation
- **Regulators** - Compliance reporting for regulated industries
- **Public/Media** - Transparency for public-facing outages

#### Communication Cadence by Stakeholder

| Stakeholder | SEV1 | SEV2 | SEV3 | SEV4 |
|-------------|------|------|------|------|
| Engineering Leadership | Real-time | 30min | 4hrs | Daily |
| Executive Team | 15min | 1hr | EOD | Weekly |
| Customer Support | Real-time | 30min | 2hrs | As needed |
| Customers | 15min | 1hr | Optional | None |
| Partners | 30min | 2hrs | Optional | None |

### Runbook Generation Framework

#### Dynamic Runbook Components

1. **Detection Playbooks**
   - Monitoring alert definitions
   - Triage decision trees
   - Escalation trigger points
   - Initial response actions

2. **Response Playbooks**
   - Step-by-step mitigation procedures
   - Rollback instructions
   - Validation checkpoints
   - Communication checkpoints

3. **Recovery Playbooks**
   - Service restoration procedures
   - Data consistency checks
   - Performance validation
   - User notification processes

#### Runbook Template Structure

```markdown
# {Service/Component} Incident Response Runbook

## Quick Reference
- **Severity Indicators:** {list of conditions for each severity level}
- **Key Contacts:** {on-call rotations and escalation paths}
- **Critical Commands:** {list of emergency commands with descriptions}

## Detection
### Monitoring Alerts
- {Alert name}: {description and thresholds}
- {Alert name}: {description and thresholds}

### Manual Detection Signs
- {Symptom}: {what to look for and where}
- {Symptom}: {what to look for and where}

## Initial Response (0-15 minutes)
1. **Assess Severity**
   - [ ] Check {primary metric}
   - [ ] Verify {secondary indicator}
   - [ ] Classify as SEV{level} based on {criteria}

2. **Establish Command**
   - [ ] Page Incident Commander if SEV1/2
   - [ ] Create incident tracking ticket
   - [ ] Join war room: {link/bridge info}

3. **Initial Investigation**
   - [ ] Check recent deployments: {deployment log location}
   - [ ] Review error logs: {log location and queries}
   - [ ] Verify dependencies: {dependency check commands}

## Mitigation Strategies
### Strategy 1: {Name}
**Use when:** {conditions}
**Steps:**
1. {detailed step with commands}
2. {detailed step with expected outcomes}
3. {validation step}

**Rollback Plan:**
1. {rollback step}
2. {verification step}

### Strategy 2: {Name}
{similar structure}

## Recovery and Validation
1. **Service Restoration**
   - [ ] {restoration step}
   - [ ] Wait for {metric} to return to normal
   - [ ] Validate end-to-end functionality

2. **Communication**
   - [ ] Update status page
   - [ ] Notify stakeholders
   - [ ] Schedule PIR

## Common Pitfalls
- **{Pitfall}:** {description and how to avoid}
- **{Pitfall}:** {description and how to avoid}

## Reference Information
→ See references/reference-information.md for details

## Usage Examples

### Example 1: Database Connection Pool Exhaustion

```bash
# Classify the incident
echo '{"description": "Users reporting 500 errors, database connections timing out", "affected_users": "80%", "business_impact": "high"}' | python scripts/incident_classifier.py

# Reconstruct timeline from logs
python scripts/timeline_reconstructor.py --input assets/sample_timeline_events.json --output timeline.md

# Generate PIR after resolution
python scripts/pir_generator.py --incident assets/sample_incident_data.json --timeline timeline.md --output pir.md
```

### Example 2: API Rate Limiting Incident

```bash
# Quick classification from stdin
echo "API rate limits causing customer API calls to fail" | python scripts/incident_classifier.py --format text

# Build timeline from multiple sources
python scripts/timeline_reconstructor.py --input assets/simple_timeline_events.json --detect-phases --gap-analysis

# Generate comprehensive PIR
python scripts/pir_generator.py --incident assets/sample_incident_pir_data.json --rca-method fishbone --action-items
```

## Best Practices

### During Incident Response

1. **Maintain Calm Leadership**
   - Stay composed under pressure
   - Make decisive calls with incomplete information
   - Communicate confidence while acknowledging uncertainty

2. **Document Everything**
   - All actions taken and their outcomes
   - Decision rationale, especially for controversial calls
   - Timeline of events as they happen

3. **Effective Communication**
   - Use clear, jargon-free language
   - Provide regular updates even when there's no new information
   - Manage stakeholder expectations proactively

4. **Technical Excellence**
   - Prefer rollbacks to risky fixes under pressure
   - Validate fixes before declaring resolution
   - Plan for secondary failures and cascading effects

### Post-Incident

1. **Blameless Culture**
   - Focus on system failures, not individual mistakes
   - Encourage honest reporting of what went wrong
   - Celebrate learning and improvement opportunities

2. **Action Item Discipline**
   - Assign specific owners and due dates
   - Track progress publicly
   - Prioritize based on risk and effort

3. **Knowledge Sharing**
   - Share PIRs broadly within the organization
   - Update runbooks based on lessons learned
   - Conduct training sessions for common failure modes

4. **Continuous Improvement**
   - Look for patterns across multiple incidents
   - Invest in tooling and automation
   - Regularly review and update processes

## Integration with Existing Tools

### Monitoring and Alerting
- PagerDuty/Opsgenie integration for escalation
- Datadog/Grafana for metrics and dashboards
- ELK/Splunk for log analysis and correlation

### Communication Platforms
- Slack/Teams for war room coordination
- Zoom/Meet for video bridges
- Status page providers (Statuspage.io, etc.)

### Documentation Systems
- Confluence/Notion for PIR storage
- GitHub/GitLab for runbook version control
- JIRA/Linear for action item tracking

### Change Management
- CI/CD pipeline integration
- Deployment tracking systems
- Feature flag platforms for quick rollbacks

