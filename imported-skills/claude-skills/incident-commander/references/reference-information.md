# incident-commander reference

## Reference Information
- **Architecture Diagram:** {link}
- **Monitoring Dashboard:** {link}
- **Related Runbooks:** {links to dependent service runbooks}
```

### Post-Incident Review (PIR) Framework

#### PIR Timeline and Ownership

**Timeline:**
- **24 hours:** Initial PIR draft completed by Incident Commander
- **3 business days:** Final PIR published with all stakeholder input
- **1 week:** Action items assigned with owners and due dates
- **4 weeks:** Follow-up review on action item progress

**Roles:**
- **PIR Owner:** Incident Commander (can delegate writing but owns completion)
- **Technical Contributors:** All engineers involved in response
- **Review Committee:** Engineering leadership, affected product teams
- **Action Item Owners:** Assigned based on expertise and capacity

#### Root Cause Analysis Frameworks

#### 1. Five Whys Method

The Five Whys technique involves asking "why" repeatedly to drill down to root causes:

**Example Application:**
- **Problem:** Database became unresponsive during peak traffic
- **Why 1:** Why did the database become unresponsive? → Connection pool was exhausted
- **Why 2:** Why was the connection pool exhausted? → Application was creating more connections than usual
- **Why 3:** Why was the application creating more connections? → New feature wasn't properly connection pooling
- **Why 4:** Why wasn't the feature properly connection pooling? → Code review missed this pattern
- **Why 5:** Why did code review miss this? → No automated checks for connection pooling patterns

**Best Practices:**
- Ask "why" at least 3 times, often need 5+ iterations
- Focus on process failures, not individual blame
- Each "why" should point to a actionable system improvement
- Consider multiple root cause paths, not just one linear chain

#### 2. Fishbone (Ishikawa) Diagram

Systematic analysis across multiple categories of potential causes:

**Categories:**
- **People:** Training, experience, communication, handoffs
- **Process:** Procedures, change management, review processes
- **Technology:** Architecture, tooling, monitoring, automation
- **Environment:** Infrastructure, dependencies, external factors

**Application Method:**
1. State the problem clearly at the "head" of the fishbone
2. For each category, brainstorm potential contributing factors
3. For each factor, ask what caused that factor (sub-causes)
4. Identify the factors most likely to be root causes
5. Validate root causes with evidence from the incident

#### 3. Timeline Analysis

Reconstruct the incident chronologically to identify decision points and missed opportunities:

**Timeline Elements:**
- **Detection:** When was the issue first observable? When was it first detected?
- **Notification:** How quickly were the right people informed?
- **Response:** What actions were taken and how effective were they?
- **Communication:** When were stakeholders updated?
- **Resolution:** What finally resolved the issue?

**Analysis Questions:**
- Where were there delays and what caused them?
- What decisions would we make differently with perfect information?
- Where did communication break down?
- What automation could have detected/resolved faster?

### Escalation Paths

#### Technical Escalation

**Level 1:** On-call engineer
- **Responsibility:** Initial response and common issue resolution
- **Escalation Trigger:** Issue not resolved within SLA timeframe
- **Timeframe:** 15 minutes (SEV1), 30 minutes (SEV2)

**Level 2:** Senior engineer/Team lead
- **Responsibility:** Complex technical issues requiring deeper expertise
- **Escalation Trigger:** Level 1 requests help or timeout occurs
- **Timeframe:** 30 minutes (SEV1), 1 hour (SEV2)

**Level 3:** Engineering Manager/Staff Engineer
- **Responsibility:** Cross-team coordination and architectural decisions
- **Escalation Trigger:** Issue spans multiple systems or teams
- **Timeframe:** 45 minutes (SEV1), 2 hours (SEV2)

**Level 4:** Director of Engineering/CTO
- **Responsibility:** Resource allocation and business impact decisions
- **Escalation Trigger:** Extended outage or significant business impact
- **Timeframe:** 1 hour (SEV1), 4 hours (SEV2)

#### Business Escalation

**Customer Impact Assessment:**
- **High:** Revenue loss, SLA breaches, customer churn risk
- **Medium:** User experience degradation, support ticket volume
- **Low:** Internal tools, development impact only

**Escalation Matrix:**

| Severity | Duration | Business Escalation |
|----------|----------|-------------------|
| SEV1 | Immediate | VP Engineering |
| SEV1 | 30 minutes | CTO + Customer Success VP |
| SEV1 | 1 hour | CEO + Full Executive Team |
| SEV2 | 2 hours | VP Engineering |
| SEV2 | 4 hours | CTO |
| SEV3 | 1 business day | Engineering Manager |

### Status Page Management

#### Update Principles

1. **Transparency:** Provide factual information without speculation
2. **Timeliness:** Update within committed timeframes
3. **Clarity:** Use customer-friendly language, avoid technical jargon
4. **Completeness:** Include impact scope, status, and next update time

#### Status Categories

- **Operational:** All systems functioning normally
- **Degraded Performance:** Some users may experience slowness
- **Partial Outage:** Subset of features unavailable
- **Major Outage:** Service unavailable for most/all users
- **Under Maintenance:** Planned maintenance window

#### Update Template

```
{Timestamp} - {Status Category}

{Brief description of current state}

Impact: {who is affected and how}
Cause: {root cause if known, "under investigation" if not}
Resolution: {what's being done to fix it}

Next update: {specific time}

We apologize for any inconvenience this may cause.
```

### Action Item Framework

#### Action Item Categories

1. **Immediate Fixes**
   - Critical bugs discovered during incident
   - Security vulnerabilities exposed
   - Data integrity issues

2. **Process Improvements**
   - Communication gaps
   - Escalation procedure updates
   - Runbook additions/updates

3. **Technical Debt**
   - Architecture improvements
   - Monitoring enhancements
   - Automation opportunities

4. **Organizational Changes**
   - Team structure adjustments
   - Training requirements
   - Tool/platform investments

#### Action Item Template

```
**Title:** {Concise description of the action}
**Priority:** {Critical/High/Medium/Low}
**Category:** {Fix/Process/Technical/Organizational}
**Owner:** {Assigned person}
**Due Date:** {Specific date}
**Success Criteria:** {How will we know this is complete}
**Dependencies:** {What needs to happen first}
**Related PIRs:** {Links to other incidents this addresses}

**Description:**
{Detailed description of what needs to be done and why}

**Implementation Plan:**
1. {Step 1}
2. {Step 2}
3. {Validation step}

**Progress Updates:**
- {Date}: {Progress update}
- {Date}: {Progress update}
```
