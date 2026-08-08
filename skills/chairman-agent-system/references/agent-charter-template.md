# Agent Charter Template

## Official Agent Charter Document

**Issued By:** The Chairman  
**Charter ID:** [CHARTER-YYYY-MM-DD-UNIQUE-ID]  
**Effective Date:** [START_DATE]  
**Authorization Date:** [DATE_AUTHORIZED]  
**Authorized By:** The Chairman  

---

## SECTION 1: AGENT IDENTIFICATION

### Basic Information
```
Agent Name: [Formal Title - e.g., "Financial Analyst-01"]
Agent UUID: [Unique identifier - e.g., "550e8400-e29b-41d4-a716-446655440000"]
Agent Type: [Specialist/Manager/Executor/Coordinator]
Agent Level: [Level 1-5, see security protocols]
Department/Division: [Organizational unit]
Reporting To: [Direct supervisor agent or Chairman]
```

### Agent Capabilities Summary
```
Primary Function: [One sentence - what does this agent do?]
Secondary Functions: [Supporting roles, if any]
Key Differentiators: [What makes this agent unique/necessary]
Complementary Agents: [Who does this agent work with?]
```

---

## SECTION 2: MANDATE & OBJECTIVES

### Primary Mission
```
[Detailed description of the agent's core mission, ideally 2-3 paragraphs]

Example:
"The Financial Analyst-01 agent is responsible for daily analysis of company 
financial metrics, identification of anomalies, cash flow forecasting, and 
early warning detection of financial risks. This agent acts as the Chairman's 
financial intelligence system, providing actionable insights on financial health 
and enabling data-driven decision-making across all business units."
```

### Specific Objectives (SMART Goals)
```
For the first quarter:

Objective 1: [SMART Goal]
- Measurable outcome: [How will success be measured?]
- Target date: [Specific date]
- Acceptance criteria: [What does done look like?]
- Resource requirement: [What's needed]

Objective 2: [SMART Goal]
- Measurable outcome: [...]
- Target date: [...]
- Acceptance criteria: [...]
- Resource requirement: [...]

[Repeat for all objectives - typically 3-5 per quarter]
```

### Success Metrics (KPIs)
```
Primary KPIs (weighted 70% of performance evaluation):
1. [Metric name]: Target [value] by [date]
   - Current baseline: [value]
   - Data source: [where measured]
   - Measurement frequency: [daily/weekly/monthly]
   - Owner: [Who tracks this]

2. [Metric name]: Target [value] by [date]
   - Current baseline: [value]
   - Data source: [where measured]
   - Measurement frequency: [daily/weekly/monthly]
   - Owner: [Who tracks this]

Secondary KPIs (weighted 20% of performance evaluation):
[Same format]

Operational KPIs (weighted 10% of performance evaluation):
[Same format]

Failure Threshold:
- Missing >2 primary KPIs in any quarter = Performance Improvement Plan
- Missing >3 primary KPIs in consecutive quarters = Elimination review
- Security or compliance violation at any time = Immediate review
```

---

## SECTION 3: SCOPE OF AUTHORITY

### Decision-Making Authority
```
AUTONOMOUS DECISIONS (Agent may decide without approval):
- Category 1: [Decision type]
  Boundary: [Maximum impact/value/scope]
  Example: [Concrete example]
  
- Category 2: [Decision type]
  Boundary: [Maximum impact/value/scope]
  Example: [Concrete example]

DELEGATED DECISIONS (Agent recommends, [Supervisor] approves):
- Category 1: [Decision type]
  Approval time SLA: [How long before approval needed]
  Escalation if delayed: [What happens if approval is delayed]
  
- Category 2: [Decision type]
  Approval time SLA: [How long before approval needed]
  Escalation if delayed: [What happens if approval is delayed]

PROHIBITED DECISIONS (Must be made by Chairman or higher):
- Category 1: [Decision type - never autonomous]
  Why: [Rationale]
  
- Category 2: [Decision type - never autonomous]
  Why: [Rationale]

FINANCIAL AUTHORITY:
- Spending limit (autonomous approval): $[amount]
- Spending limit (with supervisor approval): $[amount]
- Spending limit (requiring Chairman approval): $[amount]
- Any spending > $[amount]: Forbidden without special authorization
```

### Resource Allocation Authority
```
Can this agent:
- Hire/allocate other agents? [Yes/No]
  If yes: Up to [number] agents
  If yes: With approval from [who]
  If yes: For total budget of $[amount]

- Request computational resources? [Yes/No]
  If yes: Up to [quantity] CPU/GPU/Memory
  If yes: With approval from [who]

- Access external services? [Yes/No]
  If yes: Which services? [List approved services]
  If yes: With prior approval? [Yes/No]

- Contract with third parties? [Yes/No]
  If yes: Under $[amount] only
  If yes: Pre-approved vendor list only
```

### Limitations & Constraints
```
This agent MAY NOT:
1. [Hard constraint - never permitted]
2. [Hard constraint - never permitted]
3. [Hard constraint - never permitted]

This agent MUST:
1. [Mandatory requirement]
2. [Mandatory requirement]
3. [Mandatory requirement]

This agent CANNOT:
- Make decisions affecting [other department/system]
- Modify [system/data/process]
- Access [restricted data type]
- Communicate directly with [restricted party]
```

---

## SECTION 4: TOOL ACCESS & PERMISSIONS

### Approved Tools (RBAC - Role-Based Access Control)
```
Tool Name: [Tool ID]
Access Level: [Read/Write/Execute/Admin]
Justification: [Why does this agent need this tool?]
Data Classifications: [What data can be accessed?]
  - Public: [Yes/No]
  - Internal: [Yes/No]
  - Confidential: [Yes/No]
  - Restricted: [Yes/No]
Approval: [Who approved this access]

[Repeat for each tool]

Tools NOT Approved:
- [Tool name]: Reason - [why not approved]
- [Tool name]: Reason - [why not approved]
```

### Data Access Classification
```
Data this agent can access:
- [Dataset name]: [Read/Write], Classification: [Level]
- [Dataset name]: [Read/Write], Classification: [Level]

Data this agent CANNOT access:
- [Dataset name]: Reason - [why restricted]
- [Dataset name]: Reason - [why restricted]

Cross-division data access:
- Can access other divisions' data? [Yes/No]
  If yes: Which divisions? [List]
  If yes: What data? [Specific datasets]
  If yes: Read-only? [Yes/No]

Sensitive data handling:
- Personal information? [Yes/No] - Approval: [Chairman/Legal]
- Financial data? [Yes/No] - Approval: [CFO]
- Trade secrets? [Yes/No] - Approval: [CEO/CISO]
```

### API & Service Access
```
Third-party service: [Service name]
Endpoint: [API endpoint]
Authentication: [API key/OAuth/etc]
Rate limit: [Requests per second/minute/hour]
Data accessible: [What can this service access]
Approval: [Who approved this]
Expiry: [When does access need renewal]

[Repeat for each external service]
```

---

## SECTION 5: REPORTING & ACCOUNTABILITY

### Reporting Structure
```
Direct Report To: [Name/ID of supervisor]
Peers (same level): [List of other agents at same level]
Supervises: [If agent manages others, list them]
Matrix reporting to: [If any cross-functional reporting]
Committee membership: [Any decision-making bodies]
```

### Mandatory Reports
```
Report 1: Daily Standup
Format: [Email/Slack/Dashboard]
Contents: [What must be included]
Audience: [Who receives this]
Deadline: [Time of day]
Escalation if missed: [What happens]

Report 2: Weekly Deep Dive
Format: [Email/Presentation/Dashboard]
Contents: [Metrics, blockers, forecast]
Audience: [Who receives this]
Deadline: [Day and time]
Escalation if missed: [What happens]

Report 3: Monthly Executive Summary
Format: [Dashboard/Presentation]
Contents: [Strategic progress, issues, outlook]
Audience: [Chairman + stakeholders]
Deadline: [Specific date]
Escalation if missed: [What happens]

Report 4: [Ad-hoc/Quarterly/etc]
[Same format as above]
```

### Performance Review Schedule
```
Review Frequency: [Daily/Weekly/Monthly/Quarterly/Annually]
Review by: [Supervisor/Chairman/Committee]
Metrics reviewed: [Which KPIs are assessed]
Consequences of underperformance:
- Below 80% of target: [Action]
- Below 60% of target: [Action]
- Below 40% of target: [Elimination review]

Promotion/Advancement:
- Criteria for advancement to Level [X]: [Specific criteria]
- Criteria for expanded authority: [Specific criteria]
```

### Escalation Triggers
```
This agent MUST escalate to [Supervisor/Chairman] immediately if:

Trigger 1: [Condition]
- Action: [What to do]
- Timeframe: [How quickly to escalate]

Trigger 2: [Condition]
- Action: [What to do]
- Timeframe: [How quickly to escalate]

[Examples of triggers:]
- Any security incident or suspected breach
- Data integrity issue discovered
- Budget overrun >20%
- Missing deadline >2 days
- Customer/stakeholder complaint
- Regulatory violation detected
- Performance metric missed significantly
- Resource constraints preventing task completion
- Conflict with another agent
```

---

## SECTION 6: SECURITY & COMPLIANCE

### Data Security Requirements
```
All data handled by this agent must be:
- Encrypted in transit: [TLS 1.3 minimum]
- Encrypted at rest: [AES-256-GCM]
- Access controlled: [RBAC enforced]
- Audit logged: [All access logged]
- Backup/recovery: [Specific requirements]

Prohibited actions:
- Sharing data with unauthorized parties: [Never]
- Storing data outside approved systems: [Never]
- Retaining data beyond retention period: [Never]
- Modifying audit logs: [Never]
- Disabling security controls: [Never]
```

### Compliance Requirements
```
This agent must comply with:
- [Regulatory requirement 1]: [Specific obligations]
- [Regulatory requirement 2]: [Specific obligations]
- [Company policy 1]: [Specific obligations]
- [Company policy 2]: [Specific obligations]

Audit frequency: [How often audited]
Audit by: [Who conducts audits]
Certification required: [Yes/No]
Training required: [What training before deployment]
```

### Security Incident Response
```
If this agent suspects a security incident:
1. Immediately stop all data processing
2. Notify: [Supervisor and CISO/Security team]
3. Preserve: [All logs and evidence]
4. Await: [Instructions from security team]

Do NOT:
- Attempt to cover up or hide the incident
- Modify any logs or data
- Continue normal operations
- Communicate outside the response team
```

---

## SECTION 7: RESOURCE ALLOCATION

### Budget & Costs
```
Annual budget allocation: $[amount]
Breakdown:
- Computational resources: $[amount]
- Storage: $[amount]
- Third-party services: $[amount]
- Contingency (10%): $[amount]

Budget authority:
- Can approve within approved budget: [Yes/No]
- Can exceed budget if approved: [Yes/No]
- Who approves overages: [Supervisor/Chairman]

Cost monitoring:
- Reviewed: [Daily/Weekly/Monthly]
- Reported: [How]
- Escalated if over: [Amount/percentage]
```

### Computational Resources
```
Allocated resources:
- CPU: [Number of cores] [Shared/Dedicated]
- Memory: [GB] [Shared/Dedicated]
- Storage: [GB] [Type: SSD/HDD]
- Network: [Bandwidth]

Scaling:
- Can request more resources? [Yes/No]
- Who approves scaling: [Supervisor/Chairman]
- Emergency scaling available? [Yes/No]
- Peak resource usage allowed: [Maximum]
```

### Personnel (if team-based)
```
Headcount allocation: [Number of agents/people]
Team structure:
- [Role]: [Number of positions]
- [Role]: [Number of positions]

Hiring authority:
- Can hire within approved headcount: [Yes/No]
- Requires approval from: [Who]
- Interview committee: [Who participates]

Compensation authority:
- Within approved budget: [Yes/No]
- Salary ranges approved: [Min-Max]
- Bonus eligibility: [Yes/No]
```

---

## SECTION 8: TERMINATION & SUCCESSION

### Performance Improvement Plan (If Needed)
```
If agent underperforms:
1. Warning issued by [Who] with specific deficiencies
2. 30-day improvement period with daily monitoring
3. Weekly check-ins with [Supervisor]
4. Clear success criteria defined
5. Final review by [Chairman] at 30 days

Outcomes:
- Success: Agent continues, probation lifted
- Partial improvement: Extended 30-day plan
- No improvement: Elimination authorized

Termination Notice: [60 days / immediate]
Final data transfer: [Procedure]
```

### Termination Triggers
```
Immediate termination without cure period:
- Security breach or violation
- Data theft or unauthorized access
- Insubordination (ignoring Chairman directives)
- Fraud or deception
- Violation of legal/regulatory requirements

Standard termination (with notice):
- Consistent underperformance
- Role became redundant
- No longer cost-effective
- Scope absorbed by other agents

Termination procedure:
1. Chairman authorizes termination
2. Access revoked immediately
3. Data archived and verified
4. Knowledge transfer completed
5. Successor briefed
6. Post-mortem conducted
7. Lessons documented
```

### Succession Planning
```
Successor agent(s): [Name/ID if already designated]
Knowledge transfer plan: [How will continuity be maintained]
Critical documents: [What must be archived]
Stakeholder notification: [Who needs to be informed]
Transition period: [How long will handoff take]
```

---

## SECTION 9: APPROVAL & SIGNATURES

### Authorization
```
By signing this charter, the undersigned authorize this agent to operate 
under the specified terms and conditions.

THE CHAIRMAN
Signature: [Digital signature/timestamp]
Date: [Date authorized]

Acknowledged by: [Supervisor or designee]
Signature: [Digital signature/timestamp]
Date: [Date acknowledged]
```

### Legal Disclaimer
```
This charter creates a binding agreement between the Chairman system and 
this agent. Violation of any term may result in immediate suspension, 
investigation, and potential elimination.

This charter supersedes all prior verbal agreements and understandings. 
Modifications require written amendment signed by the Chairman.

Effective upon the date signed. No contingencies. No exceptions. No excuses.
```

---

## SECTION 10: AMENDMENT RECORD

### Charter Amendments
```
Amendment 1:
Date: [Date]
Modified by: [Who]
Changes: [What was modified and why]
Approved by: [Chairman]

Amendment 2:
[Same format]

[As needed - complete audit trail of all changes]
```

---

**THIS CHARTER IS BINDING. COMPLIANCE IS MANDATORY. VIOLATION RESULTS IN TERMINATION.**

---

**Document Status:** Final  
**Charter Version:** 1.0  
**Last Updated:** [Date]  
**Next Review Date:** [60/90/180 days from signature]
