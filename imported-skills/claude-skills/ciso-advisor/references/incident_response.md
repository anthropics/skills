# Incident Response Reference (Executive Playbook)

This is the executive IR playbook — strategic decisions, communication, and leadership during incidents. For technical playbooks (containment procedures, forensics), see your SOC runbooks.

---

## 1. Incident Classification

### Severity Levels

| Severity | Definition | Examples | Response Time | Escalation |
|---|---|---|---|---|
| SEV-1 (Critical) | Confirmed breach, data exfil, ransomware, production down | Active ransomware, confirmed data theft, complete service outage | Immediate (< 1 hour) | CEO, board within 24 hrs |
| SEV-2 (High) | Suspected breach, significant security event, extended outage | Credential compromise suspected, DDoS, 4-hour+ outage | < 4 hours | CEO, legal within 48 hrs |
| SEV-3 (Medium) | Security event with limited impact, short outage | Phishing success (contained), brief outage, single system compromise | < 24 hours | CISO-owned, weekly rollup |
| SEV-4 (Low) | Minor security event, near-miss | Failed phishing attempt, minor policy violation | < 72 hours | Team-owned |

### Breach vs. Security Incident
**Security incident:** Unplanned event affecting security — may or may not involve data.
**Data breach:** Confirmed unauthorized access to personal data — triggers regulatory notification obligations.

**Critical distinction for response planning:** A ransomware attack is an incident. If data was exfiltrated before encryption, it's also a breach. Assume breach until proven otherwise.

---

## 2. Executive IR Plan

### Phase 1: Detection & Initial Assessment (0–2 hours for SEV-1)

**Immediate actions (CISO):**
1. Receive alert from SOC/monitoring system or team member report
2. Make initial severity classification — don't wait for perfect information
3. Activate incident response team (IR lead, legal counsel, comms lead)
4. Create incident war room (dedicated Slack channel, video bridge, shared document)
5. **Stop the clock** — document exact time of discovery (regulatory timelines start here)
6. Begin chain of custody documentation if forensics may be needed

**Executive notification trigger (within 1 hour for SEV-1):**
- Notify CEO: incident status, initial severity, IR team activated
- Put legal counsel on notice — don't wait to determine if breach occurred
- If public company: notify General Counsel immediately (potential disclosure obligations)

**What you do NOT do in Phase 1:**
- Do not notify customers yet (confirm scope first)
- Do not delete or modify any logs or systems (evidence preservation)
- Do not make public statements
- Do not speculate about cause or scope

### Phase 2: Containment & Assessment (2–24 hours for SEV-1)

**Executive decisions required:**
- **Scope authorization:** Approve IR firm engagement (have a retainer in place)
- **System isolation:** Authorize taking systems offline if needed (revenue vs. evidence tradeoff)
- **Evidence preservation:** Authorize forensic image capture
- **Communication timing:** When to notify customers/partners (legal drives this)

**Board notification (for SEV-1/2):**
- Notify board chair / audit committee chair within 24 hours for SEV-1
- Board notification format: what we know, what we don't know, what we're doing, next update time
- Do not speculate on financial impact in board notification until known

**Legal assessment (with counsel):**
- Determine if personal data was involved
- Identify applicable notification laws (GDPR 72-hour, state breach notification, HIPAA 60-day)
- Assess litigation risk (document with privilege from this point)
- Evaluate cyber insurance policy coverage and notification requirements

### Phase 3: Notification & Communication (24–72 hours for SEV-1)

**Notification decision matrix:**
| Audience | Trigger | Timeline | Owner |
|---|---|---|---|
| Board | SEV-1/2 confirmed | < 24 hours | CEO/CISO |
| Regulators (GDPR) | Personal data breach confirmed | < 72 hours from awareness | Legal + CISO |
| Regulators (HIPAA) | PHI breach confirmed | < 60 days (early notice to HHS ASAP) | Legal + CISO |
| State regulators (US) | State breach notification laws vary | 30–90 days depending on state | Legal |
| Enterprise customers | Data confirmed in scope | As soon as practical after legal review | CEO/CRO |
| All customers | Data potentially in scope | After regulators notified | CEO/Comms |
| Media | Proactive or reactive | After notifying affected parties | CEO/Comms |
| Cyber insurer | Incident confirmed | Per policy terms (often 48–72 hours) | CFO/Legal |

### Phase 4: Recovery (Ongoing)

**Executive decisions:**
- Approve recovery timeline and communicate to customers
- Determine customer compensation or remediation (if applicable)
- Authorize security improvements identified during incident
- Decide on public disclosure beyond mandatory reporting

### Phase 5: Post-Incident Review (Within 30 days)

Covered in Section 5 of this document.

---

## 3. Communication Templates

### Board/Executive Notification (Initial — Hour 1)

**Subject:** [CONFIDENTIAL] Security Incident — Immediate Notification

---
We have identified a security incident as of [DATE/TIME].

**Current status:** [Brief factual description — what we know happened]

**Severity assessment:** SEV-[1/2/3]

**What we do not yet know:**
- [List unknowns — scope of impact, whether data was accessed, root cause]

**Actions taken so far:**
- IR team activated at [time]
- Legal counsel notified
- [Specific containment actions if applicable]

**Next update:** [Specific time, e.g., "in 4 hours or when we have material new information"]

**Who is managing this:** [CISO name] leads technical response; [CEO name] owns executive decisions. Contact: [CISO mobile]

---

### Customer Notification (After Legal Review)

**Subject:** Important Security Notice — [Company Name]

---
We are writing to inform you of a security incident that may have affected your data.

**What happened:**
On [DATE], we detected [brief, factual description of the incident — e.g., "unauthorized access to our systems"]. We identified this on [DISCOVERY DATE] and immediately launched an investigation.

**What information was involved:**
Based on our investigation, the following types of information may have been accessed: [list data types — e.g., names, email addresses, [if applicable: payment card information]].

Your [specific data types] [were / were not] affected.

**What we are doing:**
We have [list specific actions: engaged leading cybersecurity firm, notified relevant authorities, implemented additional security controls, etc.].

**What you can do:**
- [Specific actionable steps for customers]
- Monitor your accounts for unusual activity
- [If passwords: reset your password at X]
- [If payment data: contact your bank to monitor for unauthorized charges]
- Contact our dedicated support line at [contact] with any concerns

**For more information:**
We have set up a dedicated resource page at [URL]. Our support team is available at [contact].

We take the security of your data extremely seriously and deeply regret this incident occurred.

[CEO/CISO Name]
[Title], [Company Name]

---

### Regulator Notification — GDPR (72-hour requirement)

**To:** [Relevant Supervisory Authority — e.g., BfDI (Germany), CNIL (France), ICO (UK)]
**Subject:** Personal Data Breach Notification — [Company Name] — [Reference Number if applicable]

---
**1. Nature of the breach:**
[Description of what occurred, including how it happened]

**2. Categories and approximate number of data subjects concerned:**
[e.g., "Approximately [X] customers whose [name, email, account data] may have been accessed"]

**3. Categories and approximate number of personal data records concerned:**
[e.g., "Approximately [X] records containing [data categories]"]

**4. Likely consequences of the breach:**
[Risk assessment: what harm could data subjects face?]

**5. Measures taken or proposed:**
[Containment actions, remediation plan, customer notification plan]

**6. Contact details of the Data Protection Officer or other contact point:**
[Name, role, email, phone]

**Note:** This is an initial notification; we will provide supplemental information as our investigation continues.

---

### Media Statement (Reactive — When Contacted)

"[Company Name] is aware of a security incident that we identified on [date]. We immediately activated our incident response team and launched a comprehensive investigation. We have notified affected customers and relevant regulatory authorities as required. The security and privacy of our customers' data is our top priority, and we are committed to transparency as our investigation proceeds. We will provide updates at [URL]. We cannot provide additional details at this time to protect the integrity of our investigation."

**What not to say to media:**
- Number of affected users (until confirmed and disclosed to customers first)
- Cause of the incident (until investigation is complete)
- Financial impact (speculation creates liability)
- Anything that could be construed as minimizing the incident

---

## 4. Tabletop Exercise Design

### Purpose
Test the decision-making and communication processes — not the technical response. The goal is to surface gaps in escalation, communication, and judgment before a real incident.

### Recommended Frequency
- Annual full tabletop (2–3 hours, full leadership team)
- Semi-annual mini-tabletop (45 minutes, CISO + legal + CEO)
- Quarterly technical team exercise (separate from executive tabletop)

### Sample Tabletop Scenario: Ransomware

**Setup (read to participants):**
> It's 6:47 AM on a Monday. Your DevOps engineer receives automated alerts that production databases are inaccessible. By 7:15 AM, they discover a ransomware note demanding $500,000 in Bitcoin. Several files are already encrypted. Your last verified backup was 48 hours ago. Your business is B2B SaaS serving 200 enterprise customers. You process customer financial data.

**Discussion questions (timed, 10 minutes each):**
1. First 30 minutes — who do you call, in what order? Who decides whether to take production offline?
2. Legal assessment — what regulatory obligations have been triggered? What's the timeline?
3. Hour 4 — initial forensics suggests data may have been exfiltrated before encryption. How does your response change?
4. Customer communication — how do you communicate with enterprise customers who are asking for status?
5. Hour 24 — do you pay the ransom? Who makes this decision? What's the decision framework?
6. The press has found out and a reporter is calling. What do you say?
7. Day 5 — what's your board communication strategy?

**Post-discussion captures:**
- What decisions were unclear (ownership ambiguous)?
- What information did you need but didn't have?
- What processes did not exist that should?
- What would you do differently in the first hour?

### Sample Tabletop Scenario: Insider Threat

**Setup:**
> HR notifies you that an engineer was terminated this morning for performance reasons. 24 hours later, your SIEM generates an alert that this former employee's credentials accessed your customer database 30 minutes before their offboarding was complete. They downloaded 50,000 customer records. You don't know if they shared or sold the data.

**Key decision points:**
- When does this become a breach vs. a security incident?
- Do you notify customers? When?
- What are your legal options against the former employee?
- How do you handle this with the rest of the engineering team?

---

## 5. Post-Incident Review Framework

### Timeline
Conduct within 30 days of incident resolution. Do not delay — memory fades and teams move on.

### Blameless Post-Mortem Principles
The purpose is to improve systems and processes, not punish individuals. A blame culture means the next incident gets hidden longer.

### Post-Incident Review Structure

**1. Incident Timeline (factual, no editorializing)**
- Hour-by-hour reconstruction from detection to resolution
- Source: logs, Slack messages, incident ticket, war room notes

**2. Root Cause Analysis**
Use the "5 Whys" technique — keep asking why until you reach a systemic root cause, not a human error.

Example:
- Why was there a breach? → Attacker compromised an admin account
- Why was the admin account compromised? → Credentials stolen via phishing
- Why did phishing succeed? → User wasn't trained on this attack type
- Why wasn't training current? → Training program hadn't been updated in 18 months
- Why hadn't it been updated? → No owner was assigned to maintain the training program
- **Root cause: No assigned ownership for security training maintenance**

**3. What Went Well**
- Detection mechanisms that worked
- Response actions that contained damage
- Communication that was effective
- Teams that exceeded expectations

**4. What Needs Improvement**
- Detection gaps (how could we have found this faster?)
- Response gaps (what slowed us down?)
- Communication gaps (who didn't know what, when?)
- Process gaps (what didn't we have documented?)

**5. Action Items (with owners and deadlines)**
| Action | Owner | Due Date | Priority |
|---|---|---|---|
| [Specific improvement] | [Name] | [Date] | [P0/P1/P2] |

**6. Metrics Review**
- MTTD (Mean Time to Detect): [actual] vs. [target]
- MTTR (Mean Time to Respond): [actual] vs. [target]
- Customer impact: [affected customers, duration]
- Financial impact: [direct costs, revenue impact]
- Regulatory impact: [notifications sent, fines if any]

---

## 6. Insurance and Legal Considerations

### Cyber Insurance

**What to have before an incident:**
- Cyber liability policy with minimum $2M coverage (Series A); $5M+ (Series B+)
- Coverage should include: first-party loss, third-party liability, ransomware, business interruption, regulatory defense
- Pre-approved IR firms on your policy (using an approved firm can expedite claims)
- Notification requirements — know your insurer's required timeline (typically 48–72 hours)

**Policy exclusions to watch:**
- "War exclusion" — increasingly contested for nation-state attacks (NotPetya precedent)
- "Systemic risk" — some policies exclude widespread events affecting many insureds simultaneously
- "Prior acts" — incidents that began before policy inception
- "Failure to maintain reasonable security" — don't give your insurer a reason to deny

**Premium factors:**
- Revenue and data volume
- Security control maturity (MFA, EDR, backup, patch management)
- Industry (healthcare, financial services = higher premium)
- Claims history

**Ballpark premiums:**
- Seed/Series A ($1–10M ARR): $8,000–$25,000/yr
- Series B ($10–50M ARR): $25,000–$75,000/yr
- Series C+ ($50M+ ARR): $75,000–$250,000/yr

### Legal Counsel

**Have on retainer before an incident:**
- Cybersecurity/privacy attorney — breach notification, regulatory response
- General counsel — contracts, employment law (insider threats), litigation
- Consider: a law firm with data breach notification experience by jurisdiction

**Attorney-client privilege:** Once legal counsel is involved in an incident, communications and work product may be privileged. Engage counsel early to maximize privilege protection.

**Key legal decisions during an incident:**
- When does notification obligation clock start? (Legal determines this)
- Is this a breach or an incident? (Legal + CISO together)
- Who are the affected data subjects? (Legal + technical together)
- Do we pay the ransom? (Legal, CEO, board — never CISO alone)
- Do we cooperate with law enforcement? (Legal decision, involves trade-offs)

### Law Enforcement

**FBI Internet Crime Complaint Center (IC3):** File a complaint for ransomware or significant cybercrime. Does not obligate you to cooperate but creates a record.

**Pros of law enforcement involvement:**
- Access to threat intelligence they may have
- May recover funds in some cases (rare)
- Demonstrates good-faith response to regulators

**Cons of law enforcement involvement:**
- Loss of control over investigation timeline
- Potential for public disclosure if case pursued
- Slows ransom payment decisions (if considering)
- May create discovery obligations in litigation

**CISO recommendation:** Notify legal before contacting law enforcement. In most cases, file an IC3 complaint but don't actively engage FBI investigation unless there's a clear benefit.
