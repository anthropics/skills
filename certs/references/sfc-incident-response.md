# SFC: SEAL Framework Checklist

SFC Incident Response certification: team roles, 24/7 monitoring, paging systems, response playbooks, signer coordination, emergency communications, and regular drills.

**Controls and baselines for self-assessment and certification.**

## ir-1: Governance & Team Structure

### ir-1.1.1 — IR Team and Role Assignments
**Q:** Do you have an incident response team with clearly defined roles and responsibilities?

**Baselines:**
- Incident commander (with designated backup) who coordinates response, assigns tasks, and makes time-sensitive decisions
- Subject matter experts identified for key domains (smart contracts, infrastructure, security) who can analyze attacks and prepare response strategies
- Scribe role defined for real-time incident documentation
- Communications personnel designated for public information sharing and record-keeping
- Legal support available with procedures for reviewing response actions, whitehat engagement, and public communications
- Decision makers defined for high-stakes decisions (system shutdown, public disclosure, fund recovery)
- Roles, authorities, and escalation measures reviewed at least annually and after protocol changes, team restructuring, or major incidents

### ir-1.1.2 — Stakeholder Coordination and Contacts
**Q:** Do you maintain current contacts and coordination procedures for all parties needed during an incident?

**Baselines:**
- Internal coordination procedures between technical (devs, auditors) and operational teams (security council, communications)
- External protocol contacts for protocols you depend on and protocols that depend on you
- External expertise contacts including forensics firms, security consultants, SEAL 911, and auditors
- Legal counsel and communications/PR contacts
- Infrastructure vendor support contacts and escalation procedures
- Contact list reviewed at least quarterly and after team changes
- Escalation order documented for P1 incidents (e.g., SEAL 911 → decision makers → security partners → legal)

## ir-2: Monitoring, Detection & Alerting

### ir-2.1.1 — Monitoring Coverage
**Q:** Do you maintain monitoring coverage for your critical systems, protocols, and external attack surfaces?

**Baselines:**
- Monitoring covers critical smart contracts, infrastructure, and on-chain activity
- 24/7 monitoring capabilities with procedures for after-hours alert handling
- Credential and secret exposure detection including dark web monitoring, breach database scanning, and secret scanning in code repositories
- Organizational account monitoring including social media accounts and websites monitored for unauthorized access or compromise
- Monitoring coverage documented — what's covered, what's not, and known gaps

### ir-2.1.2 — Alerting, Paging, and Escalation
**Q:** Do you have alerting and paging systems that reliably route incidents to available responders?

**Baselines:**
- Automated alerting configured for security events and operational issues
- Alerts include embedded triage guidance for distinguishing true incidents from false positives
- Triage and classification procedures documented with escalation paths based on severity
- Time-based escalation triggers if initial responder doesn't acknowledge within defined window
- Management notification requirements for high-severity incidents
- Redundant paging systems with documented failover procedures
- On-call schedules maintained with adequate coverage for operational needs
- Backup procedures when on-call personnel are unreachable

### ir-2.1.3 — Logging Integrity and Retention
**Q:** Do you maintain tamper-evident logs with adequate retention for incident investigation?

**Baselines:**
- Log retention periods defined for security, infrastructure, and cloud provider logs
- Retention adequate for forensic analysis (consider regulatory requirements and typical investigation timelines)
- Tamper-evident logging for security-relevant events including access logs, alerting system logs, and infrastructure logs
- Alerts triggered if logs are altered, deleted, or if monitoring/logging is disabled
- Log sources documented — what's captured and where it's stored

## ir-3: Response & Emergency Operations

### ir-3.1.1 — Response Playbooks
**Q:** Do you maintain response playbooks for common incident types?

**Baselines:**
- Playbooks cover key scenarios including protocol exploits, infrastructure failures, access control breaches, key compromise, supply chain compromises, and frontend/DNS compromise
- Each playbook includes initial response actions covering containment, evidence preservation, and stakeholder notification
- Role-specific responsibilities defined for each scenario (who does what — technical, comms, legal)
- Escalation criteria documented for when to engage leadership, when to shut down systems, when to make public disclosure, and when to engage external assistance
- Key compromise playbook includes procedures for rotating keys and replacing compromised signers, with threshold and access reviewed after any signer replacement

### ir-3.1.2 — Signer Reachability and Coordination
**Q:** Can you reach enough signers to execute emergency on-chain actions at any time, including outside business hours?

**Baselines:**
- Procedures for coordinating multisig operations during incidents, including cross-timezone signer availability
- Signers integrated into on-call/paging systems
- Escalation paths documented for when signers are unreachable
- Tested quarterly

### ir-3.1.3 — Emergency Transaction Readiness
**Q:** Do you have backup signing infrastructure and pre-prepared emergency transactions for critical protocol functions?

**Baselines:**
- Pre-signed or pre-prepared emergency transactions for critical protocol functions (pause, freeze, parameter changes) where feasible
- Backup signing infrastructure available including alternate signing UI, backup RPC providers, and alternate block explorer
- Emergency execution procedures documented (what to pause/freeze/modify and the process for doing so)

## ir-4: Communication & Coordination

### ir-4.1.1 — Incident Communication Channels
**Q:** Do you maintain secure, dedicated communication channels for incident response?

**Baselines:**
- Dedicated incident communication channels with documented access controls and member lists
- Multiple communication channels (primary and backup) on different platforms, with documented failover procedures
- Procedures for rapidly creating incident-specific channels (war room) when needed
- Secure communication procedures for sensitive incident information including need-to-know access and encrypted channels

### ir-4.1.2 — Internal Status Updates
**Q:** Do you have procedures for providing regular status updates to stakeholders during incidents?

**Baselines:**
- Status update cadence defined by severity level
- Format and distribution lists for internal stakeholders

### ir-4.1.3 — Public Communication and Information Management
**Q:** Do you have procedures for public communication and information management during incidents?

**Baselines:**
- Pre-approved communication templates for different incident types and severity levels
- Procedures for coordinating communications with protocol users during and after incidents
- Procedures for managing public information flow and correcting misinformation during active incidents
- Designated communications approval flow before public statements are released

## ir-5: Testing & Continuous Improvement

### ir-5.1.1 — IR Drills and Testing
**Q:** Do you conduct regular incident response drills and evaluate the results?

**Baselines:**
- Drills conducted at least annually
- Drills cover different incident types across exercises (protocol exploit, infrastructure failure, key compromise, etc.)
- Tests the full pipeline from monitoring through alerting, paging, triage, escalation, team coordination, containment, and recovery
- Production alerting pipeline validated end-to-end from event detection through to responder notification and acknowledgment
- Drill documentation includes date, scenario, participants, response times, gaps identified, and corrective actions
- Corrective actions tracked to completion with owners and deadlines
- Drill findings incorporated into playbook and procedure updates
