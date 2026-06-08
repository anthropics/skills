# Risk Management in Tech

## Risk Taxonomy for Tech Companies

Four categories of risk that tech leaders must manage:

| Category | Examples | Owner |
|----------|----------|-------|
| Operational risk | System outages, data loss, infrastructure failures | Engineering / SRE |
| Vendor/supply chain risk | SaaS dependency failure, vendor lock-in, price risk | Engineering + Procurement |
| People risk | Key person dependency, attrition, succession gaps | Engineering management + HR |
| Security/compliance risk | Data breaches, regulatory non-compliance, vulnerabilities | Security + Engineering |

## Business Continuity Planning (BCP)

BCP is the practice of ensuring critical business functions can continue during and after a disaster.

### BCP vs. Disaster Recovery

| BCP | Disaster Recovery (DR) |
|-----|----------------------|
| Business processes and operations | IT systems and data |
| "How do we keep running?" | "How do we restore systems?" |
| Cross-functional (people, process, systems) | Primarily IT-focused |
| Broader scope | Narrower scope, more technical |

**IBM's framing**: BCP is the broader strategy; DR is a subset that addresses IT system restoration specifically.

### BCP Components for Tech Companies

**1. Business Impact Analysis (BIA)**
For each critical system and process, determine:
- RTO (Recovery Time Objective): How long can we be down before business impact is severe?
- RPO (Recovery Point Objective): How much data loss is acceptable? (How old can a backup be?)

Typical targets by tier:
| Tier | Examples | RTO | RPO |
|------|---------|-----|-----|
| Tier 0 (mission-critical) | Customer-facing API, auth service, payment | < 15 min | 0 (no data loss) |
| Tier 1 (critical) | Core product features | < 1 hour | < 15 min |
| Tier 2 (important) | Internal tools, analytics | < 4 hours | < 1 hour |
| Tier 3 (deferrable) | Batch jobs, reporting | < 24 hours | < 4 hours |

**2. Recovery Strategies**
- Tier 0: Active-active redundancy (zero failover time), multi-region deployment
- Tier 1: Active-passive with automated failover (e.g., AWS Route 53 failover routing)
- Tier 2: Manual failover from backups
- Tier 3: Restore from last backup

**3. Runbooks**
For every failure scenario, a documented runbook: who does what, in what order, with what tools. Runbooks must be:
- Tested (not just written)
- Accessible when systems are down (not stored only in the system that failed)
- Owned by a named person
- Updated after incidents

**4. Testing**
- **Tabletop exercises**: Talk through a hypothetical disaster scenario (no systems touched). Good for identifying process gaps.
- **Game days**: Inject a real failure in production or staging and practice the response. Netflix's Chaos Engineering (Chaos Monkey) is the canonical example.
- **DR drills**: Actually fail over to the DR environment and verify it works. Do this at least annually.

**2024 trend**: Organizations are integrating cybersecurity and operational resilience into unified strategies. DORA (Digital Operational Resilience Act, the EU regulation — not the DevOps metrics) mandates this for financial services.

## Vendor Concentration Risk

**Definition**: Excessive dependence on a single vendor such that their failure would cause significant business harm.

### The CrowdStrike Lesson (July 2024)
A faulty CrowdStrike Falcon sensor update caused ~8.5 million Windows systems globally to BSOD. Airlines, banks, hospitals, and media companies were severely impacted. Root cause: a single vendor's update pipeline had global blast radius with no circuit breaker.

**Lessons for tech leaders**:
1. Security tools are not immune to being the source of an outage
2. Automatic update propagation without staged rollout is a risk
3. Vendor concentration in security tooling is itself a security risk
4. You need a contingency plan for "what do we do if [critical vendor] is down?"

### Assessing Vendor Concentration Risk
Questions to ask for each critical vendor:
- If this vendor is unavailable for 1 hour / 1 day / 1 week, what breaks?
- Is there a viable alternative we could switch to in an emergency?
- Do we have a documented contingency plan?
- What is the blast radius of a vendor-side bug (like CrowdStrike)?

### Mitigation Strategies
- **Dual vendor for critical categories**: Don't put all observability in Datadog with no fallback
- **Design for vendor portability**: Avoid deep proprietary API lock-in; abstract vendor-specific code behind internal interfaces
- **Staged rollout requirements**: Require that vendor updates (especially security tools) roll out gradually, not all-at-once
- **Contract SLAs**: Ensure vendor SLAs match your RTO/RPO requirements; verify that penalties are meaningful
- **Regular vendor review**: Annually assess health, roadmap alignment, alternative landscape

## Key Person Dependency

**Definition**: Critical knowledge, decision-making authority, or customer relationships that reside in only one or two people.

### The Risk Profile
When a key person leaves:
- Projects stall or regress (institutional knowledge lost)
- Customer relationships at risk (if they were the sole point of contact)
- Architectural decisions become unclear (if only they understood why things are built this way)
- On-call gaps (if they were the only one who understood a critical service)

### Identifying Key Person Dependencies
- **Bus factor audit**: For every critical service and capability, how many people need to be hit by a bus (or leave) before you're in crisis? Anything with a bus factor of 1 is a critical risk.
- **On-call ownership**: Are there services where only one engineer can resolve incidents?
- **Customer relationship audit**: Are there customers where one sales engineer or CSM is the only contact?

### Mitigation Strategies

**Technical knowledge**:
- Documentation-first culture: all critical architectural decisions in ADRs, runbooks for every service
- Pair programming on high-risk services: at least two engineers understand each critical system deeply
- Rotation of on-call: no engineer should be the perpetual only person on-call for a service
- Game days with junior engineers: practice incident response so knowledge transfers through doing

**People risk**:
- Succession planning (3x3 model: for each critical role, name 3 people who could grow into it)
- Cross-training: deliberately train backup people for each critical function
- Knowledge transfer sessions: regular "lunch and learns" where people share what they know
- Documentation as a performance expectation: engineers who don't document are creating bus risk

**Note**: Key person dependency is also a management failure. If your senior architect is the only person who understands the data model, that's not the architect's problem — it's an org design failure.

## Security Risk Management

### Engineering's Security Responsibilities

**Shift-left security**: Find and fix security issues earlier in the development process (during design and coding) rather than later (in production). Cheaper, faster, less disruptive.

**Security in the SDLC**:
- Design: Threat modeling (STRIDE, PASTA) for new features that handle sensitive data
- Coding: SAST (Static Application Security Testing) tools in CI (Semgrep, SonarQube, Snyk)
- Review: Security checklist as part of code review for security-sensitive code
- Deploy: DAST (Dynamic Application Security Testing), container scanning
- Production: Vulnerability scanning, dependency auditing, anomaly detection

### Dependency and Supply Chain Risk
- Keep dependencies up to date (use tools like Dependabot, Renovate Bot for automated PR creation)
- Track known CVEs in your dependency tree (Snyk, GitHub Advanced Security, Grype)
- Verify provenance of open-source dependencies: don't blindly trust npm/PyPI packages
- SBOM (Software Bill of Materials): increasingly required for government and enterprise customers

### IBM Cost of a Data Breach 2024
- 40% of data breaches involved data stored across multiple environments (hybrid cloud, multi-cloud)
- Average cost of a data breach: $4.88M globally
- Breaches take an average of 258 days to identify and contain

**Implication**: Data classification and segmentation (not storing sensitive data across multiple environments without controls) is a first-order security priority.

### Access Control
- **Principle of least privilege**: Every system and person should have only the minimum access required to do their job
- **Just-in-time access**: Elevated access granted only when needed, auto-revoked (tools: Teleport, Boundary, PagerDuty JIRA automation)
- **MFA everywhere**: Especially for production systems, CI/CD, and cloud consoles
- **Regular access audits**: Quarterly audit of who has access to what, especially in production

### Security Incident Response
Integrate with incident management (see devops-sre.md). Add a security-specific escalation path:
- P0 security incidents: active breach, data exfiltration in progress → immediate CISO/legal notification
- P1 security: credential compromise, unpatched critical CVE in production → same-day response
- Security postmortems: same blameless format as operational postmortems

## Sources
- IBM "Cost of a Data Breach Report" 2024
- Bryghtpath — "Business Continuity Insights from the Biggest Disruptions of 2024"
- Ncontracts — "Business Continuity Planning vs Disaster Recovery"
- IBM Think — "Business Continuity vs. Disaster Recovery"
- GARP Risk Intelligence — "Continuity and Resilience: Lessons from 2023 into 2024"
- SecurityScorecard — "Guide to Developing a Business Continuity Plan"
- Fusion Risk Management — "2025 Trends in Continuity and Resilience"
- BCM Institute Blog — "Top Trends and Best Practices in Business Continuity Management 2024"
- EDUCAUSE — Business Continuity and Disaster Recovery Toolkit (2024)
- CrowdStrike incident analysis (July 2024 — multiple sources)
