# Security Strategy Reference

## 1. Risk-Based Security (Not Compliance-First)

### The Problem with Compliance-First Security
Most startups build security backwards: they get a compliance requirement (SOC 2, ISO 27001) and treat it as the security program. This produces:
- Controls that pass audits but don't reduce actual risk
- Resources allocated to documentation over protection
- Security teams optimizing for auditor satisfaction, not threat reduction
- False confidence ("we passed our audit") before real security exists

**The right order:**
1. Identify your actual threats (what do adversaries want from you?)
2. Identify your crown jewels (what's worth protecting most?)
3. Implement controls that address those threats to those assets
4. Map existing controls to compliance requirements — most overlap naturally

### Risk Identification Framework

**Asset Classification:**
```
Tier 1 — Crown Jewels
├── Customer PII/PHI
├── Payment card data
├── Intellectual property (source code, models, trade secrets)
└── Authentication credentials and secrets

Tier 2 — Business Critical
├── Internal communications (Slack, email)
├── Financial systems and data
├── Employee data
└── Business strategy documents

Tier 3 — Operational
├── Internal tooling and infrastructure configs
├── Non-sensitive operational data
└── Public-facing content and marketing
```

**Threat Actor Profiling:**
| Threat Actor | Motivation | Typical TTPs | Relative Likelihood |
|---|---|---|---|
| Financially motivated criminals | Data theft, ransomware | Phishing, credential stuffing | High |
| Nation-state | IP theft, espionage | Spear phishing, supply chain | Low-Medium (sector-dependent) |
| Insider threat | Financial gain, revenge | Privilege abuse, data exfil | Medium |
| Script kiddies | Notoriety, fun | Known CVEs, scanning | High (low sophistication) |
| Competitors | IP theft | Social engineering, insider recruitment | Low-Medium |

### Risk Quantification (FAIR Model Simplified)

**Annual Loss Expectancy:**
```
ALE = SLE × ARO
SLE (Single Loss Expectancy) = Asset Value × Exposure Factor
ARO (Annual Rate of Occurrence) = historical frequency or industry estimate
```

**Business Impact Categories:**
- **Direct financial loss**: fraud, ransomware payment, theft
- **Regulatory fines**: GDPR (4% global revenue), HIPAA ($100–$50K per violation), PCI DSS
- **Revenue impact**: customer churn post-breach, deal loss during incident, downtime cost
- **Reputational damage**: brand devaluation (harder to quantify, but real)
- **Legal costs**: incident response counsel, class action defense, settlements

**Example Risk Quantification:**

| Risk Scenario | SLE | ARO | ALE |
|---|---|---|---|
| Customer data breach (10K records) | $850K | 0.15 | $127,500/yr |
| Ransomware attack | $350K | 0.20 | $70,000/yr |
| Credential compromise + fraud | $120K | 0.35 | $42,000/yr |
| Third-party SaaS breach | $95K | 0.25 | $23,750/yr |
| Insider data exfiltration | $180K | 0.10 | $18,000/yr |

**Mitigation ROI:**
```
ROSI = (Risk Reduction × ALE) - Control Cost
       ────────────────────────────────────
                  Control Cost

Example: MFA deployment
  Risk reduction: 99% for credential attacks
  ALE reduced: $42,000 × 0.99 = $41,580
  Control cost: $5,000/yr
  ROSI: ($41,580 - $5,000) / $5,000 = 731%
```

---

## 2. Zero Trust Architecture at Strategy Level

### What Zero Trust Actually Means
Zero trust is not a product — it's an architectural principle: **never trust, always verify, assume breach.**

The traditional perimeter model (trust inside the network, distrust outside) fails because:
- Remote work destroyed the perimeter
- Cloud infrastructure has no perimeter
- 80% of breaches involve privileged account abuse (internal trust abused)
- Supply chain attacks compromise trusted software

### Zero Trust Maturity Model

**Stage 1 — Identity-Centric (Start Here)**
- MFA enforced for all users, all applications
- Identity provider (Okta, Azure AD, Google Workspace) as single control plane
- No shared service accounts
- Privileged Access Management (PAM) for admin access
- **Cost:** $20–80K/year | **Timeline:** 3–6 months

**Stage 2 — Device Trust**
- Endpoint detection and response (EDR) on all devices
- Device health checks before granting access
- Mobile device management (MDM) for BYOD
- Certificate-based device authentication
- **Cost:** $30–60K/year additional | **Timeline:** 6–12 months

**Stage 3 — Network Micro-Segmentation**
- Replace VPN with Zero Trust Network Access (ZTNA)
- Segment production from development from corporate
- East-west traffic inspection (not just north-south)
- **Cost:** $40–100K/year additional | **Timeline:** 12–18 months

**Stage 4 — Application-Level Controls**
- Just-in-time access (no standing privileges)
- Workload identity for service-to-service auth
- API gateway with authentication enforcement
- Continuous authorization (not just at login)
- **Cost:** $50–150K/year additional | **Timeline:** 18–30 months

**Strategic Guidance:**
- Don't sell zero trust as a project. It's a 3–5 year direction.
- Start with identity. It gives the most risk reduction per dollar.
- Measure progress by % of access covered by MFA, % of apps behind IdP, privilege account count.

---

## 3. Defense in Depth for Startups

### The Layered Security Model

```
Layer 1: Governance & Policies
  └── Asset inventory, acceptable use, vendor management

Layer 2: Perimeter Controls
  └── WAF, DDoS protection, email security (DMARC/DKIM/SPF)

Layer 3: Identity & Access
  └── MFA, SSO, PAM, just-in-time access, least privilege

Layer 4: Endpoint Security
  └── EDR, device management, patch management

Layer 5: Application Security
  └── SAST/DAST, dependency scanning, code review, API security

Layer 6: Data Protection
  └── Encryption at rest and in transit, DLP, backup/recovery

Layer 7: Detection & Response
  └── SIEM/SOAR, log aggregation, alerting, incident response

Layer 8: Recovery
  └── Backup testing, DR plan, RTO/RPO targets
```

### Startup Security Budget Allocation (Guidance)

| Stage | Annual Revenue | Recommended Security Budget | Priority Spend |
|---|---|---|---|
| Pre-seed/Seed | <$1M | 3–5% opex or $50–100K | MFA, backups, basic EDR |
| Series A | $1–10M | 2–4% revenue | +SIEM, SOC 2 Type I, AppSec |
| Series B | $10–50M | 3–5% revenue | +ZTNA, Red team, dedicated CISO |
| Series C+ | $50M+ | 4–6% revenue | +SOC, threat intelligence, M&A security |

**Non-negotiables regardless of stage:**
1. MFA on everything (particularly email, cloud consoles, code repos)
2. Automated backups with tested restore (ransomware defense)
3. Secrets management (no hardcoded credentials)
4. Dependency vulnerability scanning in CI/CD
5. Incident response plan (even a 2-page doc is better than nothing)

---

## 4. Security Program Maturity Model

**Based on NIST CSF and CMMI, simplified for startup context:**

### Level 1: Initial
- No formal policies
- Reactive security (respond to incidents, not prevent them)
- No dedicated security personnel
- Basic hygiene gaps (unpatched systems, shared passwords)
- **Typical:** Pre-seed, <20 employees

### Level 2: Developing
- Written security policies (even if not fully followed)
- Dedicated security responsibility (often part-time or dual-role)
- MFA deployed, basic asset inventory
- Incident response process documented
- SOC 2 Type I achievable from here in ~6 months
- **Typical:** Series A, 20–50 employees

### Level 3: Defined
- Security integrated into SDLC
- Dedicated security lead or vCISO
- Regular vulnerability scanning and patching
- Security awareness training program
- SOC 2 Type II and ISO 27001 achievable
- **Typical:** Series B, 50–150 employees

### Level 4: Managed
- Risk-based security program with quantified risks
- Security metrics reported to board quarterly
- Threat intelligence program
- Dedicated security team (3–8 people)
- Red team / penetration testing annually
- **Typical:** Series C+, 150–500 employees

### Level 5: Optimized
- Continuous monitoring and automated response
- Proactive threat hunting
- Industry leadership on security (bug bounty, disclosure program)
- Security as competitive advantage in sales
- **Typical:** Public company or regulated enterprise

### Maturity Assessment Questions
1. Can you list all systems that process customer data right now?
2. How long would it take to detect if an admin credential was compromised?
3. When was your last backup tested with a restore?
4. Do developers run any security checks before code is deployed?
5. Does the board receive security reporting? What's in it?

Score: 0 = no/don't know, 1 = partially, 2 = yes/verified
- 0–3: Level 1–2
- 4–7: Level 2–3
- 8–10: Level 3–4

---

## 5. Board-Level Security Reporting

### What the Board Cares About
Boards are not interested in CVE counts or firewall rules. They care about:
1. **Risk posture:** Are we getting better or worse?
2. **Regulatory exposure:** What fines could we face?
3. **Incident readiness:** If we're breached, are we prepared?
4. **Competitive position:** Do customers trust us with their data?
5. **Budget adequacy:** Are we investing appropriately?

### Quarterly Board Security Report Structure

**Executive Summary (1 page max)**
- Security posture score vs. last quarter (directional trend matters more than absolute)
- Top 3 risks and their business impact in dollars
- Key accomplishments this quarter
- Investment requested (if any)

**Risk Dashboard**
```
Risk Register Summary:
├── Critical (>$500K ALE): [count] risks, [count] mitigated
├── High ($100K–$500K ALE): [count] risks, [count] mitigated
├── Medium ($10K–$100K ALE): [count] risks
└── Low (<$10K ALE): [count] risks (for awareness only)

Trend: ↑ Risk exposure vs. Q[n-1] / ↓ Risk exposure vs. Q[n-1]
```

**Compliance Status**
- Framework certifications in scope and current status
- Next audit date
- Any findings from last audit and remediation status

**Incident Summary**
- Security incidents last quarter (count and severity)
- Time to detect / time to respond (vs. targets)
- Any regulatory reporting obligations triggered

**Key Metrics (4–6 max)**
- MFA adoption rate
- Critical patch SLA compliance
- Phishing simulation click rate (trend)
- Vendor assessments completed

**Budget Summary**
- Spend vs. budget
- Headcount
- Next quarter key investments and rationale

### Common Board Questions to Prepare For
- "Have we been breached?" (Know your detection capability, not just your answer)
- "How do we compare to peers?" (Benchmarks from Verizon DBIR, industry ISACs)
- "What's the one thing we should invest in?" (Have a clear answer)
- "If we're acquired, what would security due diligence find?" (Be honest)
- "What keeps you up at night?" (Have a real answer, not a vague one)

---

## 6. Security as Revenue Enabler

### The Sales Angle
For B2B companies, security certifications directly impact revenue:
- Enterprise buyers require SOC 2 as table stakes (increasingly SOC 2 Type II)
- Government and healthcare require ISO 27001 or HIPAA
- Passing security questionnaires faster closes deals faster
- A breach costs 10–30% customer churn; security investment is churn prevention

**How to Measure:**
- Deals blocked by security questionnaire failures (track in CRM)
- Average security questionnaire turnaround time
- Customer security reviews passed vs. failed
- Revenue attributed to new compliance certifications

### The Trust Narrative
Position security certifications in marketing:
- SOC 2 Type II: "Independently audited security controls, verified annually"
- ISO 27001: "Internationally certified information security management"
- HIPAA BAA: "Healthcare data protection to regulatory standards"

These aren't just compliance — they're trust signals that compress the sales cycle.
