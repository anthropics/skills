# Dispute Resolution & Business Insurance Reference

## Arbitration Clauses

### Why Arbitration
- Private, confidential proceedings (vs. public court filings)
- Generally faster than litigation (18 months vs. 3–5 years for complex commercial cases)
- Arbitrator expertise in commercial/tech matters
- More limited discovery (reduces cost)
- Difficult to appeal (awards confirmed unless fraud, corruption, manifest disregard of law)
- Enforced internationally under New York Convention (164 signatory countries)

### AAA vs. JAMS

**American Arbitration Association (AAA):**
- Largest arbitration provider in the US; extensive case administrator network
- Commercial Rules: for business-to-business disputes
- Consumer Arbitration Rules: mandatory for consumer disputes if company uses AAA
- Mass Arbitration rules: apply at 25+ similar claims by coordinated counsel; replaces individual filing fees with single $11,250 initiation charge ($8,125 from company + balance from consumer); then $325/case for first 500
- Filing fees for commercial: scale with claim amount ($1,750–$10,000+)

**JAMS (Judicial Arbitration and Mediation Services):**
- Smaller roster of arbitrators (typically more experienced/senior judges)
- More expensive per hour but often faster overall
- Mass arbitration rules: threshold is 75+ similar claims by individually represented claimants using same/coordinated counsel
- Higher minimum fees than AAA

**Drafting the arbitration clause:**
```
Any dispute arising out of or relating to this Agreement shall be resolved by 
binding arbitration before [AAA/JAMS] under its [Commercial Arbitration Rules / 
JAMS Comprehensive Rules], before a single arbitrator. The arbitration shall be 
conducted in [City, State]. Judgment on the award may be entered in any court 
of competent jurisdiction.
```

**Key clause decisions:**
- Seat of arbitration (determines procedural law; choose Delaware or NY for commercial)
- Number of arbitrators (1 for <$1M disputes; 3 for larger)
- Governing law (separate from seat — typically Delaware or NY law)
- Discovery limitations (incorporate rules' default or specify)
- Interim relief: allow parties to seek emergency injunctive relief in court even during arbitration

### Class Action Waivers
- **Enforceability**: upheld by US Supreme Court (AT&T Mobility LLC v. Concepcion, 2011; Epic Systems Corp. v. Lewis, 2018 for employment disputes)
- California Public Injunctions: CA courts have held PAGA (Private Attorneys General Act) representative actions cannot be waived in arbitration — pending further legal developments
- **Mass arbitration risk**: class waiver + mandatory arbitration = mass individual filings if plaintiff bar organizes (thousands of individual $X claims); coordinated mass arbitration can cost companies $50M+; carefully draft to minimize exposure or negotiate bellwether/batching provisions

### Jurisdiction Selection
- **Choice of law**: almost universally enforceable if reasonable relationship to transaction (Delaware law for corporate matters; New York for financial/commercial contracts)
- **Forum selection**: courts generally enforce (Atlantic Marine Construction v. U.S. District Court, 2013 — defendants can enforce forum selection clauses)
- **Venue strategies**: defendant-friendly: arbitration in favorable jurisdiction; plaintiff-friendly: courts closer to customers
- **International**: arbitration under ICC, LCIA, or Singapore IAC rules for cross-border contracts; avoid designating US courts for international disputes (foreign judgment enforcement issues)

### Limitation of Liability Interaction with Dispute Resolution
- Ensure limitation of liability clause and dispute resolution clause work together
- Arbitrator generally cannot award damages beyond contractual cap unless fraud, willful misconduct, or specific statutory rights
- Include explicit statement that arbitrator is bound by agreement's limitation of liability provisions

---

## Business Insurance for Tech Companies

### Essential Insurance Stack

**Directors & Officers Liability (D&O)**
- Covers: wrongful acts by directors and officers in their capacity; securities claims; derivative suits; regulatory investigations
- Side A: covers individual directors/officers when company cannot indemnify
- Side B: reimburses company for indemnifying directors/officers
- Side C: entity coverage (for securities claims)
- When needed: before any board with outside directors; VC investors typically require before investment; mandatory for publicly traded companies
- Cost for startups: $3,000–$15,000/yr for $1M–$5M limit
- Key trigger events: fundraising disputes, M&A disagreements, IPO-related claims, employment disputes, regulatory investigations

**Technology Errors & Omissions (Tech E&O)**
- Covers: claims arising from software performance failures, errors in SaaS delivery, system downtime, data loss caused by vendor errors
- Distinction from general E&O: tech E&O specifically covers technology services; general professional liability covers advisory services
- When needed: before first enterprise customer; many enterprise contracts require evidence of E&O
- Cost: $2,000–$20,000/yr for $1M–$5M limit
- Key coverage: defense costs + damages; often combined with Cyber policy

**Cyber Liability**
- Covers: data breach response costs (forensics, notification, credit monitoring), regulatory fines and penalties, ransomware payments, third-party liability from data breach, business interruption from cyber events
- First-party vs. third-party: first-party = company's own costs; third-party = liability to customers/partners
- Cost: $5,000–$100,000+/yr depending on revenue, data types, and security posture; healthcare/fintech data = significantly higher premiums
- Key requirements for coverage: MFA deployed, EDR (endpoint detection and response), backups tested, incident response plan, security training
- Post-breach: insurer typically provides breach coach, forensic firm, legal counsel, PR firm; do NOT notify anyone before contacting insurer (may void coverage)
- Note: most policies exclude nation-state attacks (war exclusion) and unencrypted stolen laptops may not be covered if policy requires encryption

**Employment Practices Liability Insurance (EPLI)**
- Covers: wrongful termination, discrimination, harassment, retaliation, failure to hire, wage and hour class actions (limited)
- When needed: as you hire employees; California especially high-litigation state
- Cost: $1,000–$10,000/yr for startups based on headcount
- Deductible: typically $10,000–$50,000/claim

**General Liability**
- Covers: bodily injury, property damage, personal injury at company facilities; advertising injury (copyright infringement in ads)
- Usually required in office leases
- Cost: $400–$2,000/yr

**Workers' Compensation**
- Required in nearly every state once you have employees
- Rates vary by job classification and state; office workers: 0.1–0.3% of payroll/yr
- Exclusive remedy doctrine: generally prevents employees from suing employer for workplace injuries

**Product Liability** (if hardware/IoT)
- Covers: physical harm caused by product defects
- More expensive if product has safety-critical applications

### Coverage Gaps to Watch For
- **Bodily injury from software**: standard CGL policies exclude "professional services" — tech E&O fills this gap
- **Crypto/digital asset theft**: most cyber policies exclude; specialty coverage needed
- **Employee theft of customer data for personal gain**: typically cyber, not fidelity bond
- **Vendor breach**: your cyber policy typically covers your breach; if vendor breaches and affects you, depends on contract indemnification + your "dependent systems" coverage
- **Regulatory investigations**: D&O investigative costs covered; actual fines typically not covered by D&O (but costs of responding are)

---

## Litigation Cost Management

### Billing Structure Options
- **Hourly**: standard for most commercial litigation; $300–$1,000+/hr depending on firm size and market
- **Contingency**: plaintiff-side; attorney gets 25–40% of recovery; rare for B2B disputes
- **Flat fee**: specific tasks (drafting, brief writing); good for predictable scope
- **Retainer/monthly cap**: common for ongoing outside counsel relationships
- **Alternative fee arrangements (AFAs)**: success fees, blended rates, holdbacks

### Cost-Benefit Analysis Framework
Before litigating:
1. Estimated total cost to conclusion ($100K–$5M+ for complex commercial)
2. Probability of success (× expected recovery)
3. Business disruption: management time, document production, depositions
4. Confidentiality: public filings vs. arbitration
5. Relationship impact: can you still work with this party after?
6. Deterrence value: message to others

### Pre-Litigation Steps
1. Cease and desist letter (sends notice; can establish damages knowledge date; may resolve without litigation)
2. Demand letter with settlement demand
3. Mediation (JAMS/AAA mediators; $5,000–$30,000/session for mediator; high settlement rate)
4. Arbitration (if required by contract or agreed)
5. Litigation (last resort)

### Insurance for Litigation Funding
**Legal expense insurance**: some D&O and E&O policies cover prosecution of IP infringement claims (not just defense); check carefully.
**Third-party litigation funding**: commercial litigation funders (Burford Capital, Validity Finance) will fund commercial IP and contract claims in exchange for portion of recovery; non-recourse if case loses; requires strong merits and size ($5M+ damages typical threshold).
