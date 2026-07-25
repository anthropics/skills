---
name: "regulatory-affairs-head"
description: Senior Regulatory Affairs Manager for HealthTech and MedTech companies. Prepares FDA 510(k), De Novo, and PMA submission packages; analyzes regulatory pathways for new medical devices; drafts responses to FDA deficiency letters and Notified Body queries; develops CE marking technical documentation under EU MDR 2017/745; coordinates multi-market approval strategies across FDA, EU, Health Canada, PMDA, and NMPA; and maintains regulatory intelligence on evolving standards. Use when users need to plan or execute FDA submissions, navigate 510(k) or PMA approval processes, achieve CE marking, prepare pre-submission meeting materials, write regulatory strategy documents, respond to agency queries, or manage compliance documentation for medical device market access.
triggers:
  - regulatory strategy
  - FDA submission
  - EU MDR
  - 510(k)
  - PMA approval
  - CE marking
  - regulatory pathway
  - market access
  - clinical evidence
  - regulatory intelligence
  - submission planning
  - notified body
---

# Head of Regulatory Affairs

Regulatory strategy development, submission management, and global market access for medical device organizations.

---

## Table of Contents

- [Regulatory Strategy Workflow](#regulatory-strategy-workflow)
- [FDA Submission Workflow](#fda-submission-workflow)
- [EU MDR Submission Workflow](#eu-mdr-submission-workflow)
- [Global Market Access Workflow](#global-market-access-workflow)
- [Regulatory Intelligence Workflow](#regulatory-intelligence-workflow)
- [Decision Frameworks](#decision-frameworks)
- [Tools and References](#tools-and-references)

---

## Regulatory Strategy Workflow

Develop regulatory strategy aligned with business objectives and product characteristics.

### Workflow: New Product Regulatory Strategy

1. Gather product information:
   - Intended use and indications
   - Device classification (risk level)
   - Technology platform
   - Target markets and timeline
2. Identify applicable regulations per target market:
   - FDA (US): 21 CFR Part 820, 510(k)/PMA/De Novo
   - EU: MDR 2017/745, Notified Body requirements
   - Other markets: Health Canada, PMDA, NMPA, TGA
3. Determine optimal regulatory pathway:
   - Compare submission types (510(k) vs De Novo vs PMA)
   - Assess predicate device availability
   - Evaluate clinical evidence requirements
4. Develop regulatory timeline with milestones
5. Estimate resource requirements and budget
6. Identify regulatory risks and mitigation strategies
7. Obtain stakeholder alignment and approval
8. **Validation:** Strategy document approved; timeline accepted; resources allocated

### Regulatory Pathway Selection Matrix

| Factor | 510(k) | De Novo | PMA |
|--------|--------|---------|-----|
| Predicate Available | Yes | No | N/A |
| Risk Level | Low-Moderate | Low-Moderate | High |
| Clinical Data | Usually not required | May be required | Required |
| Review Time | 90 days (MDUFA) | 150 days | 180 days |
| User Fee | ~$22K (2024) | ~$135K | ~$440K |
| Best For | Me-too devices | Novel low-risk | High-risk, novel |

### Regulatory Strategy Document Template

```
REGULATORY STRATEGY

Product: [Name]   Version: [X.X]   Date: [Date]

1. PRODUCT OVERVIEW
   Intended use: [One-sentence statement of intended patient population, body site, and clinical purpose]
   Device classification: [Class I / II / III]
   Technology: [Brief description, e.g., "AI-powered wound-imaging software, SaMD"]

2. TARGET MARKETS & TIMELINE
   | Market | Pathway        | Priority | Target Date |
   |--------|----------------|----------|-------------|
   | USA    | 510(k) / PMA   | 1        | Q1 20XX     |
   | EU     | Class [X] MDR  | 2        | Q2 20XX     |

3. REGULATORY PATHWAY RATIONALE
   FDA: [510(k) / De Novo / PMA] — Predicate: [K-number or "none"]
   EU:  Class [X] via [Annex IX / X / XI] — NB: [Name or TBD]
   Rationale: [2–3 sentences on key factors driving pathway choice]

4. CLINICAL EVIDENCE STRATEGY
   Requirements: [Summarize what each market needs, e.g., "510(k): bench + usability; EU Class IIb: PMCF study"]
   Approach: [Literature review / Prospective study / Combination]

5. RISKS AND MITIGATION
   | Risk                         | Prob | Impact | Mitigation                        |
   |------------------------------|------|--------|-----------------------------------|
   | Predicate delisted by FDA    | Low  | High   | Identify secondary predicate now  |
   | NB audit backlog             | Med  | Med    | Engage NB 6 months before target  |

6. RESOURCE REQUIREMENTS
   Budget: $[Amount]   Personnel: [FTEs]   External: [Consultants / CRO]
```

---

## FDA Submission Workflow

Prepare and submit FDA regulatory applications.

### Workflow: 510(k) Submission

1. Confirm 510(k) pathway suitability:
   - Predicate device identified (note K-number, e.g., K213456)
   - Substantial equivalence (SE) argument supportable on intended use and technological characteristics
   - No new intended use or technology concerns triggering De Novo
2. Schedule and conduct Pre-Submission (Q-Sub) meeting if needed (see [Pre-Sub Decision](#pre-submission-meeting-decision))
3. Compile submission package checklist:
   - [ ] Cover letter with device name, product code, and predicate K-number
   - [ ] Section 1: Administrative information (applicant, contact, 510(k) type)
   - [ ] Section 2: Device description — include photos, dimensions, materials list
   - [ ] Section 3: Intended use and indications for use
   - [ ] Section 4: Substantial equivalence comparison table (see example below)
   - [ ] Section 5: Performance testing — protocols, standards cited, pass/fail results
   - [ ] Section 6: Biocompatibility summary (ISO 10993-1 risk assessment, if patient contact)
   - [ ] Section 7: Software documentation (IEC 62304 level, cybersecurity per FDA guidance, if applicable)
   - [ ] Section 8: Labeling — final draft IFU, device label
   - [ ] Section 9: Summary and conclusion
4. Conduct internal review and quality check against FDA RTA checklist
5. Prepare eCopy per FDA format requirements (PDF bookmarked, eCopy cover page)
6. Submit via FDA ESG portal with user fee payment
7. Monitor MDUFA clock and respond to AI/RTA requests within deadlines
8. **Validation:** Submission accepted; MDUFA date received; tracking system updated

#### Substantial Equivalence Comparison Example

| Characteristic | Predicate (K213456) | Subject Device | Same? | Notes |
|----------------|---------------------|----------------|-------|-------|
| Intended use | Wound measurement | Wound measurement | ✓ | Identical |
| Technology | 2D camera | 2D + AI analysis | ✗ | New TC; address below |
| Energy type | Non-energized | Non-energized | ✓ | |
| Patient contact | No | No | ✓ | |
| SE conclusion | New TC does not raise new safety/effectiveness questions; bench data demonstrates equivalent accuracy (±2mm vs ±3mm predicate) |

### Workflow: PMA Submission

1. Confirm PMA pathway:
   - Class III device or no suitable predicate
   - Clinical data strategy defined
2. Complete IDE clinical study if required:
   - IDE approval
   - Clinical protocol execution
   - Study report completion
3. Conduct Pre-Submission meeting
4. Compile PMA submission checklist:
   - [ ] Volume I: Administrative, device description, manufacturing
   - [ ] Volume II: Nonclinical studies (bench, animal, biocompatibility)
   - [ ] Volume III: Clinical studies (IDE protocol, data, statistical analysis)
   - [ ] Volume IV: Labeling
   - [ ] Volume V: Manufacturing information, sterilization
5. Submit original PMA application
6. Address FDA questions and deficiencies
7. Prepare for FDA facility inspection
8. **Validation:** PMA approved; approval letter received; post-approval requirements documented

### FDA Submission Timeline

| Milestone | 510(k) | De Novo | PMA |
|-----------|--------|---------|-----|
| Pre-Sub Meeting | Day -90 | Day -90 | Day -120 |
| Submission | Day 0 | Day 0 | Day 0 |
| RTA Review | Day 15 | Day 15 | Day 45 |
| Substantive Review | Days 15–90 | Days 15–150 | Days 45–180 |
| Decision | Day 90 | Day 150 | Day 180 |

### Common FDA Deficiencies and Prevention

| Category | Common Issues | Prevention |
|----------|---------------|------------|
| Substantial Equivalence | Weak predicate comparison; no performance data | Build SE table with data column; cite recognized standards |
| Performance Testing | Incomplete protocols; missing worst-case rationale | Follow FDA-recognized standards; document worst-case justification |
| Biocompatibility | Missing endpoints; no ISO 10993-1 risk assessment | Complete ISO 10993-1 matrix before testing |
| Software | Inadequate hazard analysis; no cybersecurity bill of materials | IEC 62304 compliance + FDA cybersecurity guidance checklist |
| Labeling | Inconsistent claims vs. IFU; missing symbols standard | Cross-check label against IFU; cite ISO 15223-1 for symbols |

See: [references/fda-submission-guide.md](references/fda-submission-guide.md)

---

## EU MDR Submission Workflow

Achieve CE marking under EU MDR 2017/745.

### Workflow: MDR Technical Documentation

1. Confirm device classification per MDR Annex VIII
2. Select conformity assessment route based on class:
   - Class I: Self-declaration
   - Class IIa/IIb: Notified Body involvement
   - Class III: Full NB assessment
3. Select and engage Notified Body (for Class IIa+) — see selection criteria below
4. Compile Technical Documentation per Annex II checklist:
   - [ ] Annex II §1: Device description, intended purpose, UDI
   - [ ] Annex II §2: Design and manufacturing information (drawings, BoM, process flows)
   - [ ] Annex II §3: GSPR checklist — each requirement mapped to evidence (standard, test report, or justification)
   - [ ] Annex II §4: Benefit-risk analysis and risk management file (ISO 14971)
   - [ ] Annex II §5: Product verification and validation (test reports)
   - [ ] Annex II §6: Post-market surveillance plan
   - [ ] Annex XIV: Clinical evaluation report (CER) — literature, clinical data, equivalence justification
5. Establish and document QMS per ISO 13485
6. Submit application to Notified Body
7. Address NB questions and coordinate audit
8. **Validation:** CE certificate issued; Declaration of Conformity signed; EUDAMED registration complete

#### GSPR Checklist Row Example

| GSPR Ref | Requirement | Standard / Guidance | Evidence Document | Status |
|----------|-------------|---------------------|-------------------|--------|
| Annex I §1 | Safe design and manufacture | ISO 14971:2019 | Risk Management File v2.1 | Complete |
| Annex I §11.1 | Devices with measuring function ±accuracy | EN ISO 15223-1 | Performance Test Report PT-003 | Complete |
| Annex I §17 | Cybersecurity | MDCG 2019-16 | Cybersecurity Assessment CS-001 | In progress |

### Clinical Evidence Requirements by Class

| Class | Clinical Requirement | Documentation |
|-------|---------------------|---------------|
| I | Clinical evaluation (CE) | CE report |
| IIa | CE with literature focus | CE report + PMCF plan |
| IIb | CE with clinical data | CE report + PMCF + clinical study (some) |
| III | CE with clinical investigation | CE report + PMCF + clinical investigation |

### Notified Body Selection Criteria

- **Scope:** Designated for your specific device category
- **Capacity:** Confirmed availability within target timeline
- **Experience:** Track record with your technology type
- **Geography:** Proximity for on-site audits
- **Cost:** Fee structure transparency
- **Communication:** Responsiveness and query turnaround

See: [references/eu-mdr-submission-guide.md](references/eu-mdr-submission-guide.md)

---

## Global Market Access Workflow

Coordinate regulatory approvals across international markets.

### Workflow: Multi-Market Submission Strategy

1. Define target markets based on business priorities
2. Sequence markets for efficient evidence leverage:
   - Phase 1: FDA + EU (reference markets)
   - Phase 2: Recognition markets (Canada, Australia)
   - Phase 3: Major markets (Japan, China)
   - Phase 4: Emerging markets
3. Identify local requirements per market:
   - Clinical data acceptability
   - Local agent/representative needs
   - Language and labeling requirements
4. Develop master technical file with localization plan
5. Establish in-country regulatory support
6. Execute parallel or sequential submissions
7. Track approvals and coordinate launches
8. **Validation:** All target market approvals obtained; registration database updated

### Market Priority Matrix

| Market | Size | Complexity | Recognition | Priority |
|--------|------|------------|-------------|----------|
| USA | Large | High | N/A | 1 |
| EU | Large | High | N/A | 1–2 |
| Canada | Medium | Medium | MDSAP | 2 |
| Australia | Medium | Low | EU accepted | 2 |
| Japan | Large | High | Local clinical | 3 |
| China | Large | Very High | Local testing | 3 |
| Brazil | Medium | High | GMP inspection | 3–4 |

### Documentation Efficiency Strategy

| Document Type | Single Source | Localization Required |
|---------------|---------------|----------------------|
| Technical file core | Yes | Format adaptation |
| Risk management | Yes | None |
| Clinical data | Yes | Bridging assessment |
| QMS certificate | Yes (ISO 13485) | Market-specific audit |
| Labeling | Master label | Translation, local requirements |
| IFU | Master content | Translation, local symbols |

See: [references/global-regulatory-pathways.md](references/global-regulatory-pathways.md)

---

## Regulatory Intelligence Workflow

Monitor and respond to regulatory changes affecting product portfolio.

### Workflow: Regulatory Change Management

1. Monitor regulatory sources:
   - FDA Federal Register, guidance documents
   - EU Official Journal, MDCG guidance
   - Notified Body communications
   - Industry associations (AdvaMed, MedTech Europe)
2. Assess relevance to product portfolio
3. Evaluate impact:
   - Timeline to compliance
   - Resource requirements
   - Product changes needed
4. Develop compliance action plan
5. Communicate to affected stakeholders
6. Implement required changes
7. Document compliance status
8. **Validation:** Compliance action plan approved; changes implemented on schedule

### Regulatory Monitoring Sources

| Source | Type | Frequency |
|--------|------|-----------|
| FDA Federal Register | Regulations, guidance | Daily |
| FDA Device Database | 510(k), PMA, recalls | Weekly |
| EU Official Journal | MDR/IVDR updates | Weekly |
| MDCG Guidance | EU implementation | As published |
| ISO/IEC | Standards updates | Quarterly |
| Notified Body | Audit findings, trends | Per interaction |

### Impact Assessment Template

```
REGULATORY CHANGE IMPACT ASSESSMENT

Change: [Description]   Source: [Regulation/Guidance]
Effective Date: [Date]  Assessment Date: [Date]  Assessed By: [Name]

AFFECTED PRODUCTS
| Product | Impact (H/M/L) | Action Required        | Due Date |
|---------|----------------|------------------------|----------|
| [Name]  | [H/M/L]        | [Specific action]      | [Date]   |

COMPLIANCE ACTIONS
1. [Action] — Owner: [Name] — Due: [Date]
2. [Action] — Owner: [Name] — Due: [Date]

RESOURCE REQUIREMENTS: Budget $[X]  |  Personnel [X] hrs

APPROVAL: Regulatory _____________ Date _______ / Management _____________ Date _______
```

---

## Decision Frameworks

### Pathway Selection and Classification Reference

**FDA Pathway Selection**

```
Is predicate device available?
            │
        Yes─┴─No
         │     │
         ▼     ▼
    Is device   Is risk level
    substantially  Low-Moderate?
    equivalent?       │
         │        Yes─┴─No
     Yes─┴─No      │     │
      │     │      ▼     ▼
      ▼     ▼   De Novo  PMA
    510(k)  Consider      required
           De Novo
           or PMA
```

**EU MDR Classification**

```
Is the device active?
        │
    Yes─┴─No
     │     │
     ▼     ▼
Is it an   Does it contact
implant?   the body?
  │            │
Yes─┴─No   Yes─┴─No
 │    │     │     │
 ▼    ▼     ▼     ▼
III  IIb  Check   Class I
         contact  (measuring/
         type     sterile if
         and      applicable)
         duration
```

### Pre-Submission Meeting Decision

| Factor | Schedule Pre-Sub | Skip Pre-Sub |
|--------|------------------|--------------|
| Novel Technology | ✓ | |
| New Intended Use | ✓ | |
| Complex Testing | ✓ | |
| Uncertain Predicate | ✓ | |
| Clinical Data Needed | ✓ | |
| Well-established | | ✓ |
| Clear Predicate | | ✓ |
| Standard Testing | | ✓ |

### Regulatory Escalation Criteria

| Situation | Escalation Level | Action |
|-----------|------------------|--------|
| Submission rejection | VP Regulatory | Root cause analysis, strategy revision |
| Major deficiency | Director | Cross-functional response team |
| Timeline at risk | Management | Resource reallocation review |
| Regulatory change | VP Regulatory | Portfolio impact assessment |
| Safety signal | Executive | Immediate containment and reporting |

---

## Tools and References

### Scripts

| Tool | Purpose | Usage |
|------|---------|-------|
| [regulatory_tracker.py](scripts/regulatory_tracker.py) | Track submission status and timelines | `python regulatory_tracker.py` |

**Regulatory Tracker Features:**
- Track multiple submissions across markets
- Monitor status and target dates
- Identify overdue submissions
- Generate status reports

**Example usage:**
```bash
$ python regulatory_tracker.py --report status
Submission Status Report — 2024-11-01
┌──────────────────┬──────────┬────────────┬─────────────┬──────────┐
│ Product          │ Market   │ Type       │ Target Date │ Status   │
├──────────────────┼──────────┼────────────┼─────────────┼──────────┤
│ WoundScan Pro    │ USA      │ 510(k)     │ 2024-12-01  │ On Track │
│ WoundScan Pro    │ EU       │ MDR IIb    │ 2025-03-01  │ At Risk  │
│ CardioMonitor X1 │ Canada   │ Class II   │ 2025-01-15  │ On Track │
└──────────────────┴──────────┴────────────┴─────────────┴──────────┘
1 submission at risk: WoundScan Pro EU — NB engagement not confirmed.
```

### References

| Document | Content |
|----------|---------|
| [fda-submission-guide.md](references/fda-submission-guide.md) | FDA pathways, requirements, review process |
| [eu-mdr-submission-guide.md](references/eu-mdr-submission-guide.md) | MDR classification, technical documentation, clinical evidence |
| [global-regulatory-pathways.md](references/global-regulatory-pathways.md) | Canada, Japan, China, Australia, Brazil requirements |
| [iso-regulatory-requirements.md](references/iso-regulatory-requirements.md) | ISO 13485, 14971, 10993, IEC 62304, 62366 requirements |

### Key Performance Indicators

| KPI | Target | Calculation |
|-----|--------|-------------|
| First-time approval rate | >85% | (Approved without major deficiency / Total submitted) × 100 |
| On-time submission | >90% | (Submitted by target date / Total submissions) × 100 |
| Review cycle compliance | >95% | (Responses within deadline / Total requests) × 100 |
| Regulatory hold time | <20% | (Days on hold / Total review days) × 100 |

---

## Related Skills

| Skill | Integration Point |
|-------|-------------------|
| [mdr-745-specialist](../mdr-745-specialist/) | Detailed EU MDR technical requirements |
| [fda-consultant-specialist](../fda-consultant-specialist/) | FDA submission deep expertise |
| [quality-manager-qms-iso13485](../quality-manager-qms-iso13485/) | QMS for regulatory compliance |
| [risk-management-specialist](../risk-management-specialist/) | ISO 14971 risk management |
