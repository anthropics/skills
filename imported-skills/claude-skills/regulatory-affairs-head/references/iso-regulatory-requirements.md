# ISO Regulatory Requirements for Medical Devices

Key ISO standards applicable to medical device development, quality management, and regulatory compliance.

---

## Table of Contents

- [ISO 13485 Quality Management](#iso-13485-quality-management)
- [ISO 14971 Risk Management](#iso-14971-risk-management)
- [ISO 10993 Biocompatibility](#iso-10993-biocompatibility)
- [IEC 62304 Software Lifecycle](#iec-62304-software-lifecycle)
- [IEC 62366 Usability Engineering](#iec-62366-usability-engineering)
- [ISO 11607 Packaging Validation](#iso-11607-packaging-validation)
- [Sterilization Standards](#sterilization-standards)
- [Standards Cross-Reference](#standards-cross-reference)

---

## ISO 13485 Quality Management

### ISO 13485:2016 Overview

| Aspect | Requirement |
|--------|-------------|
| Scope | QMS for design, development, production, installation, and servicing |
| Certification | Third-party certification required for most markets |
| Regulatory Status | Harmonized under EU MDR; recognized by FDA QSIT |
| Validity | 3-year certification cycle with annual surveillance |

### Key Clause Requirements

| Clause | Title | Regulatory Focus |
|--------|-------|------------------|
| 4.1 | General Requirements | Process-based QMS, outsourcing control |
| 4.2 | Documentation | Quality Manual, procedures, records |
| 5.1-5.6 | Management Responsibility | Policy, planning, review |
| 6.1-6.4 | Resource Management | Competence, infrastructure, environment |
| 7.1 | Planning | Risk management integration |
| 7.2 | Customer-Related | Requirements determination and review |
| 7.3 | Design and Development | Design controls (critical for FDA) |
| 7.4 | Purchasing | Supplier controls |
| 7.5 | Production | Process validation, identification, traceability |
| 7.6 | Monitoring Equipment | Calibration |
| 8.2 | Monitoring | Feedback, complaints, audits |
| 8.3 | Nonconforming Product | Control and disposition |
| 8.5 | Improvement | CAPA |

### Design Control Requirements (Clause 7.3)

| Stage | Clause | Deliverables |
|-------|--------|--------------|
| Planning | 7.3.2 | Design plan, stages, responsibilities |
| Inputs | 7.3.3 | Requirements specification |
| Outputs | 7.3.4 | Design specifications, acceptance criteria |
| Review | 7.3.5 | Design review records |
| Verification | 7.3.6 | Verification testing reports |
| Validation | 7.3.7 | Validation protocols and reports |
| Transfer | 7.3.8 | Transfer verification records |
| Changes | 7.3.9 | Change control records |

### Regulatory Mapping

| Regulation | ISO 13485 Recognition |
|------------|----------------------|
| EU MDR 2017/745 | Harmonized standard (presumption of conformity) |
| FDA 21 CFR 820 | Substantially equivalent; QSIT alignment |
| Health Canada | MDSAP or direct recognition |
| PMDA Japan | Recognized with MHLW certification |
| TGA Australia | Accepted as conformity evidence |
| ANVISA Brazil | Required for GMP compliance |

---

## ISO 14971 Risk Management

### ISO 14971:2019 Overview

| Aspect | Requirement |
|--------|-------------|
| Scope | Risk management throughout medical device lifecycle |
| Regulatory Status | Harmonized under EU MDR; referenced by FDA |
| Key Change (2019) | Enhanced benefit-risk analysis emphasis |
| Documentation | Risk management file required |

### Risk Management Process

| Stage | Activities | Outputs |
|-------|------------|---------|
| Planning | Define scope, responsibilities, criteria | Risk management plan |
| Risk Analysis | Identify hazards, estimate risk | Hazard analysis, risk estimation |
| Risk Evaluation | Compare against acceptability criteria | Risk evaluation records |
| Risk Control | Select and implement controls | Risk control measures |
| Residual Risk | Evaluate remaining risk | Residual risk evaluation |
| Risk-Benefit | Assess overall benefit-risk | Benefit-risk analysis |
| Review | Periodic risk management review | Risk management report |

### Risk Analysis Methods

| Method | Application | Standard Reference |
|--------|-------------|-------------------|
| FMEA | Component/process failure modes | IEC 60812 |
| FTA | System-level failure analysis | IEC 61025 |
| HAZOP | Process hazard identification | IEC 61882 |
| PHA | Preliminary hazard assessment | - |

### Risk Acceptability Matrix

| Severity | Probability | Risk Level | Action |
|----------|-------------|------------|--------|
| Catastrophic | Frequent | Unacceptable | Design change required |
| Critical | Probable | ALARP | Risk reduction required |
| Serious | Occasional | ALARP | Risk reduction if practicable |
| Minor | Remote | Acceptable | Monitor |
| Negligible | Improbable | Acceptable | Document |

### Post-Production Risk Management

| Activity | Frequency | Sources |
|----------|-----------|---------|
| Complaint Analysis | Continuous | Customer complaints |
| Vigilance Review | Continuous | Adverse event reports |
| Literature Review | Annual | Scientific publications |
| Standards Review | Annual | Updated standards |
| Risk File Update | As needed | New information |

---

## ISO 10993 Biocompatibility

### ISO 10993-1:2018 Biological Evaluation Framework

| Contact Type | Duration | Required Tests |
|--------------|----------|----------------|
| Surface - Skin | Limited (<24h) | Cytotoxicity, sensitization, irritation |
| Surface - Mucosal | Prolonged (24h-30d) | + Acute systemic toxicity |
| Surface - Breached | Permanent (>30d) | + Subchronic toxicity, genotoxicity |
| External Communicating | Limited | Cytotoxicity, sensitization, irritation, hemolysis |
| External Communicating | Prolonged | + Subchronic toxicity, implantation |
| External Communicating | Permanent | + Chronic toxicity, carcinogenicity |
| Implant | Limited | Full biological evaluation |
| Implant | Prolonged/Permanent | Comprehensive testing including implantation |

### Key Test Standards

| Standard | Test |
|----------|------|
| ISO 10993-3 | Genotoxicity, carcinogenicity, reproductive toxicity |
| ISO 10993-4 | Hemocompatibility |
| ISO 10993-5 | Cytotoxicity (in vitro) |
| ISO 10993-6 | Local effects after implantation |
| ISO 10993-10 | Irritation and skin sensitization |
| ISO 10993-11 | Systemic toxicity |
| ISO 10993-12 | Sample preparation and reference materials |
| ISO 10993-18 | Chemical characterization |

### Biocompatibility Evaluation Workflow

1. Define device contact nature and duration
2. Identify materials in contact with body
3. Perform chemical characterization (ISO 10993-18)
4. Conduct gap analysis against required endpoints
5. Plan and execute required testing
6. Document biological evaluation report
7. Update for material or design changes
8. **Validation:** All endpoints addressed; testing per GLP; BE report complete

---

## IEC 62304 Software Lifecycle

### IEC 62304:2006/AMD1:2015 Overview

| Aspect | Requirement |
|--------|-------------|
| Scope | Medical device software development lifecycle |
| Regulatory Status | Harmonized under EU MDR; FDA guidance reference |
| Key Concept | Safety classification drives rigor |
| Documentation | Software development plan, architecture, testing |

### Software Safety Classification

| Class | Definition | Documentation Rigor |
|-------|------------|---------------------|
| A | No injury or damage possible | Basic |
| B | Non-serious injury possible | Moderate |
| C | Death or serious injury possible | High |

### Required Processes by Class

| Process | Class A | Class B | Class C |
|---------|---------|---------|---------|
| Software Development Planning | Required | Required | Required |
| Software Requirements Analysis | Required | Required | Required |
| Software Architecture Design | - | Required | Required |
| Software Detailed Design | - | - | Required |
| Software Unit Implementation | Required | Required | Required |
| Software Unit Verification | - | Required | Required |
| Software Integration Testing | Required | Required | Required |
| Software System Testing | Required | Required | Required |
| Software Release | Required | Required | Required |
| Software Maintenance | Required | Required | Required |
| Software Risk Management | Required | Required | Required |
| Software Configuration Management | Required | Required | Required |
| Software Problem Resolution | Required | Required | Required |

### Documentation Requirements

| Document | Class A | Class B | Class C |
|----------|---------|---------|---------|
| Software Development Plan | ✓ | ✓ | ✓ |
| Software Requirements Specification | ✓ | ✓ | ✓ |
| Software Architecture Document | - | ✓ | ✓ |
| Software Detailed Design | - | - | ✓ |
| Software Unit Test Records | - | ✓ | ✓ |
| Integration Test Records | ✓ | ✓ | ✓ |
| System Test Records | ✓ | ✓ | ✓ |
| Traceability Matrix | - | ✓ | ✓ |

---

## IEC 62366 Usability Engineering

### IEC 62366-1:2015 Overview

| Aspect | Requirement |
|--------|-------------|
| Scope | Usability engineering process for medical devices |
| Regulatory Status | Harmonized under EU MDR; FDA HFE guidance |
| Key Concept | Use-related risk identification and mitigation |
| Documentation | Usability engineering file |

### Usability Engineering Process

| Stage | Activities | Outputs |
|-------|------------|---------|
| Use Specification | Define users, use environments, user interface | Use specification document |
| User Interface Design | Design UI with task analysis input | UI specifications |
| Hazard Analysis | Identify use-related hazards | Use-related risk analysis |
| Formative Evaluation | Iterative design testing | Formative evaluation reports |
| Summative Evaluation | Final design validation | Summative evaluation report |
| Documentation | Compile usability engineering file | UEF |

### Usability Testing Requirements

| Test Type | Purpose | Participants |
|-----------|---------|--------------|
| Formative | Identify usability issues during design | Representative users (5-8 per iteration) |
| Summative | Validate final design | Representative users (15+ per user group) |
| Simulated Use | Test under realistic conditions | Trained users in simulated environment |
| Actual Use | Validate in clinical setting | Actual users in actual environment |

### Usability Engineering File Contents

| Section | Content |
|---------|---------|
| Use Specification | User profiles, use environments, user interface |
| Use-Related Risk Analysis | Hazard identification, risk evaluation |
| UI Design Specifications | Design requirements, rationale |
| Formative Evaluation | Test protocols, results, design changes |
| Summative Evaluation | Validation protocol, results, conclusions |
| Residual Risk | Remaining use-related risks |

---

## ISO 11607 Packaging Validation

### ISO 11607-1:2019 and ISO 11607-2:2019

| Part | Scope |
|------|-------|
| Part 1 | Requirements for materials, sterile barrier systems, packaging systems |
| Part 2 | Validation requirements for forming, sealing, and assembly processes |

### Packaging Validation Stages

| Stage | Activities | Documentation |
|-------|------------|---------------|
| IQ | Equipment installation verification | Installation records |
| OQ | Process parameter verification | OQ protocol and report |
| PQ | Performance under production conditions | PQ protocol and report |

### Required Testing

| Test | Standard | Purpose |
|------|----------|---------|
| Seal Strength | ASTM F88 | Peel strength measurement |
| Seal Integrity | ASTM F2095 | Bubble leak test |
| Visual Inspection | ISO 11607-1 | Defect identification |
| Package Integrity | ASTM D4169 | Distribution simulation |
| Accelerated Aging | ASTM F1980 | Shelf life validation |
| Real-Time Aging | - | Stability confirmation |

### Shelf Life Validation

| Method | Approach | Considerations |
|--------|----------|----------------|
| Accelerated Aging | Q10 = 2 (typically) | Per ASTM F1980 |
| Real-Time Aging | Concurrent with accelerated | Required for final claim |
| Worst-Case Testing | Post-aging integrity testing | Distribution + storage conditions |

---

## Sterilization Standards

### Common Sterilization Methods

| Method | Standard | Applications |
|--------|----------|--------------|
| EO (Ethylene Oxide) | ISO 11135:2014 | Heat/moisture sensitive |
| Steam | ISO 17665-1:2006 | Heat/moisture tolerant |
| Radiation | ISO 11137:2017 | Heat sensitive, high volume |
| Dry Heat | ISO 20857:2010 | Moisture sensitive |
| Aseptic Processing | ISO 13408 | Prefilled syringes |

### Sterilization Validation Requirements

| Phase | Activities | Documentation |
|-------|------------|---------------|
| IQ | Equipment installation | Installation records |
| OQ | Process parameter qualification | OQ protocol and report |
| PQ | Microbiological performance | Bioburden, SAL demonstration |
| Routine Control | Process monitoring | Batch records, BI results |

### Sterility Assurance Level (SAL)

| SAL | Probability of Non-Sterile | Application |
|-----|----------------------------|-------------|
| 10⁻⁶ | 1 in 1 million | Most medical devices |
| 10⁻³ | 1 in 1,000 | Aseptically processed |

---

## Standards Cross-Reference

### Regulatory Alignment

| Standard | EU MDR | FDA | Health Canada | TGA |
|----------|--------|-----|---------------|-----|
| ISO 13485 | Harmonized | Recognized | Required | Accepted |
| ISO 14971 | Harmonized | Referenced | Required | Accepted |
| ISO 10993 | Harmonized | Referenced | Required | Accepted |
| IEC 62304 | Harmonized | Referenced | Required | Accepted |
| IEC 62366 | Harmonized | Referenced | Required | Accepted |

### Version Requirements

| Standard | Current Version | Transition Deadline |
|----------|-----------------|---------------------|
| ISO 13485 | 2016 | Active |
| ISO 14971 | 2019 | Active |
| ISO 10993-1 | 2018 | Active |
| IEC 62304 | 2006/Amd1:2015 | Active |
| IEC 62366-1 | 2015/Amd1:2020 | Active |

### Certification Bodies

| Region | Certification Body Type |
|--------|------------------------|
| EU | Notified Bodies (per MDR) |
| USA | FDA-recognized accreditation bodies |
| MDSAP | Authorized auditing organizations |
| Global | ISO certification bodies (IATF, DNV, BSI, TÜV) |
