---
name: "mdr-745-specialist"
description: EU MDR 2017/745 compliance specialist for medical device classification, technical documentation, clinical evidence, and post-market surveillance. Covers Annex VIII classification rules, Annex II/III technical files, Annex XIV clinical evaluation, Art. 86 PSUR schedules, and EUDAMED integration. Use when classifying a medical device under MDR, building or gap-checking a technical file, planning clinical evaluation or PMS/PSUR cadence, or preparing for notified body review (e.g., 'what class is my device under MDR', 'review my PSUR schedule').
triggers:
  - MDR compliance
  - EU MDR
  - medical device classification
  - Annex VIII
  - technical documentation
  - clinical evaluation
  - PMCF
  - EUDAMED
  - UDI
  - notified body
---

# MDR 2017/745 Specialist

EU MDR compliance patterns for medical device classification, technical documentation, and clinical evidence.

---

## Table of Contents

- [Device Classification Workflow](#device-classification-workflow)
- [Technical Documentation](#technical-documentation)
- [Clinical Evidence](#clinical-evidence)
- [Post-Market Surveillance](#post-market-surveillance)
- [EUDAMED and UDI](#eudamed-and-udi)
- [Reference Documentation](#reference-documentation)
- [Tools](#tools)

---

## Device Classification Workflow

Classify device under MDR Annex VIII:

1. Identify device duration (transient, short-term, long-term)
2. Determine invasiveness level (non-invasive, body orifice, surgical)
3. Assess body system contact (CNS, cardiac, other)
4. Check if active device (energy dependent)
5. Apply classification rules 1-22
6. For software, apply MDCG 2019-11 algorithm
7. Document classification rationale
8. **Validation:** Classification confirmed with Notified Body

### Classification Matrix

| Factor | Class I | Class IIa | Class IIb | Class III |
|--------|---------|-----------|-----------|-----------|
| Duration | Any | Short-term | Long-term | Long-term |
| Invasiveness | Non-invasive | Body orifice | Surgical | Implantable |
| System | Any | Non-critical | Critical organs | CNS/cardiac |
| Risk | Lowest | Low-medium | Medium-high | Highest |

### Software Classification (MDCG 2019-11)

| Information Use | Condition Severity | Class |
|-----------------|-------------------|-------|
| Informs decision | Non-serious | IIa |
| Informs decision | Serious | IIb |
| Drives/treats | Critical | III |

### Classification Examples

**Example 1: Absorbable Surgical Suture**
- Rule 8 (implantable, long-term)
- Duration: > 30 days (absorbed)
- Contact: General tissue
- Classification: **Class IIb**

**Example 2: AI Diagnostic Software**
- Rule 11 + MDCG 2019-11
- Function: Diagnoses serious condition
- Classification: **Class IIb**

**Example 3: Cardiac Pacemaker**
- Rule 8 (implantable)
- Contact: Central circulatory system
- Classification: **Class III**

---

## Technical Documentation

Prepare technical file per Annex II and III:

1. Create device description (variants, accessories, intended purpose)
2. Develop labeling (Article 13 requirements, IFU)
3. Document design and manufacturing process
4. Complete GSPR compliance matrix
5. Prepare benefit-risk analysis
6. Compile verification and validation evidence
7. Integrate risk management file (ISO 14971)
8. **Validation:** Technical file reviewed for completeness

### Technical File Structure

```
ANNEX II TECHNICAL DOCUMENTATION
├── Device description and UDI-DI
├── Label and instructions for use
├── Design and manufacturing info
├── GSPR compliance matrix
├── Benefit-risk analysis
├── Verification and validation
└── Clinical evaluation report
```

### GSPR Compliance Checklist

| Requirement | Evidence | Status |
|-------------|----------|--------|
| Safe design (GSPR 1-3) | Risk management file | ☐ |
| Chemical properties (GSPR 10.1) | Biocompatibility report | ☐ |
| Infection risk (GSPR 10.2) | Sterilization validation | ☐ |
| Software requirements (GSPR 17) | IEC 62304 documentation | ☐ |
| Labeling (GSPR 23) | Label artwork, IFU | ☐ |

### Conformity Assessment Routes

| Class | Route | NB Involvement |
|-------|-------|----------------|
| I | Annex II self-declaration | None |
| Is/Im | Annex II + IX/XI | Sterile/measuring aspects |
| IIa | Annex II + IX or XI | Product or QMS |
| IIb | Annex IX, or Annex X + XI | QMS + tech doc assessment, or type exam + production |
| III | Annex IX, or Annex X + XI | Full QMS + product dossier, or type exam + production |

---

## Clinical Evidence

Develop clinical evidence strategy per Annex XIV:

1. Define clinical claims and endpoints
2. Conduct systematic literature search
3. Appraise clinical data quality
4. Assess equivalence (technical, biological, clinical)
5. Identify evidence gaps
6. Determine if clinical investigation required
7. Prepare Clinical Evaluation Report (CER)
8. **Validation:** CER reviewed by qualified evaluator

### Evidence Requirements by Class

| Class | Minimum Evidence | Investigation |
|-------|------------------|---------------|
| I | Risk-benefit analysis | Not typically required |
| IIa | Literature + post-market | May be required |
| IIb | Systematic literature review | Often required |
| III | Comprehensive clinical data | Required (Article 61) |

### Clinical Evaluation Report Structure

```
CER CONTENTS
├── Executive summary
├── Device scope and intended purpose
├── Clinical background (state of the art)
├── Literature search methodology
├── Data appraisal and analysis
├── Safety and performance conclusions
├── Benefit-risk determination
└── PMCF plan summary
```

### Qualified Evaluator Requirements

- Medical degree or equivalent healthcare qualification
- 4+ years clinical experience in relevant field
- Training in clinical evaluation methodology
- Understanding of MDR requirements

---

## Post-Market Surveillance

Establish PMS system per Chapter VII:

1. Develop PMS plan (Article 84)
2. Define data collection methods
3. Establish complaint handling procedures
4. Create vigilance reporting process
5. Plan Periodic Safety Update Reports (PSUR)
6. Integrate with PMCF activities
7. Define trend analysis and signal detection
8. **Validation:** PMS system audited annually

### PMS System Components

| Component | Requirement | Frequency |
|-----------|-------------|-----------|
| PMS Plan | Article 84 | Maintain current |
| PSUR | Article 86 — Class IIa and higher | Per Art. 86(1) schedule below |
| PMCF Plan | Annex XIV Part B | Update with CER |
| PMCF Report | Annex XIV Part B | Annual (Class III) |
| Vigilance | Articles 87-92 | As events occur |

### PSUR Schedule

| Class | Frequency (MDR Art. 86(1)) |
|-------|-----------------------------|
| Class III | Updated at least annually |
| Class IIb (all, incl. implantable) | Updated at least annually |
| Class IIa | When necessary, at least every 2 years |
| Class I | No PSUR — PMS report instead (Art. 85) |

### Serious Incident Reporting

| Timeline | Requirement |
|----------|-------------|
| 2 days | Serious public health threat |
| 10 days | Death or serious deterioration |
| 15 days | Other serious incidents |

---

## EUDAMED and UDI

Implement UDI system per Article 27:

1. Obtain issuing entity code (GS1, HIBCC, ICCBBA)
2. Assign UDI-DI to each device variant
3. Assign UDI-PI (production identifier)
4. Apply UDI carrier to labels (AIDC + HRI)
5. Register actor in EUDAMED
6. Register devices in EUDAMED
7. Upload certificates when available
8. **Validation:** UDI verified on sample labels

### EUDAMED Modules

| Module | Content | Actor |
|--------|---------|-------|
| Actor | Company registration | Manufacturer, AR |
| UDI/Device | Device and variant data | Manufacturer |
| Certificates | NB certificates | Notified Body |
| Clinical Investigation | Study registration | Sponsor |
| Vigilance | Incident reports | Manufacturer |
| Market Surveillance | Authority actions | Competent Authority |

### UDI Label Requirements

Required elements per Article 13:

- [ ] UDI-DI (device identifier)
- [ ] UDI-PI (production identifier) for Class II+
- [ ] AIDC format (barcode/RFID)
- [ ] HRI format (human-readable)
- [ ] Manufacturer name and address
- [ ] Lot/serial number
- [ ] Expiration date (if applicable)

---

## Reference Documentation

### MDR Classification Guide

`references/mdr-classification-guide.md` contains:

- Complete Annex VIII classification rules (Rules 1-22)
- Software classification per MDCG 2019-11
- Worked classification examples
- Conformity assessment route selection

### Clinical Evidence Requirements

`references/clinical-evidence-requirements.md` contains:

- Clinical evidence framework and hierarchy
- Literature search methodology
- Clinical Evaluation Report structure
- PMCF plan and evaluation report guidance

### Technical Documentation Templates

`references/technical-documentation-templates.md` contains:

- Annex II and III content requirements
- Design History File structure
- GSPR compliance matrix template
- Declaration of Conformity template
- Notified Body submission checklist

---

## Tools

### MDR Gap Analyzer

```bash
# Quick gap analysis
python scripts/mdr_gap_analyzer.py --device "Device Name" --class IIa

# JSON output for integration
python scripts/mdr_gap_analyzer.py --device "Device Name" --class III --output json

# Interactive assessment
python scripts/mdr_gap_analyzer.py --interactive
```

Analyzes device against MDR requirements, identifies compliance gaps, generates prioritized recommendations.

**Output includes:**
- Requirements checklist by category
- Gap identification with priorities
- Critical gap highlighting
- Compliance roadmap recommendations

---

## Notified Body Interface

### Selection Criteria

| Factor | Considerations |
|--------|----------------|
| Designation scope | Covers your device type |
| Capacity | Timeline for initial audit |
| Geographic reach | Markets you need to access |
| Technical expertise | Experience with your technology |
| Fee structure | Transparency, predictability |

### Pre-Submission Checklist

- [ ] Technical documentation complete
- [ ] GSPR matrix fully addressed
- [ ] Risk management file current
- [ ] Clinical evaluation report complete
- [ ] QMS (ISO 13485) certified
- [ ] Labeling and IFU finalized
- [ ] **Validation:** Internal gap assessment complete
