# MDR Device Classification Guide

EU MDR 2017/745 Annex VIII classification rules and decision framework.

---

## Table of Contents

- [Classification Overview](#classification-overview)
- [Classification Rules](#classification-rules)
- [Software Classification (MDCG 2019-11)](#software-classification)
- [Classification Examples](#classification-examples)
- [Conformity Assessment Routes](#conformity-assessment-routes)

---

## Classification Overview

### Risk Class Hierarchy

| Class | Risk Level | Examples | NB Required |
|-------|------------|----------|-------------|
| I | Lowest | Bandages, wheelchairs, stethoscopes | No (self-certification) |
| IIa | Low-Medium | Hearing aids, dental filling materials | Yes |
| IIb | Medium-High | Ventilators, blood bags, implantable sutures | Yes |
| III | Highest | Pacemakers, heart valves, hip implants | Yes |

### Classification Factors

Determine class based on:

1. **Duration of contact:**
   - Transient: < 60 minutes
   - Short-term: 60 min to 30 days
   - Long-term: > 30 days

2. **Degree of invasiveness:**
   - Non-invasive
   - Invasive via body orifice
   - Surgically invasive
   - Implantable

3. **Body system interaction:**
   - Central circulatory system
   - Central nervous system
   - Other organ systems

4. **Active vs. passive:**
   - Active devices (energy dependent)
   - Passive devices

---

## Classification Rules

### Non-Invasive Devices (Rules 1-4)

**Rule 1 - General non-invasive:**
- Class I (unless covered by other rules)
- Example: Wheelchairs, hospital beds, collection devices

**Rule 2 - Channeling or storing:**
- Class IIa: Blood bags, transfusion sets (>60 min contact)
- Class IIb: Blood storage, organ storage
- Class I: Simple channeling (gravity, IV bag without additives)

**Rule 3 - Modifying biological composition:**
- Class IIa: Filters, gas separators, dialysis filters
- Class IIb: Blood filtration, exchange transfusion

**Rule 4 - Contact with injured skin:**
- Class I: Wound dressings for superficial wounds
- Class IIa: Wounds in dermis requiring secondary intent healing
- Class IIb: Severe wounds, chronic wounds, burns

### Invasive Devices (Rules 5-8)

**Rule 5 - Body orifice invasive (transient):**
- Class I: Transient use, non-surgically invasive
- Class IIa: Short-term use
- Class IIb: Long-term use in oral cavity

**Rule 6 - Surgically invasive (transient):**
- Class IIa: Transient use
- Exception Class I: Reusable surgical instruments

**Rule 7 - Surgically invasive (short-term):**
- Class IIa: Short-term (< 30 days)
- Class IIb: Central circulatory or CNS contact
- Class III: Chemical change or drug delivery

**Rule 8 - Implantable and long-term surgically invasive:**
- Class IIb: General implants
- Class III: Heart, CNS, spine contact; drug delivery; biological origin

### Active Devices (Rules 9-13)

**Rule 9 - Active therapeutic devices:**
- Class IIa: Exchange or admin of energy (non-hazardous)
- Class IIb: Potentially hazardous energy levels

**Rule 10 - Active diagnostic devices:**
- Class IIa: Supply energy for imaging, monitoring
- Class IIb: Monitor vital physiological parameters

**Rule 11 - Software:**
- Class IIa: Information for diagnostic/therapeutic decisions (non-serious)
- Class IIb: Decisions that could cause death/irreversible deterioration
- Class III: Decisions with immediate risk to life
- See MDCG 2019-11 for detailed algorithm

**Rule 12 - Active devices administering substances:**
- Class IIa: Non-hazardous manner
- Class IIb: Potentially hazardous manner

**Rule 13 - Other active devices:**
- Class I: All other active devices

### Special Rules (Rules 14-22)

**Rule 14 - Contraception/STI prevention:**
- Class IIb: Contraceptive devices
- Class III: Implantable contraceptives

**Rule 15 - Disinfection/sterilization:**
- Class IIa: Disinfection of devices
- Class IIb: Disinfection of invasive devices

**Rule 16 - X-ray diagnostic recording:**
- Class IIa: Recording media for x-ray

**Rule 17 - Devices with nanomaterials:**
- Class III: High internal exposure potential
- Class IIb: Medium exposure
- Class IIa: Low exposure

**Rule 18 - Blood/plasma derivatives:**
- Class III: Utilizing blood derivatives

**Rule 19 - Drug delivery systems:**
- Class III: Integral drug administration

**Rule 20 - Breath analyzers for anesthesia:**
- Class IIb: Breath analyzers

**Rule 21 - Medicinal substance devices:**
- Class III: Incorporating medicinal substances

**Rule 22 - Closed-loop therapeutic systems:**
- Class III: Closed-loop systems

---

## Software Classification

### MDCG 2019-11 Decision Algorithm

Execute software classification:

1. Determine if software qualifies as medical device
2. Identify significance of information to healthcare decision
3. Assess healthcare situation or patient condition
4. Apply rule 11 based on severity
5. **Validation:** Classification rationale documented with MDCG reference

### Software Classification Matrix

| Information Significance | Situation/Condition | Class |
|--------------------------|---------------------|-------|
| Informs clinical management | Non-serious | IIa |
| Informs clinical management | Serious | IIb |
| Informs clinical management | Critical | III |
| Drives clinical management | Non-serious | IIa |
| Drives clinical management | Serious | IIb |
| Drives clinical management | Critical | III |
| Treats or diagnoses | Non-serious | IIa |
| Treats or diagnoses | Serious | IIb |
| Treats or diagnoses | Critical | III |

### Software Examples

| Software Type | Class | Rationale |
|---------------|-------|-----------|
| Patient record viewing | Not MD | Administrative, not clinical |
| Medication reminder app | Class I | General wellness |
| Blood glucose monitor app | Class IIa | Informs non-serious decisions |
| Sepsis detection algorithm | Class IIb | Informs serious condition |
| AI tumor detection | Class III | Diagnoses critical condition |
| Closed-loop insulin delivery | Class III | Treats critical condition |

---

## Classification Examples

### Example 1: Surgical Suture (Absorbable)

```
Device: Absorbable suture for internal wound closure
Analysis:
- Invasiveness: Surgically invasive
- Duration: Long-term (absorbed over > 30 days)
- System: General tissue (not CNS, not cardiac)
- Rule Applied: Rule 8 (implantable, long-term)

Classification: Class IIb
Rationale: Implantable device > 30 days, general tissue
Conformity Route: Annex IX (Type examination) + Annex XI
```

### Example 2: Blood Pressure Monitor

```
Device: Home blood pressure monitoring device
Analysis:
- Active: Yes (electronic measurement)
- Function: Monitoring vital physiological parameter
- Risk: Non-immediate (home use, not ICU)
- Rule Applied: Rule 10 (active diagnostic)

Classification: Class IIa
Rationale: Monitors vital parameter, non-critical setting
Conformity Route: Annex IX or XI (QMS + product verification)
```

### Example 3: Hip Implant

```
Device: Total hip replacement prosthesis
Analysis:
- Invasiveness: Surgically invasive, implantable
- Duration: Long-term (permanent)
- System: Musculoskeletal
- Rule Applied: Rule 8 (implantable, long-term)

Classification: Class III
Rationale: Implantable > 30 days in direct contact with bone
Conformity Route: Annex IX + Annex X (full QMS + type examination)
```

### Example 4: Diagnostic Software (AI)

```
Device: AI-based chest X-ray analysis for pneumonia detection
Analysis:
- Software: Qualifies as medical device (clinical decision)
- Information: Diagnoses condition
- Condition: Serious (pneumonia can be life-threatening)
- Rule Applied: Rule 11 + MDCG 2019-11

Classification: Class IIb
Rationale: Software diagnosing serious condition
Conformity Route: Annex IX or Annex XI
```

---

## Conformity Assessment Routes

### By Device Class

| Class | Conformity Route | NB Involvement |
|-------|------------------|----------------|
| I | Annex II (self-declaration) | None |
| I (sterile/measuring) | Annex II + IX/XI | Sterile/measuring aspects |
| IIa | Annex II + IX or XI | Product verification or QMS |
| IIb | Annex IX + X or Annex X + XI | Type exam + QMS or production |
| III | Annex IX + X | Full QMS + type examination |

### Annex Reference

| Annex | Content | Purpose |
|-------|---------|---------|
| II | Technical documentation | Required for all classes |
| III | Technical documentation (additions) | Class III additions |
| IX | Conformity assessment (QMS) | Quality management route |
| X | Type examination | Product design examination |
| XI | Product verification | Production quality checks |

### Decision Workflow

Select conformity route:

1. Determine device classification (Rules 1-22)
2. Identify applicable annexes for class
3. Evaluate QMS maturity (Annex IX capability)
4. Consider production volume (batch vs. mass)
5. Assess Notified Body capacity and timeline
6. Select optimal conformity assessment route
7. **Validation:** Route confirmed with Notified Body consultation
