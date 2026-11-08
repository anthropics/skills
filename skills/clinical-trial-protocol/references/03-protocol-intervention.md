# Step 3: Clinical Protocol Intervention Details

## Purpose

This subskill generates the intervention-specific sections (6-7) of a clinical study protocol. It adds detailed intervention administration, dose modifications (if applicable), preparation/handling, randomization/blinding, compliance monitoring, and discontinuation procedures to the protocol foundation.

## Prerequisites

**Required Files:**
- `waypoints/intervention_metadata.json` (must contain `protocol_template` field from Step 2)
- `waypoints/01_clinical_research_summary.json`
- `waypoints/02_protocol_foundation.md` (sections 1-5 from Step 2)
- `waypoints/02_protocol_metadata.json` (must show step_2_status: "completed")

## What This Subskill Does

1. Verifies Step 2 completion
2. Reads protocol template (from metadata) and shared guidance
3. Synthesizes intervention-specific content for Sections 6-7
4. Creates new file `waypoints/03_protocol_intervention.md` with Sections 6-7
5. Updates protocol metadata tracking file

## Execution Flow

### Step 1: Verify Step 2 Completion

Read `waypoints/02_protocol_metadata.json` and verify:
- `step_2_status` is "completed"
- `waypoints/02_protocol_foundation.md` exists (Step 2 output)

**If Step 2 not completed:**
```
Error: Step 2 must be completed before Step 3.
Step 2 status: [current status]

Please complete Step 2 first to generate protocol foundation (Sections 1-6).
```
Exit.

**If Step 2 completed:** Proceed to Step 2.

### Step 2: Read Protocol Template and Shared Guidance

1. Read `waypoints/intervention_metadata.json` to get the `protocol_template` and `template_source` field values
2. **Read the protocol template file:**
   - The path is stored in `protocol_template` field (could be `assets/[name].md` OR a user-provided path)
   - Read the file at that path (focus on Sections 6-7)
   - Note: The `template_source` field indicates whether this is `"directory"` or `"user_provided"` (for logging/debugging only)
3. Read `waypoints/02_protocol_foundation.md` to understand existing context (especially study design, endpoints, and population from Sections 1-5)

**Internalize:**
- Template structure for Sections 6-7
- Content depth targets from shared guidance
- Intervention-specific terminology (device vs drug)
- Dose modification table requirements (for complex drugs)
- Quality principles (comprehensive over brief, specific over generic)

### Step 3: Synthesize Intervention Details Content

Generate Sections 6-7 following template structure, adapted for this specific intervention and indication.

**Use data from:**
- Intervention metadata (intervention type, name, classification, regulatory status)
- Step 1 clinical research summary (similar trials, dosing information, safety profiles)
- Existing protocol draft (study design, endpoints, schedule of activities)

**Follow guidance from:**
- Selected protocol template from Step 2 (structure, regulatory requirements)

---

## Section Generation Instructions

### Section 6: STUDY INTERVENTION (1,000 lines)

This section varies based on intervention complexity.

#### 6.1 Study Intervention(s) Administration (300 lines)

**For DEVICES** (300 lines):

**Device Identification and Regulatory Status** (30 lines):
- Device name (commercial/investigational)
- Manufacturer name and location
- FDA classification: Class I/II/III with product code
- Regulatory status:
  - **If 510(k) cleared:** K-number and clearance date
  - **If De Novo:** DEN-number and classification date
  - **If PMA approved:** P-number and approval date
  - **If investigational:** "Investigational device, IDE application [submitted/pending/approved], IDE number [if applicable]"

**If 510(k) Pathway** (40 lines):
- Predicate device(s): Name, manufacturer
- Predicate 510(k) number (K-number)
- Substantial equivalence rationale:
  - Similar intended use (explain how)
  - Similar technological characteristics (materials, design, energy source)
  - Similar performance data
- Key differences from predicate and justification that differences don't affect safety/effectiveness

**Detailed Device Description** (100 lines):
- Physical characteristics: Size, weight, dimensions, shape
- Materials: List all materials in contact with tissue/blood
- Components and their functions: Describe each major component
- Principle of operation: How the device works at a technical level
- Mechanism of action: How the device achieves its clinical effect
- Power source (if applicable): Battery type, recharging, expected life
- Software/firmware (if applicable): Version, key functions

**Intended Use** (20 lines):
- Intended use per proposed labeling
- Specific indications
- Patient population
- Anatomical location
- Clinical setting

**Instructions for Use Summary** (100 lines):

*Patient Selection per IFU* (20 lines):
- Indications from IFU
- Contraindications from IFU
- Warnings and precautions

*Pre-Procedure Requirements* (30 lines):
- Patient preparation (fasting, medications, positioning)
- Equipment setup and testing
- Sterility requirements
- Anesthesia/sedation requirements

*Procedure Steps* (50 lines):
- Step-by-step implantation/use procedure
- Anatomical landmarks
- Imaging guidance (if applicable)
- Device settings and programming
- Intraoperative testing/verification
- Expected procedure duration

*Post-Procedure Care* (30 lines):
- Immediate post-procedure monitoring
- Hospital stay duration
- Activity restrictions
- Follow-up schedule for device checks
- Patient instructions

*Device Settings/Parameters* (20 lines):
- Programmable settings (if applicable)
- Adjustment procedures
- Optimization protocol

**Device-Specific Training Requirements** (30 lines):
- Investigator training requirements
- Site staff training
- Certification requirements
- Proctoring requirements (if applicable)

---

**For DRUGS/BIOLOGICS** (300 lines):

**Drug Identification and Regulatory Status** (30 lines):
- Drug name: Generic name, trade name (if applicable)
- Manufacturer name and location
- Regulatory status:
  - **If FDA approved:** List approved indications and approval date
  - **If investigational:** "Investigational drug, IND number [if known], IND application [submitted/approved]"

**Formulation Details** (30 lines):
- Dosage form: Tablet, capsule, injection, infusion, etc.
- Strength(s): Available strengths
- Active ingredient(s): Chemical name, quantity per unit
- Excipients: List inactive ingredients
- Appearance: Physical description
- Packaging: How supplied

**Mechanism of Action** (100 lines):
- Biological target: Receptor, enzyme, pathway, cell type
- Drug-target interaction: How drug binds/interacts with target (agonist, antagonist, inhibitor, etc.)
- Downstream cellular effects: Intracellular signaling, gene expression changes, metabolic effects
- Tissue-level effects: How cellular changes manifest at tissue level
- Clinical effects: How mechanism translates to clinical benefit
- Why mechanism is relevant to disease: Connect to disease pathophysiology (from Section 3.2)
- Supporting evidence: Cite preclinical and clinical data

**Pharmacokinetics Summary** (40 lines, if known):
- Absorption: Route-specific bioavailability, Tmax (time to peak concentration), Food effects
- Distribution: Volume of distribution (Vd), Protein binding (%), Tissue distribution
- Metabolism: Metabolizing enzymes (CYP450 isoforms), Active metabolites, Drug-drug interaction potential
- Excretion: Elimination half-life (t1/2), Primary route of elimination (renal/hepatic), Renal/hepatic impairment considerations

**Pharmacodynamics** (30 lines, if known):
- Dose-response relationship
- Time course of effect
- Target engagement biomarkers
- Duration of action

**Dosing Details** (50 lines):

*Dose Specification*:
- Dose amount: [X] mg/kg or fixed dose [Y] mg
- Dose calculation: If weight-based, specify calculation method
  - Body surface area (BSA) cap: Maximum BSA for calculation (e.g., "BSA capped at 2.0 m²")
  - Rounding: Specify rounding rules (e.g., "Round to nearest 10 mg")
- Route of administration: IV, PO, SC, IM, etc.
- Frequency: QD (once daily), BID (twice daily), Q3W (every 3 weeks), etc.
- Duration: Number of cycles or total treatment duration
  - Cycle definition: Define cycle length (e.g., "One cycle = 21 days")
  - Number of cycles: Specify planned number or duration criteria

*Administration Instructions*:
- **If IV:** Infusion preparation, infusion rate/duration, infusion pump requirements, line flushing
- **If PO:** Timing relative to meals, instructions for swallowing (with water, do not crush)
- **If SC:** Injection technique, rotation of injection sites, needle specifications
- Administration schedule: Specify days within cycle (e.g., "Days 1, 8, and 15 of each 21-day cycle")

*Pre-medications* (if required):
- List all required pre-medications
- For each: Drug name, dose, route, timing relative to study intervention
- Rationale: Why pre-medication needed (prevent infusion reactions, nausea, etc.)
- Examples: Antihistamines, antipyretics, antiemetics, corticosteroids

*Supportive Care Medications*:
- Medications to manage expected toxicities
- Growth factors (G-CSF, erythropoietin)
- Prophylactic medications (antiviral, antifungal, PCP prophylaxis)
- Criteria for use

---

#### 6.2 Dose Modifications (IF applicable for drugs - 300 lines)

**NOTE: Only generate this subsection if intervention requires dose modifications (complex chemotherapy, immunotherapy, targeted therapy with known toxicities). For simple interventions, devices, or fixed-dose drugs without modifications, state: "No dose modifications are planned for this study. If unacceptable toxicity occurs, study intervention will be discontinued per Section 7."**

**If dose modifications required:**

**General Principles** (40 lines):
- When to hold intervention: Typically for Grade 3-4 toxicities
- Maximum hold duration: Specify (e.g., "Hold up to 4 weeks for toxicity resolution")
- Dose reduction levels: Can reduce dose up to X levels
- Re-escalation policy: State whether dose can be increased after reduction (typically NO)
- Permanent discontinuation criteria: Conditions requiring permanent stop

**1. Generate Dose Level Table** (20 lines):

| Dose Level | [Drug Name] Dose | % of Starting Dose |
|------------|------------------|---------------------|
| Level 0 (Starting) | [Full dose, e.g., 200 mg] | 100% |
| Level -1 | [Reduced dose, e.g., 150 mg] | 75% |
| Level -2 | [Further reduced, e.g., 100 mg] | 50% |
| Level -3 | Discontinue | 0% |

**2. Generate Dose Modification Tables by Toxicity Category** (200 lines total):

Generate 3-5 tables (one per major toxicity category relevant to the intervention):

**Table: Hematologic Toxicity Dose Modifications** (60 lines):

| Toxicity | CTCAE Grade | Action | Hold Until | Dose Level on Restart | Discontinuation Criteria |
|----------|-------------|--------|-----------|----------------------|--------------------------|
| Neutropenia (ANC) | Grade 3 (0.5-<1.0 × 10^9/L) | Hold intervention | ANC ≥1.5 × 10^9/L | Continue same level if recovery ≤7 days;<br>Reduce 1 level if >7 days | Grade 4 neutropenia after 2 dose reductions |
| Neutropenia (ANC) | Grade 4 (<0.5 × 10^9/L) | Hold intervention | ANC ≥1.5 × 10^9/L | Reduce 1 level | Grade 4 neutropenia recurrence |
| Febrile Neutropenia | Grade 3-4 | Hold, hospitalize, broad-spectrum antibiotics | Afebrile for 48 hrs AND ANC ≥1.5 × 10^9/L | Reduce 1 level;<br>Consider G-CSF prophylaxis | Second occurrence despite G-CSF |
| Thrombocytopenia | Grade 3 (25-<50 × 10^9/L) | Hold intervention | Platelets ≥75 × 10^9/L | Continue same level if recovery ≤7 days;<br>Reduce 1 level if >7 days | Grade 4 thrombocytopenia despite 2 reductions |
| Thrombocytopenia | Grade 4 (<25 × 10^9/L) | Hold intervention | Platelets ≥75 × 10^9/L | Reduce 1 level | Second Grade 4 occurrence |
| Thrombocytopenia with bleeding | Any grade with bleeding | Hold, transfuse as needed | Platelets ≥75 × 10^9/L AND bleeding resolved | Reduce 1 level | Grade 3-4 bleeding despite management |
| Anemia | Grade 3 (Hgb <8 g/dL) | Continue intervention, transfuse PRN | N/A | Continue same level | Persistent Grade 3 anemia despite transfusions |
| Anemia | Grade 4 (life-threatening) | Hold, transfuse | Hgb ≥9 g/dL | Reduce 1 level | Recurrent Grade 4 anemia |

**Table: Hepatic Toxicity Dose Modifications** (40 lines):

| Toxicity | CTCAE Grade | Action | Hold Until | Dose Level on Restart | Discontinuation Criteria |
|----------|-------------|--------|-----------|----------------------|--------------------------|
| ALT/AST elevation | Grade 3 (>5-20× ULN) | Hold intervention | ALT/AST ≤2.5× ULN or baseline | Continue same level if recovery ≤14 days;<br>Reduce 1 level if >14 days | Grade 3-4 recurrence |
| ALT/AST elevation | Grade 4 (>20× ULN) | Hold intervention, monitor closely | ALT/AST ≤2.5× ULN or baseline | Reduce 1 level | Second occurrence |
| Bilirubin elevation | Grade 3 (>3-10× ULN) | Hold intervention | Bilirubin ≤1.5× ULN | Reduce 1 level | Grade 4 bilirubin |
| Bilirubin elevation | Grade 4 (>10× ULN) | Permanently discontinue | N/A | Discontinue | N/A |
| Drug-induced hepatitis | ALT/AST >3× ULN AND bilirubin >2× ULN | Permanently discontinue | N/A | Discontinue | N/A |

**Table: Renal Toxicity Dose Modifications** (40 lines):

| Toxicity | CTCAE Grade or CrCl | Action | Hold Until | Dose Level on Restart | Discontinuation Criteria |
|----------|---------------------|--------|-----------|----------------------|--------------------------|
| Creatinine elevation | Grade 2 (Cr 1.5-3× baseline) | Continue, monitor weekly | N/A | Continue same level | Progression to Grade 3 |
| Creatinine elevation | Grade 3 (Cr >3-6× baseline) | Hold intervention | Cr ≤1.5× baseline or CrCl ≥50 mL/min | Reduce 1 level | Grade 3 recurrence |
| Creatinine elevation | Grade 4 (Cr >6× baseline or dialysis) | Permanently discontinue | N/A | Discontinue | N/A |
| CrCl-based dosing | CrCl 30-50 mL/min | Reduce 1 dose level | N/A | Continue at reduced level | CrCl <30 mL/min |
| CrCl-based dosing | CrCl <30 mL/min | Hold or discontinue | N/A | Hold until CrCl ≥30; Reduce 1 level | Dialysis requirement |

**Table: [Intervention-Specific Toxicity] Dose Modifications** (60 lines):

**For immunotherapy:**
- Immune-related pneumonitis
- Immune-related colitis/diarrhea
- Immune-related hepatitis
- Immune-related endocrinopathies (thyroid, pituitary, adrenal)
- Immune-related dermatitis
- Include management algorithms: Corticosteroid dosing (prednisone 1-2 mg/kg/day), taper schedule, resumption criteria

**For chemotherapy:**
- Peripheral neuropathy (with functional impact grading)
- Ototoxicity
- Cardiotoxicity (with LVEF thresholds)
- Mucositis/stomatitis

**For targeted therapy:**
- Rash/dermatologic toxicity
- Diarrhea
- Hypertension
- Hand-foot syndrome
- Target-specific toxicities

**Example format:**
| Toxicity | CTCAE Grade | Action | Management | Intervention Restart | Discontinuation |
|----------|-------------|--------|------------|---------------------|-----------------|
| Pneumonitis | Grade 2 | Hold intervention | Prednisone 1 mg/kg/day, taper over 4-6 weeks | Resume at reduced level after resolution to Grade ≤1 AND steroid taper complete | Grade 3-4 or Grade 2 recurrence |

**3. General Toxicity Management Guidelines** (100 lines):

**Criteria to Hold Intervention:**
- Any Grade 4 toxicity (except specific exceptions like lab abnormalities without clinical sequelae)
- Grade 3 toxicity that is symptomatic or clinically significant
- Specific organ toxicities at lower grades (specify)
- Inability to manage toxicity with supportive care

**Duration of Hold:**
- Standard hold: Hold until toxicity resolves to Grade ≤1 or baseline
- Maximum hold duration: Specify (e.g., "Maximum 4 weeks")
- If toxicity does not resolve within maximum hold: Permanently discontinue

**Dose Reduction Guidelines:**
- Reduce by one dose level for specified toxicities
- Maximum number of dose reductions: Specify (typically 2-3 levels)
- No dose re-escalation once reduced
- If toxicity recurs at lowest dose level: Permanently discontinue

**Permanent Discontinuation Criteria:**
- Grade 4 toxicity recurrence after dose reduction
- Inability to tolerate lowest dose level
- Specific life-threatening toxicities (list)
- Failure of toxicity to resolve within maximum hold period
- Participant or investigator decision

**Supportive Care Management by Toxicity Type:**
- Hematologic: G-CSF indications, transfusion thresholds
- Gastrointestinal: Antiemetics, antidiarrheals, nutritional support
- Immune-related (for immunotherapy): Corticosteroid protocols, additional immunosuppression
- Organ-specific: Targeted management strategies

**Re-challenge Considerations:**
- Criteria for re-challenging after toxicity resolution
- Conditions where re-challenge is contraindicated

---

#### 6.3 Preparation/Handling/Storage/Accountability (100 lines)

**Acquisition** (20 lines):
- How intervention is obtained: Sponsor provides, commercial source, pharmacy procurement
- Shipping: Temperature controlled, special handling
- Receipt verification: Pharmacy procedures

**Storage Requirements** (30 lines):
- Temperature: Specify range (e.g., "Store at 2-8°C", "Room temperature 20-25°C", "Frozen -20°C")
- Light protection: State if light-sensitive ("Store in original carton to protect from light")
- Humidity considerations
- Storage location: Pharmacy, investigational drug storage area
- Expiration dating: Shelf life, beyond-use dating after reconstitution
- Stability: Stability data supporting storage conditions

**Preparation Instructions** (40 lines):
- Reconstitution (if applicable): Diluent type and volume, mixing instructions, final concentration, stability after reconstitution
- Dilution (if applicable): Final volume, compatible diluents (e.g., 0.9% NaCl, D5W), incompatibilities
- Special handling: Cytotoxic precautions, biohazard handling, personal protective equipment (PPE)
- Preparation area: Biological safety cabinet, sterile compounding area
- Visual inspection: Appearance after preparation, rejection criteria (particulates, discoloration)
- Labeling: Required label elements

**Handling Precautions** (30 lines):
- Cytotoxic precautions (if applicable): NIOSH guidelines, closed-system transfer devices, double gloves, gown
- Biohazard considerations: Bloodborne pathogens, infectious material handling
- Spill management: Spill kit availability, cleanup procedures, reporting
- Personnel training: Training requirements for handling

**Dispensing and Accountability** (30 lines):
- Dispensing process: Pharmacy verification, double-check procedures
- Tracking: Drug accountability logs, subject ID assignment
- Documentation: Date dispensed, quantity, lot number, expiration date
- Return of unused product: Procedures for return, reconciliation
- Destruction: Procedures for expired or unused product destruction
- Audit trail: Record-keeping for regulatory inspection

**Expiration and Stability** (20 lines):
- Expiration dating: Check expiration before dispensing
- Stability after preparation: Use immediately or within X hours
- Temperature excursions: Procedures if storage conditions breached

---

#### 6.4 Measures to Minimize Bias: Randomization and Blinding (50 lines)

**If Randomized:**

**Randomization Method** (20 lines):
- Randomization procedure: Computer-generated randomization schedule, permuted blocks, stratified randomization
- Allocation ratio: 1:1, 2:1, etc.
- Stratification factors (if applicable): List factors (e.g., age <65 vs ≥65, disease stage, site)
- Randomization system: Interactive Web Response System (IWRS), Interactive Voice Response System (IVRS), sealed envelopes (specify method)
- Who performs randomization: Independent statistician, central randomization service, pharmacy
- Timing: When is participant randomized? (after consent and eligibility confirmation, before first dose)

**Randomization Code Security** (10 lines):
- Code storage: Sealed, stored securely
- Access restrictions: Only authorized unblinded personnel

**If Blinded:**

**Blinding Methods** (30 lines):
- Who is blinded: Participants, investigators, outcome assessors, data analysts
- How blinding achieved: Matching placebo (identical appearance), identical packaging, masked labeling
- Labeling: Blinded labels with study ID and randomization number
- Administration: Identical administration procedures for all arms
- Blinding maintenance: Procedures to maintain blinding throughout study

**Unblinding Procedures** (20 lines):
- Emergency unblinding: When permitted (medical emergency requiring knowledge of treatment), how to unblind (24/7 phone line, break-the-seal envelope), documentation required
- Planned unblinding: When does unblinding occur (after database lock, after primary analysis)
- Impact of unblinding: Participant continues or discontinues after emergency unblinding (specify)

**If Open-Label:**

**Justification** (20 lines):
- Why open-label design: Objective endpoint not susceptible to bias, blinding not feasible (e.g., device vs medical therapy), regulatory precedent for indication
- Bias mitigation: Blinded outcome assessment, blinded data analysis

---

#### 6.5 Study Intervention Compliance (30 lines)

**Compliance Monitoring Methods:**
- **For oral medications:** Pill counts (count returned pills), participant diary (daily log), pharmacy dispensing records
- **For IV/injectable:** Direct observation (administered in clinic), infusion logs
- **For devices:** Device interrogation (if applicable), device diary, follow-up assessments
- Pharmacy records review
- IWRS tracking

**Compliance Calculation** (if applicable):
- Formula: (Actual doses taken / Expected doses) × 100%
- For continuous dosing: Compliance = (Days with medication taken / Total days in period) × 100%

**Acceptable Compliance Threshold:**
- Typically ≥80% compliance expected
- Per-protocol population: Participants with ≥80% compliance

**Documentation of Compliance:**
- Record compliance at each visit
- Document reasons for non-compliance
- Review compliance with participant at visits

**Procedures for Non-Compliance:**
- Investigator discusses with participant
- Assess barriers to compliance
- Provide education and support
- If persistent non-compliance: Consider study discontinuation per Section 7

---

#### 6.6 Concomitant Therapy (50 lines)

**Allowed Medications** (20 lines):
- Permitted concomitant medications: Standard of care for underlying disease, supportive care, medications for comorbidities
- Required medications: Specify if any medications must be continued (e.g., "Participants must continue standard of care [specific therapy]")
- Rescue medications: Permitted rescue therapies for breakthrough symptoms
- Over-the-counter medications: Generally permitted unless contraindicated
- Vitamins and supplements: Generally permitted (document)

**Prohibited Medications** (20 lines):
- Specific drugs or drug classes not allowed during study
- Examples:
  - Other investigational agents
  - Chemotherapy (unless specified as combination)
  - Immunosuppressive agents (specify exceptions for immune-related AE management)
  - Strong CYP450 inhibitors/inducers (if drug-drug interactions expected)
  - [List specific drugs relevant to this intervention]
- Washout requirements: If previously taken, specify washout period before enrollment

**Required Standard of Care** (10 lines):
- Medications that must be continued: Specify standard of care that cannot be withheld for ethical reasons
- Background therapy: If study intervention is added to standard of care

**Documentation:**
- All concomitant medications documented at each visit: Drug name, dose, route, frequency, indication, start date, stop date
- Medication changes documented in real-time
- Concomitant medications recorded in eCRF

**Review and Management:**
- Investigator reviews medications at each visit
- Assess for drug-drug interactions
- Assess for prohibited medications
- Document compliance with concomitant therapy restrictions

---

### Section 7: STUDY INTERVENTION DISCONTINUATION AND PARTICIPANT DISCONTINUATION/WITHDRAWAL (80 lines)

Generate three subsections:

#### 7.1 Discontinuation of Study Intervention (30 lines)

Participant stops receiving study intervention but continues in study follow-up.

**Criteria for Discontinuing Intervention:**
- Disease progression: Per protocol-defined criteria (reference Section 9 for assessment)
- Unacceptable toxicity: Toxicity meeting permanent discontinuation criteria (reference Section 7.2 or list specific toxicities)
- Intercurrent illness: Illness or condition preventing safe continuation of intervention
- Investigator decision: Safety concern identified by investigator
- Participant decision: Participant withdraws consent for intervention but agrees to continued follow-up
- Protocol deviation: Major deviation requiring intervention discontinuation
- Pregnancy: Pregnancy detected during study (reference Section 9.3.9)
- Non-compliance: Persistent non-compliance with study intervention (reference Section 7.5)
- Death: Participant dies
- Sponsor decision: Study termination or intervention deemed unsafe

**Procedures After Intervention Discontinuation:**
- Continue study follow-up: Participants continue scheduled visits per Schedule of Activities (Section 2.3)
- Safety follow-up: Continue AE monitoring for 30 days after last dose (or longer for devices/long-acting agents)
- Efficacy assessments: Continue primary and secondary endpoint assessments per protocol
- Survival follow-up: If survival is an endpoint, continue survival status collection
- End-of-treatment visit: Complete end-of-treatment assessments per SoA
- Document reason: Clearly document reason for intervention discontinuation in eCRF

---

#### 7.2 Participant Discontinuation/Withdrawal from the Study (30 lines)

Participant withdraws completely from study (no further participation).

**Criteria for Study Withdrawal:**
- Participant withdraws consent: Participant withdraws consent for all study procedures (no further data collection)
- Lost to follow-up: Unable to contact participant despite documented attempts (see Section 7.3)
- Investigator decision: Safety concern requiring immediate study discontinuation
- Sponsor decision: Entire study terminated
- Death: Participant dies (continue to collect date and cause of death)

**Procedures for Withdrawn Participants:**
- Document reason for withdrawal: Record specific reason in eCRF
- Perform safety assessments if possible: Encourage participant to complete safety follow-up visit
- Collect data up to withdrawal: All data collected prior to withdrawal will be included in analyses
- No replacement: Withdrawn participants are not replaced unless protocol specifies otherwise
- Intent-to-treat analysis: Withdrawn participants included in ITT population

**Withdrawal of Consent:**
- Partial withdrawal: Participant may withdraw from intervention but continue follow-up visits
- Complete withdrawal: No further data collection after withdrawal
- Use of previously collected data: Clarify whether previously collected data may be used (per informed consent)

**Death:**
- Document date and cause: Obtain death certificate or medical records if possible
- Report as SAE: All deaths reported as serious adverse events (Section 9.3.6)
- Continue survival follow-up for other participants

---

#### 7.3 Lost to Follow-Up (20 lines)

**Definition:**
- Lost to follow-up (LTFU): Participant who fails to return for scheduled study visits and cannot be contacted despite documented attempts

**Differentiation:**
- LTFU ≠ Withdrawal: LTFU is passive (cannot contact); withdrawal is active (participant declines)
- Participant is not considered LTFU until all contact attempts exhausted

**Contact Attempt Procedures:**
- Minimum contact attempts: At least 3 documented attempts via different methods
- Contact methods: Phone calls (multiple times, different times of day), certified mail, email (if permitted by IRB), text message (if permitted), contact of emergency contact person (per consent), query site staff/coordinators, check medical records for recent visits
- Documentation: Document each contact attempt (date, time, method, outcome) in study records
- Timing: Attempts made over at least 2-4 weeks

**Reporting:**
- Report to sponsor: Notify sponsor of LTFU
- Report to IRB: Per IRB requirements

**Analysis:**
- ITT population: LTFU participants included in ITT analysis
- Last observation: Use data up to last contact
- Missing data: Handle per statistical analysis plan (Section 10.4.10)

**Do Not:**
- Do not consider participant withdrawn without documented contact attempts
- Do not replace LTFU participants (unless protocol specifies)

---

### Step 4: Create Intervention Details File

**IMPORTANT:** This creates a NEW file with only Sections 6-7.

Create `waypoints/03_protocol_intervention.md` with Sections 6-7 only.

**Procedure:**
1. Generate Section 6 content
2. Generate Section 7 content
3. Write both sections to new file `waypoints/03_protocol_intervention.md`
4. Confirm file creation successful

### Step 5: Update Protocol Metadata

Update `waypoints/02_protocol_metadata.json`:
- Set `step_3_status` to "completed"
- Add sections 7 and 8 to `sections_completed` array
- Update `protocol_status` to "intervention_complete"
- Update notes

**Example:**
```json
{
  "intervention_id": "[from metadata]",
  "intervention_name": "[from metadata]",
  "protocol_version": "1.0 Draft",
  "protocol_date": "[current date]",
  "study_design": "[from Phase 1]",
  "enrollment_target": "[from Phase 1]",
  "primary_endpoint": "[from Section 4]",
  "duration_months": "[from Phase 1 or generated]",
  "regulatory_pathway": "[IDE or IND]",
  "protocol_status": "intervention_complete",
  "step_2_status": "completed",
  "step_3_status": "completed",
  "step_4_status": "pending",
  "sections_completed": [1, 2, 3, 4, 5, 6, 7, 8],
  "sections_pending": [9, 10, 11, 12],
  "notes": [
    "DRAFT for planning purposes",
    "Protocol foundation and intervention details (Sections 1-8) completed",
    "Continue to Step 4 for assessments, statistics, and operations",
    "Requires biostatistician review",
    "Requires IRB approval",
    "Requires FDA feedback",
    "Sponsor TBD items require completion"
  ]
}
```

### Step 6: Display Summary

Display concise summary with:
- Intervention name, protocol version, date
- Step 3 completion status
- Sections completed: 7-8 (Study Intervention, Discontinuation)
- Protocol file updated with size
- DRAFT disclaimer
- Next steps: Review intervention details, continue to Phase 4 for assessments and statistics (Sections 9-12)

**Example output:**
```
✅ Step 3: Intervention Details - COMPLETED

Intervention: [Name]
Protocol: Version 1.0 Draft (2025-12-03)

Sections Completed (7-8):
  ✓ Section 7: Study Intervention
    - Administration procedures and dosing
    - Dose modifications [if applicable]
    - Preparation, handling, storage
    - Randomization and blinding
    - Compliance monitoring
    - Concomitant therapy
  ✓ Section 7: Study Intervention Discontinuation and Participant Discontinuation/Withdrawal

Files Updated:
  • waypoints/03_protocol_intervention.md (appended ~[size]KB, now [total lines] lines)
  • waypoints/02_protocol_metadata.json

Protocol Status: Sections 1-8 complete (Foundation + Intervention)

```

## Output Files

**Created:**
- `waypoints/03_protocol_intervention.md` (Sections 6-7 only, ~1,200 lines)

**Updated:**
- `waypoints/02_protocol_metadata.json` (step 3 marked complete)

**NOT updated yet:**
- `waypoints/intervention_metadata.json` (will be updated after Step 4 completes)
- `waypoints/02_protocol_draft.md` (will be created by Step 4 concatenation)

## Error Handling

**If Phase 2 not completed:**
```
Error: Step 2 must be completed first.
Current status: step_2_status = [status]

Please complete Step 2 to generate protocol foundation (Sections 1-6) before proceeding to Phase 3.
```

**If protocol foundation file missing:**
```
Error: Protocol foundation file not found.
Expected: waypoints/02_protocol_foundation.md

Please run Step 2 first to create the protocol foundation.
```

**If user declines intervention details:**
```
Intervention details skipped at user request.
Step 3 not completed.
User can return to this phase later if needed.
```

**If Step 3 already completed:**
```
Warning: Phase 3 appears to be already completed.
Metadata shows: step_3_status = "completed"

Would you like to:
  1. Skip Step 3 and continue to Phase 4
  2. Regenerate Step 3 (will overwrite Sections 6-7)
  3. Exit
```

## Quality Checks

Before finalizing, verify:
- [ ] Section 6 generated with all required subsections (6.1-6.6)
- [ ] Intervention-specific content (device vs drug terminology used correctly)
- [ ] Dose modifications section appropriate for intervention type
- [ ] Section 7 includes all three subsections (7.1-7.3)
- [ ] Content appended successfully to existing protocol draft
- [ ] Protocol metadata updated correctly
- [ ] Intervention details length: ~1,200 lines (appropriate for complexity)
- [ ] Total protocol now contains Sections 1-7

## Notes

- This subskill generates approximately 1,200 lines of protocol content
- Output stays within token limits by focusing on Sections 6-7 only
- Step 4 will complete the protocol by adding assessments, statistics, and operational content
