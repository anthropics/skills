# Step 2: Clinical Protocol Foundation

## Purpose

This subskill generates a **title page** and the foundation sections (1-6) of a clinical study protocol. It creates the protocol framework including a formal title page, compliance statements, study summary, introduction, objectives, design, and population criteria.

## Prerequisites

**Required Files:**
- `waypoints/intervention_metadata.json`
- `waypoints/01_clinical_research_summary.json`
- At least one protocol template (`.md` file) in the `assets/` directory

## What This Subskill Does

1. Reads intervention metadata and clinical research summary
2. Reads NIH template and shared guidance
3. Generates formal protocol title page with regulatory identifiers
4. Synthesizes intervention-specific protocol content for Sections 1-6
5. Writes protocol foundation (title page + Sections 1-6) to waypoint file (creates new file)
6. Creates protocol metadata tracking file

## Execution Flow

### Step 1: Load Previous Waypoints

Read all required files:
- `waypoints/intervention_metadata.json` (including initial_context if provided)
- `waypoints/01_clinical_research_summary.json`

### Step 2: Discover and Select Protocol Template

**PRIORITY 1: Check for user-provided template from Step 0**

1. Read `waypoints/intervention_metadata.json` and check the `user_provided_template` field
2. **If `user_provided_template.provided` is `true`:**
   - User has already provided a custom template
   - Verify the file exists and is readable at `user_provided_template.file_path`
   - If file is valid, use it as the template
   - Store in metadata: `"protocol_template": "[user_provided_template.file_path]"`
   - Store template source: `"template_source": "user_provided"`
   - Display: "✓ Using custom template: [file_name]"
   - **Skip to Step 3**

**PRIORITY 2: Check assets/ directory**

3. List all `.md` files in the `assets/` directory
4. **If exactly one template found:** Use it automatically
   - Store: `"protocol_template": "assets/[name].md"`, `"template_source": "directory"`
5. **If multiple templates found:** Present list to user
   - Ask: "Multiple templates found. Please select: [list templates with numbers]"
   - Store selected: `"protocol_template": "assets/[selected].md"`, `"template_source": "directory"`
6. **If no templates found AND no user-provided template:** Display error and exit

**Store the template selection in `waypoints/intervention_metadata.json`:**
```json
{
  "protocol_template": "assets/[name].md" or "[user-provided-path]",
  "template_source": "directory" or "user_provided"
}
```

### Step 3: Read Protocol Template and Shared Guidance

1. Read the selected protocol template file from Step 2 in its entirety

**Internalize:**
- NIH template structure for Sections 1-6
- Content depth targets from shared guidance
- Quality principles (comprehensive over brief, specific over generic)
- Intervention-specific terminology (device vs drug)
- Table formatting guidelines
- **CRITICAL: Extract the exact Table of Contents structure from the template (lines 188-368) and include it verbatim in the generated protocol after the Title Page**

### Step 4: Generate Protocol Title Page

Generate formal title page (see Title Page section below) with:
- Metadata table with protocol title, NCT number placeholder, document date
- Protocol identifier and product name
- Confidentiality statement
- Sponsor information
- Full protocol title
- Regulatory identifiers (IND/IDE number)
- Footer with version and confidentiality marking

### Step 5: Synthesize Protocol Foundation Content

Generate Sections 1-6 following template structure, adapted for this specific intervention and indication.

**Use data from:**
- Intervention metadata (intervention type, name, indication, initial context)
- Step 1 clinical research summary (similar trials, FDA guidance, disease background, recommended design)

**Follow guidance from:**
- Selected protocol template from Step 2 (structure, regulatory requirements)

---

## Section Generation Instructions

### Title Page (Protocol Cover Page) (30 lines)

**Generate a formal protocol title page** similar to industry-standard protocols (e.g., pharmaceutical company protocols). This page appears BEFORE Section 1.

**Content to Generate:**

1. **Metadata Table** (5 lines):
   Create a simple markdown table with key protocol identifiers:
   ```
   |Official Protocol Title:|[Full protocol title from synopsis]|
   |---|---|
   |**NCT Number:**|[TBD - to be assigned upon ClinicalTrials.gov registration]|
   |**Document Date:**|[Current date in DD-MMM-YYYY format]|
   ```

2. **Protocol Identifier** (3 lines):
   - Protocol number/code (if sponsor has format, otherwise use: `PROTO-[InterventionAcronym]-[Indication]-001`)
   - Product name or device name
   - Protocol/Amendment number (e.g., "Protocol No.: 001-00" for initial version)

3. **Confidentiality Statement** (5 lines):
   - State confidentiality of protocol document
   - Example: "THIS PROTOCOL AND ALL OF THE INFORMATION RELATING TO IT ARE CONFIDENTIAL AND PROPRIETARY PROPERTY OF [SPONSOR NAME]."
   - Adapt based on whether academic, NIH, or industry-sponsored

4. **Sponsor Information** (10 lines):
   - **SPONSOR:** [Institution or Company Name]
   - (hereafter referred to as the Sponsor or [Abbreviation])
   - Full address (if known, otherwise use "[Institution Address]")
   - Contact information statement (e.g., "Protocol-specific Sponsor Contact information can be found in the Investigator Trial File Binder (or equivalent).")

5. **Full Title** (5 lines):
   - **TITLE:**
   - [Full protocol title - same as in synopsis table]

6. **Regulatory Identifiers** (5 lines):
   - **For drugs:** "**IND NUMBER:** [TBD or if known]"
   - **For devices:** "**IDE NUMBER:** [TBD or if known]"
   - **If international:** "**EudraCT NUMBER:** [TBD or if applicable]"
   - Other relevant regulatory identifiers

7. **Footer** (2 lines):
   - Protocol identifier with version and date
   - Confidentiality marking (e.g., "Confidential")

**Formatting Notes:**
- Use bold (**text**) for section labels like **SPONSOR:**, **TITLE:**, **IND NUMBER:**
- Leave blank lines between major sections for readability
- Center-align or left-align based on preference (markdown doesn't enforce centering, but structure should be clear)
- Use placeholder text [TBD] for items not yet determined (NCT number, IND/IDE number)

---
**Table of Contents - Use the below table of contents exactly!**

STATEMENT OF COMPLIANCE

1 PROTOCOL SUMMARY
   1.1 Synopsis
   1.2 Schema
   1.3 Schedule of Activities (SoA)
2 INTRODUCTION
   2.1 Study Rationale
   2.2 Background
   2.3 Risk/Benefit Assessment
   2.3.1 Known Potential Risks
   2.3.2 Known Potential Benefits
   2.3.3 Assessment of Potential Risks and Benefits
3 OBJECTIVES AND ENDPOINTS
4 STUDY DESIGN
   4.1 Overall Design
   4.2 Scientific Rationale for Study Design
   4.3 Justification for Dose
   4.4 End of Study Definition
5 STUDY POPULATION
   5.1 Inclusion Criteria
   5.2 Exclusion Criteria
   5.3 Lifestyle Considerations
   5.4 Screen Failures
   5.5 Strategies for Recruitment and Retention
6 STUDY INTERVENTION
   6.1 Study Intervention(s) Administration
      6.1.1 Study Intervention Description
      6.1.2 Dosing and Administration
   6.2 Preparation/Handling/Storage/Accountability
      6.2.1 Acquisition and accountability
      6.2.2 Formulation, Appearance, Packaging, and Labeling
      6.2.3 Product Storage and Stability
      6.2.4 Preparation
   6.3 Measures to Minimize Bias: Randomization and Blinding
   6.4 Study Intervention Compliance
   6.5 Concomitant Therapy
      6.5.1 Rescue Medicine
7 STUDY INTERVENTION DISCONTINUATION AND PARTICIPANT DISCONTINUATION/WITHDRAWAL
   7.1 Discontinuation of Study Intervention
   7.2 Participant Discontinuation/Withdrawal from the Study
   7.3 Lost to Follow-Up
8 STUDY ASSESSMENTS AND PROCEDURES
   8.1 Efficacy Assessments
   8.2 Safety and Other Assessments
   8.3 Adverse Events and Serious Adverse Events
      8.3.1 Definition of Adverse Events (AE)
      8.3.2 Definition of Serious Adverse Events (SAE)
      8.3.3 Classification of an Adverse Event
      8.3.4 Time Period and Frequency for Event Assessment and Follow-Up
      8.3.5 Adverse Event Reporting
      8.3.6 Serious Adverse Event Reporting
      8.3.7 Reporting Events to Participants
      8.3.8 Events of Special Interest
      8.3.9 Reporting of Pregnancy
8.4 Unanticipated Problems
   8.4.1 Definition of Unanticipated Problems (UP)
   8.4.2 Unanticipated Problem Reporting
   8.4.3 Reporting Unanticipated Problems to Participants
9 STATISTICAL CONSIDERATIONS
   9.1 Statistical Hypotheses
   9.2 Sample Size Determination
   9.3 Populations for Analyses
   9.4 Statistical Analyses
      9.4.1 General Approach
      9.4.2 Analysis of the Primary Efficacy Endpoint(s)
      9.4.3 Analysis of the Secondary Endpoint(s)
      9.4.4 Safety Analyses
      9.4.5 Baseline Descriptive Statistics
      9.4.6 Planned Interim Analyses
      9.4.7 Sub-Group Analyses
      9.4.8 Tabulation of Individual participant Data
      9.4.9 Exploratory Analyses
10 SUPPORTING DOCUMENTATION AND OPERATIONAL CONSIDERATIONS
   10.1 Regulatory, Ethical, and Study Oversight Considerations
      10.1.1 Informed Consent Process
      10.1.2 Study Discontinuation and Closure
      10.1.3 Confidentiality and Privacy
      10.1.4 Future Use of Stored Specimens and Data
      10.1.5 Key Roles and Study Governance
      10.1.6 Safety Oversight
      10.1.7 Clinical Monitoring
      10.1.8 Quality Assurance and Quality Control
      10.1.9 Data Handling and Record Keeping
      10.1.10 Protocol Deviations
      10.1.11 Publication and Data Sharing Policy
      10.1.12 Conflict of Interest Policy
   10.2 Additional Considerations
   10.3 Abbreviations
   10.4 Protocol Amendment History
11 REFERENCES
---

### STATEMENT OF COMPLIANCE (50 lines)

**Content to Generate:**

STATEMENT OF COMPLIANCE
Provide a statement that the trial will be conducted in compliance with the protocol, International Conference on Harmonisation Good Clinical Practice (ICH GCP) and applicable state, local and federal regulatory requirements. Each engaged institution must have a current Federal-Wide Assurance (FWA) issued by the Office for Human Research Protections (OHRP) and must provide this protocol and the associated informed consent documents and recruitment materials for review and approval by an appropriate Institutional Review Board (IRB) or Ethics Committee (EC) registered with OHRP. Any amendments to the protocol or consent materials must also be approved before implementation. Select one of the two statements below: 

(1)	[The trial will be carried out in accordance with International Conference on Harmonisation Good Clinical Practice (ICH GCP) and the following: 

•	United States (US) Code of Federal Regulations (CFR) applicable to clinical studies (45 CFR Part 46, 21 CFR Part 50, 21 CFR Part 56, 21 CFR Part 312, and/or 21 CFR Part 812) 

National Institutes of Health (NIH)-funded investigators and clinical trial site staff who are responsible for the conduct, management, or oversight of NIH-funded clinical trials have completed Human Subjects Protection and ICH GCP Training.

The protocol, informed consent form(s), recruitment materials, and all participant materials will be submitted to the Institutional Review Board (IRB) for review and approval.  Approval of both the protocol and the consent form must be obtained before any participant is enrolled.  Any amendment to the protocol will require review and approval by the IRB before the changes are implemented to the study.  In addition, all changes to the consent form will be IRB-approved; a determination will be made regarding whether a new consent needs to be obtained from participants who provided consent, using a previously approved consent form.]

OR

(2)	[The trial will be conducted in accordance with International Conference on Harmonisation Good Clinical Practice (ICH GCP), applicable United States (US) Code of Federal Regulations (CFR), and the <specify NIH Institute or Center (IC) > Terms and Conditions of Award. The Principal Investigator will assure that no deviation from, or changes to the protocol will take place without prior agreement from the Investigational New Drug (IND) or Investigational Device Exemption (IDE) sponsor, funding agency and documented approval from the Institutional Review Board (IRB), except where necessary to eliminate an immediate hazard(s) to the trial participants. All personnel involved in the conduct of this study have completed Human Subjects Protection and ICH GCP Training.

The protocol, informed consent form(s), recruitment materials, and all participant materials will be submitted to the IRB for review and approval.  Approval of both the protocol and the consent form must be obtained before any participant is enrolled.  Any amendment to the protocol will require review and approval by the IRB before the changes are implemented to the study.  All changes to the consent form will be IRB approved; a determination will be made regarding whether a new consent needs to be obtained from participants who provided consent, using a previously approved consent form.]


---

### Section 1: PROTOCOL SUMMARY (150 lines)

This section contains three major components. Generate each with appropriate detail.

#### Section 1.1: Synopsis (50 lines)

**Generate a comprehensive synopsis table** with the following rows (use two-column format: Field | Content):

1. **Title:** Generate full study title including:
   - Study type (e.g., "A Randomized, Double-Blind, Placebo-Controlled")
   - Phase (if drug: "Phase 2" or "Phase 3"; if device: may omit or use "Pivotal")
   - Intervention name
   - Indication
   - Population (e.g., "in Adults with [Condition]")

2. **Short Title:** Brief version (50 characters or less)

3. **Protocol Version and Date:** "Version 1.0 Draft" and current date

4. **Study Description:** 3-5 sentence summary including:
   - Study purpose
   - Population
   - Intervention(s)
   - Comparator (if applicable)
   - Primary outcome
   - Hypothesis statement

5. **Objectives:** List in bullets:
   - Primary objective (1 objective)
   - Secondary objectives (2-4 objectives)
   - Exploratory objectives (1-3 if applicable)
   - (Must match Section 4 exactly)

6. **Endpoints:** List in bullets:
   - Primary endpoint (1 endpoint with measurement timing)
   - Secondary endpoints (2-5 endpoints with timing)
   - Exploratory endpoints (if applicable)
   - (Must match Section 4 exactly)

7. **Study Population:** Describe:
   - Target enrollment (N=X)
   - Age range
   - Health status (healthy volunteers vs patients)
   - Key inclusion criteria summary (1-2 sentences)
   - Key exclusion criteria summary (1-2 sentences)

8. **Phase:** State "Phase 2" or "Phase 3" for drugs; "N/A" or "Pivotal Study" for devices

9. **Description of Sites:**
   - Multi-site or single-site
   - Geographic location (US sites, international, specify countries)
   - Approximate number of sites

10. **Description of Study Intervention(s):**
    - **For drugs:** Name, dose, route, frequency (e.g., "Pembrolizumab 200 mg IV Q3W")
    - **For devices:** Name, classification, brief description of intended use
    - Include comparator/control description

11. **Study Duration:**
    - Enrollment period: X months
    - Treatment/intervention period: X months
    - Follow-up period: X months
    - Total study duration: X months

12. **Participant Duration:**
    - Screening period: Up to X days
    - Treatment period: X weeks/months
    - Follow-up period: X weeks/months
    - Total participation duration: X months

#### Section 1.2: Schema (30 lines)

**Generate a text-based flow diagram** showing study progression. 

**Required Elements:**
- **Screening Period:** Show duration (e.g., "Within 28 days") and key activities (eligibility assessment)
- **Randomization:** If RCT, show randomization with allocation ratio (e.g., "1:1 randomization")
- **Study Arms:** Show each arm with:
  - Arm name/label (e.g., "Arm A: Intervention X", "Arm B: Control")
  - Target enrollment per arm (N=X)
  - Intervention details (dose, frequency)
  - Duration of treatment phase
- **Key Time Points:** Label major assessment points (Baseline, Week 4, Week 12, End of Treatment, Follow-up visits)
- **Follow-up Period:** Show duration and key assessments
- **Study End:** Mark endpoint

#### Section 1.3: Schedule of Activities (SoA) (50 lines)

**Generate comprehensive table.**

**Columns (15 columns):** Procedures | Screening (Day -28 to -1) | Baseline/V1 (Day 1) | Treatment Visits (V2-N with timing ± windows) | Follow-up Visits (± windows)

**Rows (20 rows) by Category:**

**A. Administrative (3-5 rows):** Informed consent, I/E criteria, demographics, medical history, randomization, study ID
**B. Intervention (1-2 rows):** Administer [intervention]; Device implantation/procedure
**C. Concomitant Meds (1 row):** X--------------X (continuous)
**D. Clinical Assessments (5-8 rows):** Physical exam (Complete at baseline/final, Directed at interim), vital signs, height (screening only), weight, performance status (ECOG/Karnofsky), disease-specific exams
**E. Laboratory (3-6 rows):** Hematology (CBC+diff), chemistry panel (see footnote), coagulation (if relevant), urinalysis (if relevant), pregnancy test (WOCBP: serum at screening, urine at visits), disease/intervention-specific labs
**F. Imaging/Diagnostics (2-4 rows):** Disease assessment imaging (CT/MRI/PET per RECIST), ECG/Echo (if required), other disease-specific tests
**G. Efficacy (2-4 rows):** Primary endpoint measurement, secondary endpoints, disease-specific assessments
**H. Safety (2-3 rows):** AE assessment (X--------------X continuous), intervention-specific safety checks
**I. PROs (1-2 rows, if applicable):** QoL questionnaire (specify instrument), symptom diary
**J. Special Procedures (0-3 rows):** Biospecimen collection, PK sampling, research procedures

**Marking:** X = performed; X--------------X = continuous; Footnotes: ^a^, ^b^, ^c^

**Visit Windows:** Screening ≤28 days; Baseline Day 1; Early ±1-3d; Mid ±3-7d; Late/monthly ±7-14d; Follow-up ±14-28d


---

### Section 2: INTRODUCTION (400 lines)

Generate three comprehensive subsections.

#### Section 2.1: Study Rationale (50 lines)

**Generate 2-4 paragraphs addressing:**

*Paragraph 1 - Clinical Problem* (15 lines):
- What is the disease/condition? (epidemiology, prevalence, incidence from Step 1 research)
- What is the current standard of care?
- What are the limitations of current treatments? (efficacy gaps, safety issues, access problems)

*Paragraph 2 - Evidence Gap* (15 lines):
- What is unknown or poorly understood about treating this condition?
- What specific question does THIS study answer?
- Why hasn't this been studied adequately before?

*Paragraph 3 - Why This Study Now* (15 lines):
- What recent developments make this study timely? (new intervention availability, new understanding of disease, recent FDA guidance from Step 1)
- What preliminary evidence supports this approach? (preclinical data, pilot studies, similar trials from Step 1 research)

*Paragraph 4 - Study Impact* (10 lines):
- What will this study contribute to the field?
- How will results inform clinical practice or regulatory decisions?
- What future research will this enable?

#### Section 2.2: Background (250 lines)

Generate comprehensive background with these subsections:

**A. Disease/Condition Overview** (50 lines):
- Disease definition, classification, and pathophysiology
- Natural history and disease progression
- Epidemiology: Prevalence, incidence, demographics, risk factors (cite sources from Step 1)
- Disease burden: Mortality rates, morbidity, QoL impact, economic costs
- Diagnosis: Diagnostic criteria, staging systems, biomarkers

**B. Current Standard of Care** (50 lines):
- First-line treatments (drugs, devices, procedures currently used)
- Treatment outcomes from pivotal trials (cite NCT numbers from Step 1 research)
- Response rates, survival data, symptom improvement statistics
- Limitations: Efficacy limitations (% responders), safety/tolerability issues (common AEs), practical barriers (cost, access), unmet needs in subgroups

**C. [FOR DEVICES ONLY] Device Background** (150 lines):

*C1. Device Description* (40 lines):
- Detailed physical description (size, weight, dimensions, materials)
- Components and their functions
- Principle of operation and mechanism of action at device level
- Intended use per proposed labeling
- Instructions for Use summary

*C2. Regulatory Classification* (30 lines):
- FDA classification: Class I, II, or III (specify with rationale)
- Product code (if known)
- Regulatory pathway:
  - **If 510(k):** List K-number, clearance date
  - **If De Novo:** List DEN-number, classification date
  - **If PMA:** List P-number, approval date
  - **If Investigational:** State "Investigational device, IDE application submitted/pending"

*C3. Predicate Device(s)* (if 510(k) pathway) (40 lines):
- Predicate device name, manufacturer
- Predicate 510(k) number (K-number)
- Predicate device indications for use
- Substantial equivalence rationale:
  - Similar intended use (explain how)
  - Similar technological characteristics (materials, design, energy source)
  - Similar performance data
- Differences from predicate and justification that differences don't affect safety/effectiveness

*C4. Clinical Experience with Predicate/Similar Devices* (40 lines):
- Clinical data from predicate device (published studies - cite 3-5 from Step 1)
- Real-world experience (registry data, post-market surveillance)
- Efficacy outcomes and safety profile
- AE rates and device complications from predicate
- Gaps in evidence this study addresses

**C. [FOR DRUGS/BIOLOGICS ONLY] Drug Background** (150 lines):

*C1. Drug Description* (30 lines):
- Chemical name, generic name, trade name
- Drug class and mechanism category
- Molecular structure (brief description)
- Formulation: Active ingredient(s), excipients, dosage form, strengths

*C2. Mechanism of Action* (40 lines):
- Biological target (receptor, enzyme, pathway)
- How drug interacts with target (agonist, antagonist, inhibitor)
- Downstream cellular and tissue effects
- Why this mechanism is relevant to disease (connect to pathophysiology from subsection A)

*C3. Pharmacology* (40 lines):
- Pharmacokinetics (if known): Absorption (bioavailability, Tmax), Distribution (Vd, protein binding), Metabolism (CYP enzymes, metabolites), Excretion (t1/2, renal/hepatic elimination)
- Pharmacodynamics (if known): Dose-response, time course, target engagement

*C4. Nonclinical Studies* (40 lines):
- Preclinical efficacy: In vitro studies, animal models, dose-response
- Preclinical safety/toxicology: Acute/chronic toxicity, carcinogenicity/genotoxicity, reproductive toxicity, NOAEL
- Translation to humans: Human equivalent dose calculation, starting dose rationale

*C5. Prior Clinical Experience* (40 lines):
- Phase 1 studies: First-in-human, dose escalation, MTD or RP2D, safety profile, PK/PD
- Phase 2 studies (if any): Indications studied, efficacy signals, safety in target population
- Approved indications (if any): Countries, approved indications and dosing, marketed experience
- Investigational use in other indications: Ongoing trials (NCT numbers from Step 1)

**D. Rationale for Current Study Intervention** (50 lines):
- Why is this intervention expected to work for this indication? (biological plausibility)
- What evidence supports this hypothesis? (preclinical, pilot studies, related indications)
- What is novel/innovative? (first in indication, new dose/regimen, new population)
- Rationale for study design choice (RCT vs single-arm, comparator choice, duration)

**E. Similar Clinical Trials and Lessons Learned** (50 lines):
- Identify 3-5 similar trials from Step 1 research (NCT numbers, titles, sponsors, design, N, key results)
- What did these trials teach us? (successes to replicate, challenges encountered, lessons for protocol design)
- How does current study differ? (different population, dose, duration, endpoints, improvements)

#### Section 2.3: Risk/Benefit Assessment (100 lines)

Generate three comprehensive subsections:

**A. Known Potential Risks** (60 lines):

*Immediate Risks* (30 lines):
- List 5-10 specific risks occurring during/shortly after intervention
- **For drugs:** Common AEs by frequency and severity with citations (e.g., "Nausea 60-70%, mostly Grade 1-2 (Smith et al., NCT01234567)"), Serious AEs (e.g., "Infusion reactions 5-10%, rare anaphylaxis"), Organ toxicities with grades
- **For devices:** Procedural risks (infection rates, bleeding), Device malfunction rates, Immediate complications
- Risks from study procedures (blood draws, imaging contrast, biopsies)

*Long-Range Risks* (30 lines):
- List 3-5 potential long-term risks
- **For drugs:** Chronic toxicities (cumulative organ damage), Immunosuppression, Secondary malignancies, Reproductive risks
- **For devices:** Chronic foreign body reaction, Late device failure, Long-term tissue changes
- Acknowledge unknown risks for novel interventions

**B. Known Potential Benefits** (40 lines):

*Immediate Potential Benefits* (20 lines):
- Direct benefit: Symptom improvement potential (specify symptoms, magnitude, timeframe)
- Disease control or regression potential
- Access to novel intervention
- Be realistic: May state "No guarantee of benefit; participants may receive placebo"
- Monitoring benefits: Close study team monitoring, regular assessments, study-related care access

*Long-Range Potential Benefits* (20 lines):
- Potential for durable response or long-term disease control
- Potential for improved QoL
- Reduced need for other treatments
- Contribution to generalizable knowledge for future patients

**C. Assessment of Potential Risks and Benefits** (40 lines):

*Risk-Benefit Balance* (20 lines):
- Weigh identified risks against potential benefits
- Compare to risks of standard care or no treatment
- Justify higher risks (if applicable) by greater potential benefit or serious disease
- Ethical justification statement

*Risk Minimization Strategies* (20 lines):
- How are risks minimized? (patient selection via eligibility criteria, dose selection from prior data, frequent monitoring per SoA, stopping rules, trained staff, DSMB oversight)
- Participant protections (informed consent, voluntary participation, withdrawal rights, confidentiality)

---

### Section 4: OBJECTIVES AND ENDPOINTS (50 lines)

**Generate an objectives and endpoints table** with these columns: Objective | Endpoint | Justification

**Rows to include:**

1. **Primary Objective and Endpoint** (1 row, 15 lines):
   - Objective: State as clear hypothesis (e.g., "To evaluate the efficacy of [intervention] compared to [control] in [population]")
   - Endpoint: Specify measurement (e.g., "Mean change from baseline in [measure] at Week 24"), must be specific, measurable, clinically meaningful, regulatory-acceptable
   - Justification: Explain why this endpoint is appropriate (cite similar trials, FDA guidance from Step 1, clinical meaningfulness)

2. **Secondary Objectives and Endpoints** (2-4 rows, 20 lines):
   - For each secondary objective/endpoint pair:
     - State objective clearly
     - Define endpoint with timing
     - Justify choice
   - Examples: Safety, additional efficacy measures, QoL, biomarkers

3. **Exploratory Objectives and Endpoints** (1-3 rows if applicable, 10 lines):
   - Clearly label as exploratory (hypothesis-generating, not powered)
   - Examples: Mechanistic biomarkers, sub-group analyses, correlative studies

**NOTE:** Objectives and endpoints listed here must match exactly with Synopsis table (Section 2.1) and Statistical Analysis section (Section 10 - will be generated in Step 4).

---

### Section 4: STUDY DESIGN (150 lines)

Generate four subsections:

**4.1 Overall Design** (50 lines):
- Study type: Interventional clinical trial
- Study phase: Phase 2 or 3 (drugs) or Pivotal (devices) or N/A
- Design: Randomized vs single-arm, controlled vs uncontrolled
- Blinding: Open-label, single-blind, double-blind, triple-blind (specify who is blinded)
- Randomization: Allocation ratio (e.g., 1:1), stratification factors (if applicable)
- Study arms: Describe each arm (intervention, dose, duration)
- Number of sites: Single-center vs multi-center, approximate number, geographic distribution
- Study duration: Enrollment period, treatment period, follow-up period, total duration
- Sample size: Target enrollment (N=X per arm, total), per-arm breakdown

**4.2 Scientific Rationale for Study Design** (50 lines):
- Why was this design chosen?
  - **If RCT:** Why is randomized controlled trial necessary? (gold standard for efficacy, regulatory requirement, ethical justification)
  - **If single-arm:** Why is single-arm acceptable? (rare disease, no standard comparator, ethical considerations, regulatory precedent - cite similar trials)
- Why this comparator/control?
  - **If placebo:** Justify placebo use (no effective treatment exists, or placebo + standard care design)
  - **If active comparator:** Why this specific comparator? (current standard of care, regulatory preference)
- Why this blinding approach? (minimize bias for subjective endpoints, or open-label acceptable for objective endpoints)
- Why this duration? (based on expected time to effect, disease natural history, similar trials)

**4.3 Justification for Dose** (30 lines):
- **For drugs:**
  - How was dose selected? (Phase 1 MTD/RP2D, Phase 2 dose-finding, PK/PD modeling)
  - Dose rationale from preclinical data (animal studies, HED calculation)
  - Dose rationale from prior clinical data (safety, efficacy signals)
  - Route and frequency rationale
  - Cite specific studies/data supporting dose choice
- **For devices:**
  - Device specifications and settings (if applicable)
  - Procedure specifications (surgical technique, implantation approach)
  - Rationale for procedure timing/frequency

**4.4 End of Study Definition** (20 lines):
- Participant completes study: When? (completion of last visit/procedure in SoA, including final follow-up)
- Study ends globally: When? (last participant completes last visit, database lock, or specific date)
- Early termination criteria: Under what circumstances might study end early? (safety concerns, futility, external data, regulatory decision, sponsor decision)

---

### Section 5: STUDY POPULATION (200 lines)

This is a critical section requiring detailed criteria.

**5.1 Inclusion Criteria** (100 lines):

**Generate 10-15 numbered, detailed inclusion criteria. Structure:**

1. **Diagnostic/Disease Criteria** (2-3 criteria):
   - Confirmed diagnosis (specify how: histological, imaging, clinical criteria, specify staging system)
   - Disease stage/severity requirements (specify measurable disease if applicable)
   - Duration of disease (if relevant)

2. **Age Requirements** (1 criterion):
   - Age range (e.g., "Age ≥18 years and ≤75 years") with rationale for limits

3. **Performance Status** (1 criterion):
   - Specify scale and threshold (e.g., "ECOG Performance Status 0-1" or "Karnofsky Performance Status ≥70%")

4. **Organ Function/Laboratory Requirements** (1 criterion referencing table):
   - State: "Adequate organ function as defined in Table X" or list specific values
   - **Generate Table X: Laboratory Values for Inclusion** (if complex, 15 parameters):
     - Hematological: ANC ≥1.5 × 10^9/L, Platelets ≥100 × 10^9/L, Hemoglobin ≥9 g/dL
     - Renal: Creatinine clearance ≥50 mL/min (Cockcroft-Gault), or Serum creatinine ≤1.5 × ULN
     - Hepatic: Total bilirubin ≤1.5 × ULN, AST/ALT ≤2.5 × ULN (or ≤5 × ULN if liver metastases)
     - Coagulation: INR ≤1.5, aPTT ≤1.5 × ULN
     - Other organ-specific parameters as relevant

5. **Prior Treatment Requirements** (1-2 criteria):
   - Treatment-naive OR specific prior treatments required
   - Specify washout periods if prior treatments allowed

6. **Life Expectancy** (1 criterion, if applicable):
   - Minimum life expectancy (e.g., "Life expectancy ≥6 months per investigator judgment")

7. **Contraception Requirements** (2 criteria - separate for WOCBP and males):
   - Women of childbearing potential (WOCBP): Define WOCBP, require effective contraception method (specify acceptable methods), specify duration (during study and X months after)
   - Males: Require effective contraception if partner is WOCBP, specify duration

8. **Pregnancy Testing** (1 criterion):
   - WOCBP must have negative pregnancy test within X hours prior to first dose (specify serum or urine)

9. **Tissue/Biomarker Requirements** (0-2 criteria, if applicable):
   - Tissue availability for biomarker analysis (specify type: archival vs fresh biopsy, processing requirements)
   - Specific biomarker status required (e.g., PD-L1 expression, HER2 status)

10. **Consent and Compliance** (2 criteria):
    - Ability to understand and provide written informed consent
    - Willingness and ability to comply with study procedures and follow-up

11-15. **Disease/Intervention-Specific Criteria** (3-5 additional criteria):
    - Add criteria specific to this intervention and indication
    - Examples: Measurable disease per RECIST, specific symptom severity, no active CNS metastases, candidate for specific procedure, etc.

**5.2 Exclusion Criteria** (60 lines):

**Generate 15-30 numbered exclusion criteria covering:**

**A. Prior Therapy (3-5):** Prior same/similar intervention; Recent chemo/targeted/investigational (specify washout); Recent radiation to target; Recent major surgery; Recent immunotherapy/biologics
**B. Active Infections (2-3):** HIV (or controlled acceptable); Active hep B/C (specify testing/controlled); Active systemic infection requiring IV antibiotics
**C. Pregnancy/Nursing (1):** Pregnant or breastfeeding
**D. Intervention Contraindications (3-5):** Hypersensitivity/allergy; **Devices:** Anatomical contraindications; **Drugs:** Class-specific (e.g., autoimmune for immunotherapy); Prior severe reaction; Conditions precluding safe administration
**E. Cardiovascular (2-3):** Uncontrolled hypertension (define threshold); Recent MI/unstable angina/CABG; Significant arrhythmia/QTc prolongation
**F. Other Comorbidities (3-5):** Severe pulmonary (specify); Active neurological (seizures, recent stroke); Psychiatric impairing compliance/consent; Active autoimmune requiring treatment; Bleeding disorders/coagulopathy
**G. Concurrent Medications (2-3):** Prohibited medications (list); Chronic immunosuppressants (exceptions); Concurrent trial enrollment
**H. Other Malignancies (1-2):** Active malignancy within X years (specify exceptions); High-risk recurrence
**I. Lab/Functional (1-2):** Lab abnormalities not in inclusion; Functional impairments precluding participation
**J. Logistical (1-2):** Unable to comply with procedures/follow-up; Investigator opinion unsuitable

**5.3 Lifestyle Considerations** (20 lines):
- Dietary restrictions (if any specific to intervention or assessments)
- Activity restrictions (if any during treatment or recovery)
- Contraception requirements (reference back to inclusion criteria)
- Other lifestyle considerations

**5.4 Screen Failures** (20 lines):
- Definition: Participant who consents but does not meet eligibility
- Documentation: Screen failures documented with reason for screen failure
- Re-screening: Specify if re-screening allowed and under what circumstances
- Reporting: Screen failures reported to IRB and in study records

**5.5 Strategies for Recruitment and Retention** (30 lines):
- Recruitment methods: How will participants be identified? (clinic populations, registries, advertisements, referrals)
- Recruitment materials: Subject to IRB approval
- Retention strategies: How will participants be retained? (regular communication, flexible scheduling, minimizing participant burden, reimbursement for time/travel)
- Enrollment targets and timeline: Target enrollment rate, enrollment period duration


---

### Step 6: Write Protocol Foundation Waypoint

Create `waypoints/02_protocol_foundation.md` with:
- Title Page (from Step 4)
- Sections 1-6 (from Step 5 synthesis) in markdown format

**IMPORTANT:** This is a NEW FILE creation. Write all content starting with Title Page, followed by Sections 1-6.

Create `waypoints/02_protocol_metadata.json` with:
```json
{
  "intervention_id": "[from metadata]",
  "intervention_name": "[from metadata]",
  "protocol_version": "1.0 Draft",
  "protocol_date": "[current date]",
  "study_design": "[from Step 1]",
  "enrollment_target": "[from Step 1]",
  "primary_endpoint": "[generated in Section 4]",
  "duration_months": "[from Step 1 or generated]",
  "regulatory_pathway": "[IDE or IND]",
  "protocol_status": "foundation_complete",
  "step_2_status": "completed",
  "step_3_status": "pending",
  "step_4_status": "pending",
  "sections_completed": [1, 2, 3, 4, 5, 6],
  "sections_pending": [7, 8, 9, 10, 11, 12],
  "notes": [
    "DRAFT for planning purposes",
    "Protocol foundation (Sections 1-6) completed",
    "Continue to Step 3 for intervention details",
    "Requires biostatistician review",
    "Requires IRB approval",
    "Requires FDA feedback",
    "Sponsor TBD items require completion"
  ]
}
```

### Step 7: Display Summary

Display concise summary with:
- Intervention name, protocol version, date
- Step 2 completion status
- Title Page + Sections completed: 1-6
- Protocol foundation file created with size
- DRAFT disclaimer
- Next steps: Review protocol foundation, continue to Step 3 for intervention details (Sections 7-8)

**Example output:**
```
✅ Step 2: Protocol Foundation - COMPLETED

Intervention: [Name]
Protocol: Version 1.0 Draft (2025-12-03)

Protocol Structure:
  ✓ Title Page (Protocol Cover Page with regulatory identifiers)

Sections Completed (1-6):
  ✓ Section 1: Statement of Compliance
  ✓ Section 2: Protocol Summary (Synopsis, Schema, SoA)
  ✓ Section 3: Introduction (Rationale, Background, Risk/Benefit)
  ✓ Section 4: Objectives and Endpoints
  ✓ Section 5: Study Design
  ✓ Section 6: Study Population (Inclusion/Exclusion Criteria)

Files Created:
  • waypoints/02_protocol_foundation.md (~[size]KB, [lines] lines)
  • waypoints/02_protocol_metadata.json
```

## Output Files

**Created:**
- `waypoints/02_protocol_foundation.md` (~100KB - Sections 1-6 only, ~1,500 lines)
- `waypoints/02_protocol_metadata.json` (~1KB - protocol metadata with phase tracking)

**NOT updated yet:**
- `waypoints/intervention_metadata.json` (will be updated after Step 4 completes)

## Error Handling

**If waypoint files missing:**
```
Error: Required waypoint files not found.
Cannot draft protocol without previous phase data.
Please run steps in order (Step 0, Step 1, then Step 2).
```

**If user declines protocol foundation:**
```
Protocol foundation skipped at user request.
Step 2 not completed - no waypoint files created.
User can return to this step later if needed.
```

**If Step 2 already completed:**
```
Warning: Phase 2 appears to be already completed.
Files exist: waypoints/02_protocol_foundation.md
Would you like to:
  1. Skip Phase 2 and continue to Phase 3
  2. Regenerate Phase 2 (will overwrite existing content)
  3. Exit
```

## Quality Checks

Before finalizing, verify:
- [ ] Title page is included with all required elements (metadata table, protocol ID, confidentiality statement, sponsor info, title, regulatory IDs, footer)
- [ ] All 6 sections (1-6) are included after the title page
- [ ] Synopsis table matches objectives/endpoints table
- [ ] Schedule of Activities table is comprehensive (20-30 rows, 12-20 columns)
- [ ] Inclusion criteria: 10-15 detailed items with specific values
- [ ] Exclusion criteria: 15-30 detailed items covering all categories
- [ ] Study design rationale references Phase 1 findings
- [ ] Background section leverages Phase 1 research extensively
- [ ] Intervention-specific terminology used correctly (device vs drug)
- [ ] Protocol foundation length: ~1,500 lines (appropriate for sections 1-6)
- [ ] File created successfully at waypoints/02_protocol_foundation.md

## Notes

- This subskill generates approximately 1,500 lines of protocol content
- Output stays well within token limits by focusing on Sections 1-6 only
- Phases 2b and 2c will append to this foundation to complete the protocol
- Protocol foundation provides the structural framework; intervention details and operational content follow in subsequent phases
