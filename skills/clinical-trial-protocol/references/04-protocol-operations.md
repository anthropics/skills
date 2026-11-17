# Step 4: Clinical Protocol Operations and Statistics

## Purpose

This subskill generates the operational, assessment, and statistical sections (8-11) of a clinical study protocol. It adds efficacy and safety assessments, adverse event reporting, statistical analysis plan with sample size calculation, regulatory/operational considerations, and references to complete the protocol.

## Prerequisites

**Required Files:**
- `waypoints/intervention_metadata.json` (must contain `protocol_template` field from Step 2)
- `waypoints/01_clinical_research_summary.json`
- `waypoints/02_protocol_foundation.md` (sections 1-5 from Step 2)
- `waypoints/03_protocol_intervention.md` (sections 6-7 from Step 3)
- `waypoints/02_protocol_metadata.json` (must show step_3_status: "completed")
- `scripts/sample_size_calculator.py` (for sample size calculation)

## What This Subskill Does

1. Verifies Step 3 completion
2. **Performs sample size calculation** (asks user for parameters, runs calculator script)
3. Reads protocol template (from metadata) and shared guidance
4. Synthesizes operational and statistical content for Sections 8-11
5. Creates new file `waypoints/04_protocol_operations.md` with Sections 8-11
6. **Concatenates all protocol sections** into `waypoints/02_protocol_draft.md`
7. Updates protocol and intervention metadata

## Execution Flow

### Step 1: Verify Phase 3 Completion

Read `waypoints/02_protocol_metadata.json` and verify:
- `step_3_status` is "completed"
- `waypoints/02_protocol_foundation.md` exists (Sections 1-5)
- `waypoints/03_protocol_intervention.md` exists (Sections 6-7)

**If Step 3 not completed:**
```
Error: Step 3 must be completed before Phase 4.
Phase 3 status: [current status]

Please complete Step 3 first to generate intervention details (Sections 6-7).
```
Exit.

**If Phase 3 completed:** Proceed to Step 2.

### Step 2: Calculate Sample Size

**BEFORE generating Section 9, perform sample size calculation.**

#### 2.1 Extract Endpoint Information

Read from `waypoints/02_protocol_draft.md` Section 3 (Objectives and Endpoints):
- Primary endpoint description
- Classify endpoint type:
  - Continuous: Mean change, score change (e.g., "Mean change from baseline in systolic blood pressure")
  - Binary: Proportion, success rate, response rate (e.g., "Proportion of participants achieving treatment success")
  - Time-to-event: Survival, time to progression (Note: Not commonly used for primary endpoint in Phase 2/3, but possible)

#### 2.2 Determine Study Design

From Section 4 (Study Design):
- RCT (randomized controlled trial) vs Single-arm
- Superiority vs Non-inferiority

#### 2.3 Prompt User for Statistical Parameters

**For CONTINUOUS endpoints:**

Ask user conversationally:
```
📊 Sample Size Calculation - Continuous Endpoint

Primary Endpoint: [From Section 3, e.g., "Mean reduction in systolic blood pressure at 6 months"]

To calculate sample size, I need the following information from you:

1. Expected effect size (mean difference between groups):
   Based on similar trials from Phase 1: [e.g., "5 mmHg reduction expected"]

   Please confirm or provide your expected effect size (as a number): ___

2. Expected standard deviation:
   Based on similar trials from Phase 1: [e.g., "Standard deviation typically 15 mmHg"]

   Please confirm or provide expected standard deviation: ___

3. Study design (default: superiority):
   - Superiority (showing intervention is better than control)
   - Non-inferiority (showing intervention is not worse than control)

   Your choice (superiority/noninferiority, default: superiority): ___

Optional parameters (press Enter to use defaults):
- Alpha (Type I error rate): 0.05 (5%)
- Power: 0.80 (80%)
- Expected dropout rate: 0.15 (15%)

Would you like to customize these optional parameters? (Yes/No, default: No)
```

If user wants to customize optional parameters, ask for each.

**For BINARY endpoints:**

Ask user conversationally:
```
📊 Sample Size Calculation - Binary Endpoint

Primary Endpoint: [From Section 3, e.g., "Treatment success rate at 6 months"]

To calculate sample size, I need the following information from you:

1. Expected proportion in CONTROL group:
   Based on similar trials from Phase 1: [e.g., "60% success rate in control"]

   Please provide control group proportion (0 to 1, e.g., 0.60 for 60%): ___

2. Expected proportion in TREATMENT group:
   Based on similar trials from Phase 1: [e.g., "75% success rate in treatment"]

   Please provide treatment group proportion (0 to 1, e.g., 0.75 for 75%): ___

3. Study design (default: superiority):
   - Superiority (showing intervention is better than control)
   - Non-inferiority (showing intervention is not worse than control)

   Your choice (superiority/noninferiority, default: superiority): ___

Optional parameters (press Enter to use defaults):
- Alpha (Type I error rate): 0.05 (5%)
- Power: 0.80 (80%)
- Expected dropout rate: 0.15 (15%)

Would you like to customize these optional parameters? (Yes/No, default: No)
```

**For TIME-TO-EVENT endpoints (if applicable):**

Note: Sample size calculator may not support time-to-event. If primary endpoint is time-to-event, use pattern-based approach from similar trials in Phase 1, and add disclaimer.

#### 2.4 Run Sample Size Calculator Script

**BEFORE running the calculator, display this message to the user:**

```
🔬 Calculating Sample Size

Running statistical power calculation with your parameters...

This will:
• Calculate the required sample size per arm
• Adjust for expected dropout rate
• Generate detailed assumptions for the statistical section
• Save results to waypoints/02_sample_size_calculation.json

Please wait while the calculation completes.
```

**For continuous endpoints:**

```bash
python scripts/sample_size_calculator.py \
  --type continuous \
  --effect-size [user provided value] \
  --std-dev [user provided value] \
  --alpha [user provided or 0.05] \
  --power [user provided or 0.80] \
  --dropout [user provided or 0.15] \
  --design [superiority or noninferiority] \
  --output waypoints/02_sample_size_calculation.json
```

**For binary endpoints:**

```bash
python scripts/sample_size_calculator.py \
  --type binary \
  --p1 [control proportion] \
  --p2 [treatment proportion] \
  --alpha [user provided or 0.05] \
  --power [user provided or 0.80] \
  --dropout [user provided or 0.15] \
  --design [superiority or noninferiority] \
  --output waypoints/02_sample_size_calculation.json
```

**AFTER running the calculator successfully, display this message to the user:**

```
✅ Sample Size Calculation Complete

Results:
• Sample Size Per Arm: [n_per_arm from calculation]
• Total Sample Size (Unadjusted): [n_total from calculation]
• Adjusted for Dropout ([dropout]%): [adjusted_n_total from calculation]
• Final Enrollment Target: [adjusted_n_total] participants

These results will be incorporated into Section 9.2 (Sample Size Determination) of the protocol.
```

#### 2.5 Read Calculation Results

If script succeeds:
- Read `waypoints/02_sample_size_calculation.json`
- Extract:
  - Endpoint type
  - Sample size per arm (n_per_arm)
  - Total sample size (n_total)
  - All input assumptions (effect_size, std_dev or p1/p2, alpha, power, dropout)
  - Adjusted sample size accounting for dropout

If script fails:
- Use pattern-based approach: Look at similar trials from Step 1 research, use their enrollment numbers
- Add prominent disclaimer: "Sample size calculation could not be performed. Enrollment target based on similar trials: [NCT numbers]. Requires biostatistician review and validation."

### Step 3: Read Protocol Template and Shared Guidance

1. Read `waypoints/intervention_metadata.json` to get the `protocol_template` and `template_source` field values
2. **Read the protocol template file:**
   - The path is stored in `protocol_template` field (could be `assets/[name].md` OR a user-provided path)
   - Read the file at that path (focus on Sections 8-11)
   - Note: The `template_source` field indicates whether this is `"directory"` or `"user_provided"` (for logging/debugging only)
3. Read `waypoints/02_protocol_foundation.md` and `waypoints/03_protocol_intervention.md` to understand existing context (especially study design, endpoints, population, and Schedule of Activities)

**Internalize:**
- Template structure for Sections 8-11
- Content depth targets from shared guidance
- Sample size calculation results (from Step 2)
- Quality principles (comprehensive over brief, specific over generic)

### Step 4: Synthesize Operations and Statistics Content

Generate Sections 8-11 following template structure, adapted for this specific intervention and indication.

**Use data from:**
- Sample size calculation results (`waypoints/02_sample_size_calculation.json`)
- Intervention metadata
- Phase 1 clinical research summary
- Existing protocol draft (Sections 1-8)

**Follow guidance from:**
- Selected protocol template from Step 3 (structure, regulatory requirements)

---

## Section Generation Instructions

### Section 8: STUDY ASSESSMENTS AND PROCEDURES (800 lines)

#### 8.1 Efficacy Assessments (100 lines)

**Primary Endpoint Measurement** (40 lines):
- Endpoint name: [From Section 3]
- Detailed description of measurement procedure
- Instrument or scale used: Include name, range, clinically meaningful difference
  - If validated scale: Cite validation reference, describe domains
  - If clinical measurement: Describe procedure in detail
- Timing of assessments: Reference Schedule of Activities (Section 2.3)
- Who performs assessment: Trained investigator, blinded assessor, central reader, participant self-report
- Standardization procedures: Training requirements, quality control procedures, calibration (for devices)
- Data collection: Source documents, eCRF entry

**Secondary Endpoint Measurements** (60 lines):

For EACH secondary endpoint (2-5 endpoints):
- Endpoint name: [From Section 3]
- Measurement procedure: Similar detail as primary
- Validated instrument specification: Name, version, scoring
- Timing: Per SoA
- Assessor: Who performs
- Quality control

**Common validated instruments** (examples - use appropriate for indication):
- Quality of life: EQ-5D-5L, EORTC QLQ-C30, SF-36
- Symptom scales: Disease-specific scales
- Functional assessments: Karnofsky, ECOG, Barthel Index
- Cognitive assessments: MMSE, MoCA
- Imaging criteria: RECIST v1.1 for solid tumors, Lugano for lymphoma

#### 8.2 Safety and Other Assessments (200 lines)

**Laboratory Tests** (60 lines):
- Timing: Reference Schedule of Activities
- Hematology specifications:
  - Complete blood count (CBC) with differential
  - Parameters: WBC, RBC, hemoglobin, hematocrit, platelets, ANC, lymphocytes, monocytes, eosinophils, basophils
  - Method: Automated hematology analyzer
  - Fasting: Not required
- Chemistry panel specifications:
  - Comprehensive metabolic panel
  - Parameters: Sodium, potassium, chloride, CO2, glucose, BUN, creatinine, calcium, albumin, total protein, alkaline phosphatase, ALT, AST, total bilirubin
  - Additional: Creatinine clearance (calculated by Cockcroft-Gault equation)
  - Fasting: Specify if required for glucose
- Coagulation (if relevant): PT/INR, aPTT
- Urinalysis (if relevant): Dipstick or microscopic
- Disease-specific labs: Thyroid function, cardiac biomarkers, tumor markers, etc.
- Sample handling: Collection, processing, storage, shipping to central lab
- Reference ranges: Local lab normal ranges

**Imaging** (40 lines):
- Modality: CT, MRI, PET, X-ray, ultrasound
- Anatomical coverage: Chest/abdomen/pelvis, brain, etc.
- Protocol specifications: Contrast vs non-contrast, slice thickness, image acquisition parameters
- Timing: Per Schedule of Activities
- Quality control: Central imaging review (if applicable)
- Assessment criteria: RECIST v1.1, modified RECIST, WHO criteria
- Image storage: PACS, DICOM format

**Physical Examinations** (30 lines):
- Complete physical examination: Baseline and final visit - all body systems
- Directed physical examination: Interim visits - focus on intervention-related findings
- Components: General appearance, vital signs, HEENT, cardiovascular, pulmonary, abdominal, neurological, musculoskeletal, skin
- Disease-specific exams: Tumor measurements, neurological exam, etc.

**Vital Signs** (20 lines):
- Parameters: Blood pressure, heart rate, respiratory rate, temperature, oxygen saturation
- Measurement procedures: Position (seated, supine), rest period before measurement, equipment specifications
- Timing: Per SoA
- Clinically significant changes: Define thresholds requiring action

**Electrocardiogram (ECG)** (if required) (30 lines):
- Type: 12-lead ECG
- Timing: Per SoA
- Interpretation: Investigator interpretation, central reading (if applicable)
- QTc calculation: Specify formula (Fridericia, Bazett)
- QTc prolongation criteria: Define threshold for concern (e.g., QTc >480 ms or increase >60 ms from baseline)

**Cardiac Assessments** (if required) (30 lines):
- Echocardiogram or MUGA scan
- Left ventricular ejection fraction (LVEF)
- Timing: Per SoA
- LVEF decline criteria: Define threshold for dose modification or discontinuation

**Disease-Specific Assessments** (30 lines):
- Tumor measurements: Bidimensional or RECIST
- Symptom scores: Disease-specific validated scales
- Functional assessments: ADL, IADL
- Other disease-specific measures

**Quality Control for All Assessments** (20 lines):
- Training of assessors: Required training, certification
- Standard operating procedures: SOPs for each assessment
- Calibration: Equipment calibration schedules
- Data quality checks: Range checks, consistency checks
- Central review: Specify assessments requiring central review

---

#### 8.3 Adverse Events and Serious Adverse Events (300 lines)

**CRITICAL: Generate ALL subsections 8.3.1-8.3.9 with complete regulatory definitions.**

**8.3.1 Definition of Adverse Events (AE)** (20 lines):
- ICH-GCP definition: Any untoward medical occurrence in a participant administered a pharmaceutical product or medical device, whether or not related to treatment. Includes unfavorable signs, symptoms, or disease temporally associated with intervention use.
- Examples in this study context: [List 5-10 anticipated AEs based on intervention]
- Distinguish AEs from expected disease symptoms: [Specify how to differentiate]
- Pre-existing conditions: Worsening = AE

**8.3.2 Definition of Serious Adverse Events (SAE)** (20 lines):
- Regulatory definition per 21 CFR 312.32 (drugs) or 21 CFR 812.3(s) (devices)
- SAE criteria (any one of):
  1. Death
  2. Life-threatening
  3. Hospitalization (new or prolonged)
  4. Persistent/significant disability
  5. Congenital anomaly/birth defect
  6. Important medical event requiring intervention
- Exclusions: Planned protocol hospitalizations, elective procedures, social admissions
- Examples: [List 5-10 potential SAEs for this intervention]

**8.3.3 Classification of an Adverse Event** (100 lines):

*8.3.3.1 Severity of Event* (30 lines):
- CTCAE v5.0 grading system (Common Terminology Criteria for Adverse Events)
- **Grade 1 (Mild):** Asymptomatic/mild; no intervention; [2-3 examples for intervention]
- **Grade 2 (Moderate):** Minimal intervention indicated; limiting instrumental ADL; [2-3 examples]
- **Grade 3 (Severe):** Medically significant; hospitalization/disabling; limiting self-care ADL; [2-3 examples]
- **Grade 4 (Life-threatening):** Urgent intervention indicated; [2-3 examples]
- **Grade 5 (Death):** Death related to AE

**Important:** Severity (Grade) ≠ Seriousness (SAE). Example: Grade 1 reaction requiring hospitalization = SAE.

**CTCAE reference:** https://ctep.cancer.gov/protocoldevelopment/electronic_applications/ctc.htm

*8.3.3.2 Relationship to Study Intervention* (30 lines):

**5-point attribution scale:**
- **Not Related:** Clearly explained by other causes; [1 example]
- **Unlikely:** Doubtfully related; alternatives more likely; [1 example]
- **Possible:** Reasonable temporal relationship but other factors possible; [1 example]
- **Probable:** Likely related; alternatives less likely; [1 example]
- **Definite:** Clear temporal relationship, known pattern, no other explanation; [1 example]

**Assessment:** Investigator assesses each AE; document rationale; when uncertain, use "Possible" or "Probable"

**Reporting:** Related = Possible/Probable/Definite; Unrelated = Not Related/Unlikely; Unexpected related SAEs require expedited FDA reporting

*8.3.3.3 Expectedness* (20-40 lines):
- **Expected:** Listed in Investigator's Brochure, device labeling/IFU, Protocol Section 3.3, or FDA-approved labeling
- **Unexpected:** Not listed OR greater severity/frequency/different body system than listed

**SUSAR:** Suspected Unexpected Serious Adverse Reaction = Unexpected + Related + Serious (requires expedited FDA/IRB reporting)

**Reference documents for this study:** [List specific IB, device labeling, Protocol Section 3.3]

**8.3.4 Time Period and Frequency for Event Assessment and Follow-Up** (50 lines):

**AE Collection Start:**
- AE collection begins: At time of informed consent OR at first dose of study intervention (specify)
- Pre-treatment AEs: AEs occurring after consent but before first dose are captured as baseline conditions (medical history)

**AE Collection End:**
- For drugs: AE collection ends 30 days after last dose of study intervention
- For devices: AE collection may extend longer (specify: 90 days, 6 months, or through final visit) depending on device type and potential for late effects
- For long-acting agents or biologics: May extend AE collection period (specify)
- SAEs: Continue to collect SAEs beyond 30-day period if related to study intervention

**Frequency of Assessment:**
- At each study visit per Schedule of Activities (Section 2.3)
- Continuous: Participants instructed to report new symptoms immediately between visits (provide contact information)
- Elicited by investigator: "Have you had any health problems since your last visit?"
- Volunteered by participant: Any symptoms volunteered by participant

**Follow-Up:**
- AEs followed until: Resolution, stabilization, or determination that event is unlikely to resolve (chronic condition)
- Ongoing AEs at study completion: Continue follow-up until resolution or for 30 days after last dose (minimum)
- SAEs: Follow until resolution or stabilization

**Late-Onset Events:**
- Events occurring after 30-day follow-up: If participant contacts site with event potentially related to intervention, report as AE

**8.3.5 Adverse Event Reporting** (50 lines):

**Participant Responsibility:**
- Participants instructed to report all new symptoms, health problems, or changes in health status immediately
- Contact information: 24/7 contact number provided on wallet card

**Site Responsibility:**
- Document ALL AEs in participant's medical record (source documentation)
- Record AEs in electronic Case Report Form (eCRF)
- Timeframe: Within 24 hours of becoming aware of AE

**AE Documentation (for each AE):**
- AE term: Use participant's words, then translate to medical terminology
- Start date: Date AE first occurred or was first observed
- Stop date: Date AE resolved or stabilized
- Severity: CTCAE Grade (1-5)
- Seriousness: SAE criteria met (Yes/No)
- Relationship: Attribution (Not Related, Unlikely, Possible, Probable, Definite)
- Action taken: Intervention held, dose reduced, discontinued, none, etc.
- Outcome: Resolved, resolved with sequelae, ongoing, fatal
- Treatment: Medications or interventions given for AE

**MedDRA Coding:**
- All AEs coded using Medical Dictionary for Regulatory Activities (MedDRA) version [specify version, e.g., 25.1]
- Lowest Level Term (LLT) and Preferred Term (PT) assigned
- System Organ Class (SOC) assigned for analysis

**Routine Submission to Sponsor:**
- Non-serious AEs: Reported to sponsor per scheduled data transmission (typically weekly or monthly)
- Sponsor monitors AE data for trends and signals

**8.3.6 Serious Adverse Event Reporting** (80 lines):

**IMMEDIATE Reporting Requirements:**

**To Sponsor:**
- Timeframe: Within 24 hours of site becoming aware that AE meets SAE criteria
- Method: Phone call or email to sponsor safety contact (provide contact information)
- Initial report: May be preliminary if full information not yet available
- Follow-up report: Complete SAE report form within 24-48 hours
- Ongoing follow-up: Updates as new information becomes available until resolution

**SAE Report Form Contents:**
- Participant information: Study ID, initials, age, sex
- SAE details: Event term, start/stop dates, outcome
- Seriousness criteria: Which SAE criterion met (death, life-threatening, hospitalization, etc.)
- Severity: CTCAE grade
- Relationship to intervention: Attribution
- Expectedness: Expected vs unexpected
- Action taken with intervention: Held, reduced, discontinued, none
- Concomitant medications and procedures
- Investigator narrative: Description of event, clinical course, outcome

**To IRB:**
- Timeframe: Per IRB requirements (typically within 5-10 calendar days for unexpected related SAEs)
- Method: IRB submission portal or email
- Events reportable to IRB: Unexpected + Related SAEs, deaths, protocol deviations involving increased risk
- Annual report: Summary of all SAEs in annual continuing review

**To FDA (Sponsor Responsibility):**
- Sponsor submits IND Safety Reports (for drugs, 21 CFR 312.32) or IDE reports (for devices, 21 CFR 812.150)
- Fatal or life-threatening unexpected related SAEs: 7 calendar days (initial report), 15 days (follow-up)
- Other unexpected related SAEs: 15 calendar days
- Annual report: Summary of SAEs in IND/IDE annual report

**Expedited Reporting (SUSARs):**
- Suspected Unexpected Serious Adverse Reactions (SUSARs): Serious + Unexpected + Related
- Reported by sponsor to FDA within regulatory timeframes
- Investigators at all sites notified of SUSARs

**Follow-Up Reports:**
- Submit follow-up SAE reports as new information becomes available
- Final report when SAE resolves or stabilizes

**8.3.7 Reporting Events to Participants** (30 lines):

**When to Inform Participants:**
- New safety information emerges that may affect risk/benefit or willingness to participate
- SUSAR occurs at this site or other sites
- Protocol amended to address new risks

**Process:**
- Investigator notifies participants of new safety information
- Provide written summary of new information
- Allow participants to ask questions
- Document notification in study records

**Consent Form Updates:**
- If new risks identified, informed consent form amended
- Amendment submitted to IRB for approval
- Re-consent process required for currently enrolled participants
- New participants sign updated consent form

**Participant Right to Withdraw:**
- Participants always have right to withdraw from study
- New safety information may prompt some participants to withdraw

**8.3.8 Events of Special Interest** (30 lines):

**Intervention-Specific Events Requiring Special Monitoring:**

**For drugs/biologics:**
- Infusion reactions: Hypersensitivity, cytokine release syndrome
- Immune-related AEs (for immunotherapy): Pneumonitis, colitis, hepatitis, endocrinopathies, dermatitis, neuropathies
- Organ-specific toxicities: Cardiotoxicity, nephrotoxicity, hepatotoxicity, neurotoxicity
- Hypersensitivity reactions: Anaphylaxis, severe allergic reactions
- Tumor lysis syndrome (for oncology interventions)

**For devices:**
- Device malfunctions: Any failure of device to operate as intended
- Device migration or displacement
- Device fracture or breakage
- Infections related to device: Surgical site infections, device-related infections
- Need for device removal or revision
- Thrombosis or embolism related to device

**Reporting and Management:**
- All events of special interest reported to sponsor within 24 hours
- Follow protocol-specific management algorithms (reference Section 7.2 for dose modifications)
- **For devices:** Device malfunctions reported to sponsor and manufacturer immediately; may require device return for analysis
- Document detailed description, management, and outcome

**8.3.9 Reporting of Pregnancy** (40 lines):

**All Pregnancies Reported Immediately:**
- Pregnancy in female participant
- Pregnancy in partner of male participant

**Detection:**
- Pregnancy testing per Schedule of Activities: Serum β-hCG at screening, urine pregnancy tests at subsequent visits for women of childbearing potential (WOCBP)
- Participant self-report: Any missed menstrual period or suspected pregnancy reported immediately

**Reporting:**
- Report pregnancy to sponsor within 24 hours of awareness
- Pregnancy report form: Estimated date of conception, estimated due date, pregnancy test result

**Study Intervention:**
- Intervention discontinued immediately upon pregnancy confirmation
- No further doses administered

**Follow-Up:**
- Follow pregnancy to outcome: Live birth, miscarriage, elective termination, ectopic pregnancy, stillbirth
- Outcome report: Include pregnancy outcome, complications, birth defects (if any)
- Infant follow-up: Obtain information on infant health at birth (if participant consents)
- Timeframe: Follow through delivery and obtain outcome information

**Partner Pregnancies:**
- Male participants must report if their partner becomes pregnant during study
- Report to sponsor within 24 hours
- Follow to outcome

**Pregnancy Registry (if applicable):**
- If pregnancy registry exists for intervention, provide information to participant
- Encourage participation in registry (voluntary)

---

#### 8.4 Unanticipated Problems (40 lines)

**Definition of Unanticipated Problems Involving Risks (per OHRP/FDA):**

An unanticipated problem involving risks to participants or others is any incident, experience, or outcome that meets ALL of the following criteria:
1. **Unexpected:** Not described in terms of nature, severity, or frequency in protocol, consent form, investigator brochure, or device labeling
2. **Related or possibly related** to participation in research
3. **Suggests that research places participants or others at greater risk** of harm than previously known or recognized

**Examples:**
- Cluster of similar AEs suggesting increased risk
- Single occurrence of serious injury that was not anticipated
- Protocol deviation that increases risk to participants
- Breach of confidentiality
- Loss of study drug/device
- Complaint from participant about research conduct raising safety concerns
- Error in informed consent process affecting participant rights/welfare

**Not Unanticipated Problems:**
- Individual SAEs that are expected and consistent with known risks (these are just SAEs, not UPs)
- Protocol deviations that do not increase risk or affect participant rights

**Reporting:**
- To IRB: Report to IRB within timeframe specified by IRB (typically 5-10 days)
- To Sponsor: Report to sponsor within 24 hours
- To FDA: Sponsor determines if FDA reporting required

**Documentation:**
- Description of unanticipated problem
- Analysis of how it meets UP criteria
- Actions taken to prevent recurrence
- Impact on research and participants
- Protocol amendments or corrective actions implemented

---

### Section 9: STATISTICAL CONSIDERATIONS (600 lines)

**Use sample size calculation results from Step 2 (`waypoints/02_sample_size_calculation.json`) throughout this section.**

#### 9.1 Statistical Hypotheses (30 lines):

**For Primary Endpoint:**
- Null hypothesis (H0): [State null hypothesis, typically "There is no difference between [intervention] and [control] in [primary endpoint]"]
- Alternative hypothesis (Ha or H1): [State alternative, typically "There is a difference between [intervention] and [control] in [primary endpoint]" for superiority, or "[Intervention] is non-inferior to [control]" for non-inferiority]
- One-sided vs two-sided testing: State whether testing is one-sided or two-sided (typically two-sided for superiority, one-sided for non-inferiority)
- Alpha level: 0.05 (two-sided) or 0.025 (one-sided)

**If Multiple Primary Endpoints:**
- State hypotheses for each
- Specify multiplicity adjustment (see Section 10.4.2)

**For Key Secondary Endpoints (if formal testing planned):**
- State hypotheses
- Specify if testing is conditional on primary endpoint significance

#### 9.2 Sample Size Determination (150 lines):

**Use exact values from `waypoints/02_sample_size_calculation.json`.**

**Paragraph 1: Primary Endpoint for Sample Size** (15-20 lines):
- The sample size calculation is based on the primary efficacy endpoint: [Endpoint name from Section 4]
- Endpoint type: [Continuous/Binary/Time-to-event]

**Paragraph 2: Detailed Assumptions and Calculations** (80 lines):

**For Continuous Endpoints:**
- Primary endpoint: [Specify, e.g., "Mean change from baseline in systolic blood pressure at 6 months"]
- Expected mean difference between groups: [X] units [From calculation: effect_size]
  - Based on: [Cite 2-3 similar trials from Step 1 research that informed this assumption]
- Common standard deviation: [Y] units [From calculation: std_dev]
  - Based on: [Cite similar trials]
- Statistical test: Two-sample t-test or ANCOVA adjusting for baseline
- Two-sided alpha: [From calculation: alpha, typically 0.05]
- Power: [From calculation: power, typically 0.80 or 80%]
- Allocation ratio: 1:1 [or specify different ratio]
- Sample size formula: [Specify formula or software]
- Calculated sample size per arm: [n_per_arm from calculation]
- Total sample size (both arms): [n_total from calculation]

**For Binary Endpoints:**
- Primary endpoint: [Specify, e.g., "Proportion of participants achieving treatment success at 6 months"]
- Expected proportion in control group (P1): [From calculation: p1]
  - Based on: [Cite 2-3 similar trials]
- Expected proportion in treatment group (P2): [From calculation: p2]
  - Based on: [Cite similar trials]
- Absolute difference (P2 - P1): [Calculate and state]
- Statistical test: Chi-square test or Fisher's exact test
- Two-sided alpha: [From calculation: alpha, typically 0.05]
- Power: [From calculation: power, typically 0.80 or 80%]
- Allocation ratio: 1:1 [or specify different ratio]
- Sample size formula: [Specify formula or software]
- Calculated sample size per arm: [n_per_arm from calculation]
- Total sample size (both arms): [n_total from calculation]

**For Time-to-Event Endpoints (if applicable):**
- Primary endpoint: [Specify]
- Median time in control group: [M1] months
- Median time in treatment group: [M2] months
- Hazard ratio (HR): [Calculate from medians]
- Statistical test: Log-rank test
- Accrual period: [X] months
- Follow-up period: [Y] months
- Number of events required: [Calculated number]
- Calculated sample size per arm: [n_per_arm]
- Total enrollment target: [n_total]

**Paragraph 3: Adjustment for Dropout** (30-40 lines):
- Expected dropout rate: [From calculation: dropout, typically 15%]
  - Based on: [Cite similar trials showing dropout rates]
- Rationale: Account for participants lost to follow-up, withdrawals, and missing data
- Adjusted sample size per arm: [n_per_arm] / (1 - [dropout]) = [adjusted_n_per_arm]
- Total enrollment target: [adjusted_n_total]

**Formula shown:**
```
Adjusted N = N / (1 - dropout rate)
Adjusted N per arm = [n_per_arm] / (1 - [dropout]) = [adjusted_n_per_arm]
Total enrollment: [adjusted_n_total]
```

**Paragraph 4: Sensitivity Analyses** (40 lines):
- To assess robustness of sample size, calculations performed under alternative assumptions:

**Alternative Scenario 1: Lower effect size (20% reduction):**
- Effect size: [X * 0.8] [or P2-P1 reduced by 20%]
- Calculated N per arm: [Calculate alternative N]
- Interpretation: [State whether study still adequately powered]

**Alternative Scenario 2: Higher effect size (20% increase):**
- Effect size: [X * 1.2] [or P2-P1 increased by 20%]
- Calculated N per arm: [Calculate alternative N]
- Interpretation: [State increased power]

**Alternative Scenario 3: Higher variance (20% increase in SD):**
- Standard deviation: [Y * 1.2]
- Calculated N per arm: [Calculate alternative N]
- Interpretation: [State impact on power]

**Conclusion:** The proposed sample size is robust to moderate deviations from assumptions. If actual effect size or variance differs substantially from assumptions, study may be underpowered or overpowered.

**Paragraph 5: Power for Secondary Endpoints** (20 lines):
- Sample size is powered for the primary efficacy endpoint only
- Secondary endpoints:
  - Expected to have [greater/similar/lower] effect sizes
  - Study may have [sufficient/insufficient] power to detect clinically meaningful differences in secondary endpoints
  - If power is limited, secondary endpoint analyses may be considered exploratory and hypothesis-generating
- Acknowledge that study is not formally powered for multiple comparisons across all secondary endpoints

**Paragraph 6: Justification and Biostatistician Review** (40 lines):
- Sample size assumptions informed by similar trials:
  - [NCT number and citation 1]
  - [NCT number and citation 2]
  - [NCT number and citation 3]
- Sample size calculation performed using [software, e.g., "nQuery version X", "PASS version X", "R statistical software", "SAS PROC POWER"]
- **IMPORTANT DISCLAIMER:** "Sample size calculations are preliminary and subject to biostatistician review and validation prior to study initiation. Final sample size may be adjusted based on updated assumptions or regulatory feedback."

#### 9.3 Populations for Analyses (50 lines):

Define each analysis population clearly:

**Intent-to-Treat (ITT) Population:**
- Definition: All randomized participants, analyzed according to treatment assignment as randomized, regardless of treatment actually received
- Inclusions: All participants who undergo randomization
- Exclusions: None
- Use: Primary population for efficacy analyses (conservative approach, preserves randomization)

**Modified Intent-to-Treat (mITT) Population** (if applicable):
- Definition: All randomized participants who received at least one dose of study intervention
- Inclusions: Randomized participants with ≥1 dose
- Exclusions: Randomized but never dosed (e.g., consent withdrawal before dosing)
- Use: May be primary efficacy population if specified; supportive efficacy analysis
- Rationale: [If using mITT as primary, justify - e.g., "Participants never dosed have no opportunity to benefit"]

**Per-Protocol (PP) Population:**
- Definition: All participants who completed study per protocol without major protocol deviations
- Inclusions: Participants who: Received ≥[X]% of planned intervention doses (e.g., ≥80%), Completed all required efficacy assessments, Did not have major protocol deviations affecting efficacy
- Exclusions: Major protocol deviations (specify what constitutes major)
- Use: Supportive efficacy analysis (provides estimate of treatment effect under ideal adherence)

**Safety Population:**
- Definition: All participants who received at least one dose (or partial dose) of study intervention
- Analyzed according to treatment actually received (as-treated)
- Inclusions: All participants with ≥1 dose
- Exclusions: Randomized but never dosed
- Use: Primary population for all safety analyses

**Evaluable Population** (if applicable):
- Definition: Participants with adequate data for specific endpoint assessment
- Inclusions: Participants with valid baseline and post-baseline measurements for specific endpoint
- Use: Sensitivity analysis for specific endpoints

**Primary Population Specification:**
- Primary efficacy analyses: ITT population [or mITT if specified]
- Safety analyses: Safety population
- Supportive efficacy analyses: PP population

#### 9.4 Statistical Analyses (400 lines):

**CRITICAL: Generate ALL subsections 9.4.1-9.4.9 with detailed methods.**

**9.4.1 General Approach** (30 lines):

**Descriptive Statistics:**
- Categorical: n (%)
- Continuous: mean ± SD, median, range/IQR, min, max

**Inferential Statistics:**
- Alpha: 0.05 (two-sided unless specified)
- 95% confidence intervals for treatment effects
- Missing data per Section 10.4.10

**Statistical Software:** [R/SAS/Stata version X.X]

**Pre-Specified Covariates:** Age, sex, baseline primary endpoint value, stratification factors, [other relevant covariates]

**Assumptions:** Normality (Shapiro-Wilk, Q-Q plots), homogeneity of variance (Levene's), proportional hazards (Schoenfeld residuals). If violated: transformations or nonparametric tests.

**Multiplicity:** Primary endpoint - no adjustment. Secondary endpoints: [Specify adjustment method or state exploratory]

**9.4.2 Analysis of the Primary Efficacy Endpoint(s)** (50 lines):

**For EACH primary endpoint, generate:**

**Endpoint:** [Name from Section 3]
**Definition:** [Full definition]
**Timing:** [Timepoint]
**Scale:** [Continuous/Binary/Time-to-event, units]
**Population:** Intent-to-Treat (ITT) [or mITT]

**Statistical Procedure:**

**If Continuous:**
- ANCOVA: `Y = Treatment + Baseline_Value + Age + Sex + [Stratification_Factors] + Error`
- Least squares means, treatment effect (difference), 95% CI, two-sided p-value, effect size

**If Binary:**
- Logistic regression: `logit(P[success]) = Intercept + Treatment + [Covariates]`
- OR with 95% CI, p-value (Wald/likelihood ratio), risk difference, relative risk
- Alternative: Chi-square or Fisher's exact (if counts <5)

**If Time-to-Event:**
- Cox regression: `h(t) = h0(t) × exp(Treatment + [Covariates])`
- HR with 95% CI, p-value, Kaplan-Meier curves, log-rank test, median time-to-event
- Check proportional hazards (Schoenfeld residuals)

**Diagnostics:** Check assumptions, examine residuals, identify outliers

**Presentation:** Table (statistics, effect, CI, p-value), Figure (mean change/proportion/KM curves)

**Sensitivity Analyses:** Per-protocol, complete case, alternative missing data methods, unadjusted

**If Multiple Primary Endpoints:** [Specify multiplicity adjustment method or hierarchical testing order]

**9.4.3 Analysis of the Secondary Endpoint(s)** (40 lines):

**For EACH secondary endpoint (2-5 endpoints):**

**Secondary Endpoint [N]:** [Name]
- Definition: [Full definition]
- Scale: [Continuous/Binary/Time-to-event]
- Population: ITT
- Method: [ANCOVA/Logistic/Cox regression - similar to 10.4.2]
- Treatment effect: [Mean difference/OR/HR with 95% CI], p-value
- Presentation: Table, figure

[Repeat for each secondary endpoint]

**Multiplicity Strategy:** [Hierarchical testing (specify order) OR No adjustment (exploratory) OR Bonferroni/Holm adjustment]

**9.4.4 Safety Analyses** (60 lines):

**Analysis Population:** Safety population (all participants with ≥1 dose)

**Adverse Events (AEs):**
- MedDRA Coding: All AEs coded using MedDRA version [X.X] (System Organ Class, Preferred Term)
- Summary tables: Frequency (n) and percentage (%) of participants with:
  - Any AE
  - Treatment-related AEs (Possible, Probable, or Definite relationship)
  - Grade 3-4 AEs (by CTCAE grading)
  - Serious AEs (SAEs)
  - AEs leading to dose reduction
  - AEs leading to treatment discontinuation
  - Fatal AEs (Grade 5)
- AEs by System Organ Class and Preferred Term: Sorted by decreasing frequency
- Denominator: Number of participants in safety population
- Comparison between arms: Descriptive only (no formal statistical testing), but may calculate risk difference if clinically relevant

**Serious Adverse Events (SAEs):**
- Separate detailed table for SAEs
- Frequency by SOC and PT
- Relationship to study intervention
- Outcomes: Resolved, ongoing, fatal, resolved with sequelae

**AEs Leading to Discontinuation:**
- Separate table
- By SOC and PT
- Treatment group comparison

**Deaths:**
- Individual participant listings with narratives
- Cause of death
- Relationship to study intervention
- Timing relative to last dose

**Laboratory Data:**
- Shift tables: Baseline CTCAE grade → Worst post-baseline CTCAE grade
  - For key lab parameters: Hemoglobin, ANC, platelets, creatinine, ALT, AST, bilirubin
- Potentially Clinically Significant (PCS) values: Define thresholds for each parameter
  - Example: Hemoglobin <8 g/dL, ANC <1.0 × 10^9/L, ALT >3× ULN
- Frequency of PCS values by treatment group
- Summary statistics: Mean, SD, change from baseline for continuous lab values

**Vital Signs:**
- Summary statistics at each time point: Mean, SD
- Change from baseline: Mean change, 95% CI
- Outliers: Frequency of values outside normal ranges (e.g., SBP >180 mmHg, HR >120 bpm)

**ECG/Cardiac Assessments (if applicable):**
- QTc interval: Mean, SD, change from baseline, frequency of QTc >480 ms or increase >60 ms
- LVEF: Mean, SD, change from baseline, frequency of LVEF decline >10% or LVEF <50%

**Device-Related Complications (for devices):**
- Device malfunctions: Frequency and type
- Device-related infections
- Need for device removal or revision
- Comparison to predicate device rates (if available)

**9.4.5 Baseline Descriptive Statistics** (30 lines):

**Table 1: Baseline Characteristics by Treatment Arm**

**Purpose:** Demonstrate comparability of treatment groups at baseline

**Population:** ITT population

**Variables included:**
- Demographics:
  - Age: Mean ± SD, median, range
  - Sex: n (%) Male, Female
  - Race: n (%) for each category (White, Black/African American, Asian, Other)
  - Ethnicity: n (%) Hispanic/Latino, Not Hispanic/Latino
- Disease Characteristics:
  - Disease duration: Mean ± SD, median
  - Disease stage/severity: n (%) for each category
  - Baseline primary endpoint value: Mean ± SD, median
- Prior Treatments:
  - Prior [specific treatment 1]: n (%)
  - Prior [specific treatment 2]: n (%)
  - Number of prior treatments: Mean ± SD, median
- Baseline Efficacy Measures:
  - Baseline values for primary and key secondary endpoints: Mean ± SD for continuous, n (%) for categorical
- Baseline Laboratory Values:
  - Key lab parameters: Mean ± SD

**Presentation:**
- Three columns: Intervention Arm, Control Arm, Total
- Continuous variables: Mean ± SD, median (range)
- Categorical variables: n (%)
- **NO statistical testing between arms**: Baseline comparisons are descriptive only; no p-values presented
- Rationale: Randomization ensures balance; hypothesis testing at baseline is inappropriate

**9.4.6 Planned Interim Analyses** (40 lines):

**If Interim Analyses Planned:**

**Purpose:** [Efficacy/futility/safety monitoring]
**Timing:** [X% enrollment/X months/X events]
**Number:** [1, 2, or more]
**DSMB:** Conducts analyses; investigators/sponsor blinded; recommends continue/modify/terminate

**Methods:**

**Efficacy:** Group sequential design, O'Brien-Fleming or Lan-DeMets alpha spending, overall alpha = 0.05 maintained
**Futility:** Conditional power approach; stop if < [threshold, e.g., 20%]
**Safety:** DSMB reviews unblinded data; no formal boundary

**Interim Analysis Plan:**

| Analysis | Timing | Info Fraction | Efficacy Boundary | Futility Boundary | Alpha Spent |
|----------|--------|---------------|-------------------|-------------------|-------------|
| Interim 1 | 50% | 0.50 | 3.47 (p=0.001) | <20% | 0.001 |
| Interim 2 | 75% | 0.75 | 2.51 (p=0.012) | <30% | 0.011 |
| Final | 100% | 1.00 | 2.00 (p=0.045) | N/A | 0.045 |

**Impact:** CIs and p-values adjusted for multiple looks; estimates adjusted for early stopping bias if applicable

**Reporting:** If early stop, report reason, results, analyses conducted

---

**If NO Interim Analyses:**
- No formal efficacy/futility analyses; study continues to full enrollment unless safety concerns
- **Safety Monitoring:** Investigators (continuous); DSMB/SMC reviews aggregate data [frequency]; DSMB may recommend termination; operates under charter (Section 10.6)

**9.4.7 Sub-Group Analyses** (50 lines):

**Purpose:** Explore consistency of treatment effect across participant subgroups (hypothesis-generating, not confirmatory)

**Pre-Specified Subgroups:**
1. Age: <65 years vs ≥65 years
2. Sex: Male vs Female
3. Race/Ethnicity: [Specify categories based on enrollment, e.g., White vs Non-White]
4. Baseline disease severity: [Define categories, e.g., Mild vs Moderate/Severe]
5. Disease-specific subgroups:
   - [e.g., Biomarker status: Positive vs Negative]
   - [e.g., Disease stage: Early vs Advanced]
   - [e.g., Prior treatment: Yes vs No]
6. [Additional pre-specified subgroups relevant to intervention and indication]

**Analysis Method:**

**Interaction Tests:**
- Test for subgroup × treatment interaction in regression model
- Model: Outcome = Treatment + Subgroup + Treatment×Subgroup + [Covariates]
- P-value for interaction term indicates whether treatment effect differs between subgroups
- Significance level: P < 0.10 considered suggestive of interaction (more lenient than 0.05 due to low power)

**Forest Plots:**
- Treatment effect estimate (mean difference, OR, or HR) with 95% CI for each subgroup
- Overall treatment effect for comparison
- Visual assessment of consistency

**Interpretation:**
- Subgroup analyses are exploratory and hypothesis-generating
- Not adjusted for multiplicity (multiple subgroups tested)
- Interpret with caution: Risk of false positives
- Consistency assessment: Determine if treatment effect is generally consistent across subgroups
- If interaction p < 0.10: Describe difference and note exploratory nature

**Reporting:**
- Subgroup analyses reported in exploratory analyses section
- Clearly labeled as exploratory
- Limitations acknowledged

**9.4.8 Tabulation of Individual Participant Data** (20 lines):

**All individual participant data will be listed in appendices (not summarized in tables).**

**Listings Include:**
1. Demographics: Individual participant demographics (ID, age, sex, race, ethnicity, study arm)
2. Adverse Event Listings:
   - All AEs: Every AE for every participant (ID, AE term, start/stop date, severity, relationship, outcome)
   - SAEs: Separate listing for serious AEs
   - AEs Leading to Discontinuation: Separate listing
   - Deaths: Separate listing with narratives
3. Concomitant Medications: All medications taken during study (ID, medication name, dose, route, start/stop date, indication)
4. Laboratory Data: All lab values at all time points (ID, parameter, value, unit, date, normal range, CTCAE grade)
5. Efficacy Endpoints: Individual endpoint values at all time points (ID, endpoint, value, date)
6. Protocol Deviations: All deviations (ID, deviation description, date, impact)

**Sorting:** Listings sorted by treatment group, then subject ID, then visit or date

**Purpose:**
- Support summary tables and analyses
- Available for regulatory inspection
- Enable identification of individual participant patterns

**9.4.9 Exploratory Analyses** (40 lines):

**Purpose:** Generate hypotheses for future studies; not powered or adjusted for multiplicity

**Exploratory Analyses Include:**

1. **Exploratory Endpoints** (from Section 4):
   - [List specific exploratory endpoints]
   - Descriptive statistics and treatment comparisons
   - No formal hypothesis testing

2. **Correlation Analyses:**
   - Correlation between biomarkers and efficacy endpoints
   - Example: "Assess correlation between [biomarker X] levels and primary endpoint response"
   - Methods: Pearson or Spearman correlation, scatter plots

3. **Post-Hoc Subgroup Analyses:**
   - Subgroups not pre-specified in Section 10.4.7
   - Generated based on emerging data patterns
   - Clearly labeled as post-hoc

4. **Responder Analyses:**
   - Define responder criteria: [e.g., "Participants achieving ≥50% improvement in primary endpoint"]
   - Proportion of responders in each treatment arm
   - Characteristics of responders vs non-responders

5. **Dose-Response Analyses (if multiple dose levels):**
   - Assess relationship between dose and efficacy
   - Assess relationship between dose and safety

6. **Longitudinal Analyses:**
   - Trajectory of endpoints over time
   - Mixed models for repeated measures
   - Growth curve analyses

**Methods:**
- Descriptive statistics predominant
- Exploratory modeling
- Graphical displays

**Multiplicity:**
- No adjustment for multiplicity
- Purely hypothesis-generating

**Interpretation:**
- Results interpreted with caution
- Acknowledge exploratory nature and risk of false positives
- Use to inform future research questions

**9.4.10 Missing Data Handling** (30 lines):

**Primary Approach** (choose based on endpoint/design):

**MMRM (Mixed Model for Repeated Measures):** For continuous endpoints with multiple timepoints; includes all data without imputation; MAR assumption
**Multiple Imputation:** MICE or similar; 20-50 imputations; combined via Rubin's rules; MAR assumption
**LOCF:** Generally NOT recommended unless field standard; assumes no change after dropout

**Rationale:** [Justify method based on expected patterns and literature]

**Sensitivity Analyses:**

1. **Complete Case:** Observed outcomes only (MCAR assumption)
2. **Worst-Case:** Intervention = worst, Control = best (conservative)
3. **Best-Case:** Intervention = best, Control = worst (optimistic)
4. **Tipping Point:** Identify assumptions that would change conclusions
5. **Pattern-Mixture:** Model outcomes by missingness pattern (if potentially informative)

**Missing Covariates:** Complete case (if few) OR multiple imputation

**Dropouts:** Compare time to discontinuation (KM, log-rank), tabulate reasons, assess if differential dropout suggests informative missingness

**Reporting:** Describe patterns, report n (%) missing, reasons by arm, sensitivity results, impact on conclusions

---

### Section 10: SUPPORTING DOCUMENTATION AND OPERATIONAL CONSIDERATIONS (400 lines)

#### 10.1 Informed Consent Process (50 lines):

**Documents:** ICF for adults; assent for minors (if <18 years); optional consents (future specimen/data use, genetic research)

**Procedures:**
- **Who:** PI or qualified trained designee
- **When:** Before study-specific procedures; adequate time to review
- **Language:** Participant's native language; 8th grade reading level; avoid jargon
- **Process:** Verbal explanation, written ICF, time to review (≥24 hrs if possible), questions answered, emphasize voluntary participation and withdrawal rights

**Key Elements (21 CFR 50.25):** Research purpose, duration, procedures, experimental nature, risks/discomforts, benefits, alternatives, confidentiality, compensation (if applicable), voluntary participation, withdrawal rights, contact information

**Documentation:** Signed/dated by participant (or LAR) and person obtaining consent; original in study records, copy to participant, documented in medical record

**Re-Consent:** If protocol amended with new risks, re-consent required; amended ICF submitted to IRB; currently enrolled and new participants sign updated form

**Compliance:** 21 CFR Part 50, ICH-GCP E6(R2), IRB requirements, HIPAA Authorization (US studies)

#### 10.2 Study Discontinuation and Closure (50 lines):

**Circumstances for Early Study Termination:**
1. Unacceptable safety profile: SAE rate or severity exceeds acceptable risk
2. Futility: Interim analysis demonstrates low probability of achieving study objectives
3. External data: New data from other studies renders study obsolete or unethical
4. Regulatory authority decision: FDA or other regulatory body requests study termination
5. Sponsor decision: Business, financial, or strategic reasons
6. Inadequate enrollment: Unable to enroll sufficient participants within reasonable timeframe

**Procedures Upon Early Termination:**

**Notification:**
- Notify FDA (for IND/IDE studies): Within required timeframe per regulations
- Notify IRB: Immediately, with reason for termination
- Notify participants: Letter sent to all enrolled participants explaining termination
- Notify investigators: All sites notified
- Update ClinicalTrials.gov: Update study status to "Terminated" with reason

**Safety Follow-Up:**
- Enrolled participants: Continue safety follow-up per protocol or abbreviated schedule
- Ongoing AE monitoring: AEs followed to resolution or stabilization
- Final safety assessment: Encourage participants to complete final safety visit

**Data Collection:**
- Collect all data up to termination point
- Complete data entry for available data
- Perform final database lock

**Analysis and Reporting:**
- Analyze all available data
- Final study report prepared
- Report submitted to FDA and IRB
- Results posted on ClinicalTrials.gov (per 42 CFR Part 11 if applicable)

**Study Closure (Planned Completion):**
- Last participant completes last visit
- All data collected and entered
- All queries resolved
- Database locked
- Statistical analysis performed
- Final study report prepared
- Close-out visits at all sites
- Study records archived

#### 10.3 Confidentiality and Privacy (40 lines):

**HIPAA Compliance (if US study):**
- Participants sign HIPAA Authorization for use and disclosure of Protected Health Information (PHI)
- Authorization covers: Use of PHI for research, disclosure to sponsor, disclosure to regulatory authorities, disclosure for safety reporting
- Authorization specifies: Types of PHI to be used, who may use/disclose PHI, purpose, expiration (or statement that no expiration), right to revoke

**Data Protection:**
- Deidentified data: Participants assigned unique subject identification numbers (e.g., "001-001")
- No personal identifiers in study database: No names, addresses, dates of birth (only age), medical record numbers
- Secure data storage: Electronic data stored on password-protected, encrypted servers
- Physical records: Kept in locked filing cabinets in secure area
- Limited access: Only authorized study personnel have access to identifiable data
- Site master log: Links subject ID to identifiable information; kept separately in locked location

**Data Transfer:**
- Data transmitted to sponsor via secure encrypted transmission
- No PHI included in routine data transmissions
- Identifiable data (e.g., for SAE reporting) sent via secure methods

**GDPR Compliance (if EU participants or sites):**
- Data processing per General Data Protection Regulation (GDPR) requirements
- Data Processing Agreement between sponsor and sites
- Participant rights: Access to data, rectification, erasure (right to be forgotten), data portability, restriction of processing
- Legal basis for processing: Participant consent, legal obligations (regulatory requirements)
- Data retention: Specify retention period (per ICH-GCP: minimum 2 years after last approval or longer per regulations)
- Data Protection Officer: Appointed if required

**Confidentiality Breach:**
- Report to sponsor, IRB, and participants (if identifiable)
- Mitigation measures implemented
- Report to relevant authorities (OCR for HIPAA, supervisory authority for GDPR)

#### 10.4 Future Use of Stored Specimens and Data (30 lines):

**Optional Consent for Future Research:**
- Separate section in ICF or separate consent form
- Participants may consent to study but decline future use
- Voluntary: No impact on study participation if declined

**Future Research Uses:**
- Biospecimens (blood, tissue, other samples) may be stored for future research
- Types of future research: Unspecified at this time; may include genetic/genomic research, biomarker discovery, other exploratory research
- Identifiability: Specimens coded or deidentified
- Sharing: Specimens may be shared with other researchers (academic, commercial)
- Commercial use: Potential for commercial use; no financial benefit to participant
- Results: Future research results not returned to participants (unless clinically actionable and IRB approved)

**Storage:**
- Duration: Specify (e.g., "Specimens stored for up to 15 years" or "indefinitely")
- Location: Biorepository or sponsor facility
- Destruction: Participant may request specimen destruction at any time

**Re-Contact:**
- Participant may be re-contacted for additional studies if consented
- Contact information kept separately from specimens

**Withdrawal:**
- Participant may withdraw consent for future use at any time
- Specimens destroyed upon request
- Data already generated from specimens may be retained

#### 10.5 Key Roles and Study Governance (40 lines):

**Sponsor:** Overall oversight; regulatory submissions (IND/IDE, safety/annual reports, amendments); funding; monitoring/QA; data management (eCRF, database); safety reporting; study supplies; site support; closeout (final report, results posting, archiving)

**Principal Investigator (PI):** Conduct study per protocol; regulatory compliance (21 CFR 50, 56, 312/812, ICH-GCP); IRB submissions/approvals; informed consent; participant safety/AE management; SAE reporting (sponsor within 24 hrs, IRB per timeline); data accuracy; staff supervision/training; study supplies accountability; available for FDA inspections; protocol deviation reporting

**Medical Monitor (if applicable):** Safety oversight; SAE review/causality; dosing decisions; stopping rule evaluation (if no DSMB); protocol questions; emergency unblinding authority; safety report assistance

**Biostatistician:** Write SAP; review/validate sample size; generate randomization schedule; perform analyses; interim analyses (if planned); prepare statistical sections; support regulatory submissions

**Steering Committee (if applicable):** Protocol design/amendments; study oversight; publication/authorship decisions; members: PI, sponsor, KOLs, biostatistician

**DSMB:** See Section 10.6

#### 10.6 Safety Oversight (50 lines):

**For DEVICES (21 CFR 812):**

**IDE Classification:**
- **Significant Risk (SR):** Implants, life-support, or substantial diagnostic/therapeutic importance → Full IDE (FDA+IRB approval, investigational labeling, annual FDA reports, safety reports)
- **Non-Significant Risk (NSR):** Doesn't meet SR criteria → Abbreviated IDE (IRB approval only, FDA may audit)

**Approval Process:**
- SR: IDE to FDA (30-day review) → IRB approval → Study begins
- NSR: IRB approval with NSR determination → Study begins

**Device Classification:** Class III (usually SR, requires PMA); Class II (SR or NSR); Class I (usually exempt unless SR)

**Predicate Safety (510(k) pathway):** Leverage predicate device safety data, justify similar profile

---

**For DRUGS (21 CFR 312):**

**IND Requirements:**
- Phase [2 or 3]; IND submission to FDA (30-day review, may proceed if no hold)
- IRB approval, informed consent (21 CFR 50)
- Safety reporting: 15-day (unexpected related SAEs), 7-day (fatal/life-threatening)
- Annual reports: Safety, progress, amendments, IB updates

---

**For ALL STUDIES:**

**DSMB/SMC:**

**When Required:** High-risk (mortality/morbidity endpoints), serious toxicities, vulnerable populations, blinded trials with interim analyses, large multi-site, NIH-funded (risk-based)

**When Not Required:** Low-risk, short duration, small studies with internal monitoring

**DSMB Structure:** 3-7 independent experts (clinical, biostatistician, ethicist); operates under formal charter

**Meetings:** [Quarterly/semi-annually/annually]; closed sessions (unblinded data), open sessions (blinded data)

**Responsibilities:** Review unblinded safety/efficacy, assess benefit-risk, evaluate stopping rules, recommend continue/modify/terminate

**If No DSMB:** Internal monitoring by medical monitor/sponsor; periodic safety review; IRB reviews at continuing review

**Stopping Rules:**
- **Safety:** Excess SAEs ([threshold-fold increase]), specific Grade 4 toxicities (>[X]%), deaths exceed threshold
- **Futility:** Conditional power <20% (Section 10.4.6)
- **Efficacy:** Crosses pre-specified boundary (Section 10.4.6)

#### 10.7 Clinical Monitoring (40 lines):

**Monitoring Plan:**
- Monitoring approach: On-site monitoring and/or central monitoring
- Risk-based approach: Monitoring intensity based on risk level per FDA guidance "Oversight of Clinical Investigations — A Risk-Based Approach to Monitoring"

**Monitoring Frequency:**
- Site initiation visit: Before first participant enrolled
- Periodic monitoring visits: Frequency based on risk and enrollment rate
  - High-risk: Monthly or quarterly
  - Moderate-risk: Quarterly or semi-annually
  - Low-risk: Semi-annually or annually
- Close-out visit: After last participant completes study

**Monitoring Activities:**
- Regulatory document review: IRB approval, ICFs, CV of PI, training documentation, delegation log
- Informed consent verification: Review process, verify signed consents for sample of participants
- Source data verification (SDV): Compare eCRF data to source documents for accuracy
  - 100% SDV for key data points (primary endpoint, SAEs, eligibility, informed consent)
  - Targeted SDV for other data points (sample of participants)
- Inclusion/exclusion criteria verification: Confirm eligibility for sample of participants
- AE reporting verification: Confirm SAEs reported to sponsor and IRB within required timeframes
- Study intervention accountability: Verify drug/device accountability records
- Protocol compliance: Identify protocol deviations
- Data quality: Review data completeness and quality

**Monitoring Reports:**
- Monitor prepares monitoring visit report after each visit
- Report submitted to sponsor
- Site receives findings and responds to any issues
- Follow-up on corrective actions

**Central Monitoring:**
- Remote data review: Real-time review of eCRF data for quality, consistency, and patterns
- Statistical methods: Detect outliers, unusual patterns, potential fraud
- Risk-based: Focus on key data points

#### 10.8 Quality Assurance and Quality Control (40 lines):

**Quality Assurance (QA) Procedures:**

**Standard Operating Procedures (SOPs):**
- Sponsor SOPs: Cover all aspects of study conduct (monitoring, data management, safety reporting, etc.)
- Site SOPs: Cover site-specific procedures (informed consent, AE reporting, lab processing, etc.)
- Training on SOPs required

**Training:**
- Investigator meeting: All investigators and coordinators attend site initiation meeting
- Protocol training: Detailed training on protocol procedures, eligibility, endpoints, safety
- eCRF training: Training on electronic data capture system
- GCP training: ICH-GCP training required for all study staff
- Device/intervention training: Training on intervention administration (especially for devices)

**Audits:**
- Sponsor audits: Periodic audits of sites by sponsor QA department
- Regulatory inspections: FDA inspections (for cause or routine)
- Audit preparedness: Sites maintain inspection-ready study files

**Quality Control (QC) Procedures:**

**Data Quality:**
- Edit checks: Automated range checks, consistency checks, logic checks in eCRF
- Query management: System generates queries for out-of-range or inconsistent data
- Query resolution: Site responds to queries, provides corrections or explanations
- Data review: Regular data review meetings

**Protocol Compliance:**
- Protocol deviation tracking: All deviations documented and tracked
- Corrective and preventive actions (CAPA): Implement CAPA for recurring deviations

**Quality Metrics:**
- Define quality metrics: Query rates, deviation rates, enrollment rates, monitoring findings
- Track metrics over time
- Review at study team meetings

**Oversight:**
- Sponsor quality management
- Regular study team meetings to review quality

#### 10.9 Data Handling and Record Keeping (60 lines):

**Data Collection and Management:**

**Electronic Data Capture (EDC):**
- eCRF system: [Specify system name, e.g., "Medidata Rave", "REDCap", or state "TBD"]
- Web-based access: Sites access eCRF via secure web browser
- User access: Role-based access control; unique usernames and passwords
- Training: Sites trained on eCRF before use

**CRF Completion:**
- Timeliness: Data entered within [X] days of visit (e.g., 3-5 business days)
- Accuracy: Data transcribed from source documents accurately
- Completeness: All required fields completed
- Queries: Respond to data queries within [X] days (e.g., 5 business days)

**Query Resolution:**
- System generates automated queries for missing or inconsistent data
- Monitor generates manual queries during monitoring visits
- Site responds: Correct data or provide explanation
- Query closure: Monitor or data manager closes query after review

**Data Quality Checks:**
- Real-time edit checks during data entry
- Batch edit checks run periodically
- Medical review: Medical monitor reviews safety data
- Statistical review: Biostatistician reviews data for patterns and outliers

**Data Management:**
- Database design: Sponsor data management team designs database
- Database testing: User acceptance testing before go-live
- Database lock: Database locked for analysis after all queries resolved and monitoring complete
- Data cleaning: Iterative process until database clean

**Source Documentation:**

**Definition of Source Documents:**
- Original records of clinical findings, observations, or activities
- Examples: Medical records, progress notes, lab reports, imaging reports, ECG printouts, device interrogation reports, study-specific worksheets

**Source Data Verification (SDV):**
- Monitor compares eCRF data to source documents
- Verify accuracy, completeness, and consistency
- 100% SDV for key data points; targeted SDV for others

**Source Document Requirements:**
- Contemporaneous: Recorded at the time of the event
- Original: First recording of information
- Accurate and complete
- Legible
- Attributable: Signed and dated by person performing/recording procedure
- Traceable to participant: Subject ID included

**Data Security:**

**Electronic Systems:**
- Secure servers: Data stored on secure, password-protected servers
- Encryption: Data encrypted during storage and transmission
- Access controls: Role-based access; unique user IDs
- Audit trails: 21 CFR Part 11 compliant; system logs all data entries, modifications, deletions with user ID and timestamp
- Backups: Regular automated backups; disaster recovery plan

**Physical Records:**
- Locked storage: Source documents and regulatory documents stored in locked cabinets
- Restricted access: Only authorized site personnel have access

**Study Records Retention:**

**Duration:**
- Per ICH-GCP: Minimum 2 years after last approval of marketing application or longer per local regulations
- Per FDA (devices, 21 CFR 812.140): 2 years after investigation terminated or concluded
- Per FDA (drugs, 21 CFR 312.62): 2 years after marketing application approved or 2 years after IND closed
- Sponsor specifies exact retention period (typically 15-25 years)

**What to Retain:**
- Regulatory documents: Protocol, amendments, ICF versions, IRB approvals, FDA correspondence
- Source documents: Medical records, lab reports, imaging
- CRFs: Electronic or paper CRFs
- Monitoring reports
- Safety reports
- Final study report

**Archiving:**
- After study closure, records archived per sponsor procedures
- Sites notified when records may be destroyed

#### 10.10 Protocol Deviations (30 lines):

**Definition:**
- Protocol deviation: Any departure from protocol procedures, inclusion/exclusion criteria, or good clinical practice

**Classification:**

**Major Deviation:**
- Affects participant safety, rights, or welfare
- Affects data integrity or study results
- Examples: Enrollment of ineligible participant, administration of wrong dose, failure to obtain informed consent, failure to report SAE

**Minor Deviation:**
- Does not affect safety, rights, or data integrity
- Examples: Visit conducted outside window (if clinically acceptable), minor documentation error

**Reporting:**
- To sponsor: All deviations reported to sponsor
  - Major deviations: Immediately (within 24 hours)
  - Minor deviations: Routine reporting (with data transmission)
- To IRB: Major deviations reported to IRB per IRB requirements (typically within 5-10 days)
- Documentation: Deviation log maintained at site

**Management:**
- Root cause analysis: Investigate cause of deviation
- Corrective action: Implement corrective action to prevent recurrence
- Preventive action: Identify and address potential deviations before they occur
- Monitor trends: Track deviation rates; identify systemic issues

**Impact on Analysis:**
- Per-protocol population: Major deviations may exclude participant from PP population (see Section 10.3)

#### 10.11 Publication and Data Sharing Policy (40 lines):

**Authorship:**
- Per International Committee of Medical Journal Editors (ICMJE) criteria:
  1. Substantial contributions to conception/design, data acquisition/analysis/interpretation
  2. Drafting or revising manuscript critically for intellectual content
  3. Final approval of version to be published
  4. Agreement to be accountable for all aspects
- Investigators and key contributors eligible for authorship
- Sponsor representatives may be co-authors if meet ICMJE criteria

**Publication Timeline:**
- Primary manuscript: Target within 12 months of study completion
- Presentations: Results presented at scientific meetings (oral or poster)
- Secondary manuscripts: Exploratory analyses, subgroup analyses

**Review and Approval:**
- Sponsor review: Sponsor reviews manuscript to ensure accuracy and protect confidential information
- Review period: [X] days (e.g., 30-60 days)
- Sponsor may request delays for patent filing or confidentiality

**Authorship Disputes:**
- Resolved by steering committee or PI

**Data Sharing:**
- Individual Participant Data (IPD): Deidentified IPD may be available upon reasonable request after publication
- Who can access: Qualified researchers
- What data: Deidentified data at participant level
- When: After publication of primary manuscript (typically 6-12 months after publication)
- How: Data use agreement required; request submitted to sponsor
- Why: For meta-analyses, secondary analyses (must specify research question)
- Embargo period: [X] months after publication before data shared

**ClinicalTrials.gov:**
- Results posted per 42 CFR Part 11 (if applicable): Within 1 year of primary completion date
- Includes: Participant flow, baseline characteristics, primary and secondary outcome measures, adverse events

#### 10.12 Conflict of Interest Policy (30 lines):

**Financial Disclosure:**
- Per 21 CFR Part 54 (Financial Disclosure by Clinical Investigators)
- All investigators and sub-investigators disclose financial interests

**Disclosable Financial Interests:**
1. Compensation to investigator where any payment is tied to study outcome
2. Proprietary interest in the product (patent, trademark, copyright, licensing)
3. Equity interest in sponsor (exceeding $50,000)
4. Significant payments of other sorts (exceeding $25,000 annually for services not directly related to study)

**Disclosure Process:**
- Investigators complete financial disclosure form annually and at study completion
- Submit to sponsor
- Sponsor maintains disclosure records
- Sponsor submits to FDA with marketing application

**Conflict Management:**
- Sponsor reviews disclosures
- If potential COI identified: Assess whether COI could affect data integrity
- Mitigation strategies:
  - Increased monitoring
  - Independent data verification
  - Exclude investigator from study
  - Disclose COI to IRB and in publications
- IRB may review and approve or require additional mitigation

#### 10.13 Additional Considerations (20-40 lines):

**Study-Specific Operational Details:**
- [Include any study-specific operational considerations not covered elsewhere]
- [Example: Special equipment requirements, special laboratory procedures, biospecimen handling, imaging core lab procedures, centralized assessments]

**Emergency Procedures (if applicable):**
- Emergency contact information for study team (24/7)
- Emergency unblinding procedures (reference Section 7.4)
- Management of medical emergencies related to intervention (reference Section 7.2 or 9.3)

**Special Equipment or Facility Requirements:**
- [Specify if study requires special equipment, facilities, certifications]
- [Example: "Sites must have capability for 24-hour monitoring for first infusion"]

#### 10.14 Abbreviations (30 lines):

**Generate comprehensive abbreviation list in alphabetical order.**

Include all abbreviations used in protocol.

**Format:** Abbreviation | Full Term

**Example abbreviations (generate complete list specific to protocol):**
- AE: Adverse Event
- ALT: Alanine Aminotransferase
- ANCOVA: Analysis of Covariance
- ANC: Absolute Neutrophil Count
- AST: Aspartate Aminotransferase
- BP: Blood Pressure
- CFR: Code of Federal Regulations
- CI: Confidence Interval
- CrCl: Creatinine Clearance
- CRF: Case Report Form
- CT: Computed Tomography
- CTCAE: Common Terminology Criteria for Adverse Events
- DSMB: Data Safety Monitoring Board
- ECG: Electrocardiogram
- eCRF: Electronic Case Report Form
- EDC: Electronic Data Capture
- FDA: Food and Drug Administration
- GCP: Good Clinical Practice
- HIPAA: Health Insurance Portability and Accountability Act
- HR: Hazard Ratio
- ICF: Informed Consent Form
- ICH: International Council for Harmonisation
- IDE: Investigational Device Exemption
- IFU: Instructions for Use
- IND: Investigational New Drug
- IRB: Institutional Review Board
- ITT: Intent-to-Treat
- IV: Intravenous
- LVEF: Left Ventricular Ejection Fraction
- MedDRA: Medical Dictionary for Regulatory Activities
- MMRM: Mixed Model for Repeated Measures
- MRI: Magnetic Resonance Imaging
- OR: Odds Ratio
- PD: Pharmacodynamics
- PI: Principal Investigator
- PK: Pharmacokinetics
- PMA: Premarket Approval
- PP: Per-Protocol
- PRO: Patient-Reported Outcome
- QTc: Corrected QT Interval
- RCT: Randomized Controlled Trial
- SAE: Serious Adverse Event
- SD: Standard Deviation
- SOC: System Organ Class
- SoA: Schedule of Activities
- SOP: Standard Operating Procedure
- SUSAR: Suspected Unexpected Serious Adverse Reaction
- ULN: Upper Limit of Normal
- WOCBP: Women of Childbearing Potential

[Generate complete list specific to this protocol]

---

### Section 11: REFERENCES (60-150 lines)

**Generate 30-60 references organized by category using Step 1 research data.**

#### A. FDA Guidance Documents (5-10 from Phase 1):
FDA. [Title]. [Date]. Available at: [URL]
[List guidance documents from Phase 1 relevant to indication/intervention]

#### B. Similar Clinical Trials (10-20 from Phase 1):
[Authors]. [Title]. [Journal]. [Year];[Vol]:[Pages]. ClinicalTrials.gov Identifier: NCT[number].
[List similar trials that informed protocol design from Phase 1]

#### C. Device-Specific References (IF device - 5-10):
- FDA. [Predicate Device] 510(k) Summary. K[number]. [Date]. Available at: https://www.accessdata.fda.gov/...
- FDA. De Novo Classification Order for [Device]. DEN[number]. [Date]. Available at: https://www.accessdata.fda.gov/...
- FDA. [Device] Classification. Product Code: [ABC]. Available at: https://www.accessdata.fda.gov/scripts/cdrh/cfdocs/cfPCD/classification.cfm
- FDA. Class II Special Controls Guidance: [Device Type]. [Date]. Available at: https://www.fda.gov/...

#### D. Background Literature (10-20):
[Standard citation format - AMA or Vancouver style]
[Key publications on disease, intervention mechanism, prior studies]

#### E. Intervention Documentation (2-5):
- [Manufacturer]. [Drug/Device Name] Investigator's Brochure/IFU. Version [X]. [Date]. [Mark TBD if needed]
- [Manufacturer]. [Device Name] Technical Specifications. [Date]. [Mark TBD if applicable]

#### F. Regulatory References (5-10):
1. FDA. 21 CFR Part 50: Protection of Human Subjects. Available at: https://www.accessdata.fda.gov/scripts/cdrh/cfdocs/cfcfr/CFRSearch.cfm?CFRPart=50
2. FDA. 21 CFR Part 56: Institutional Review Boards. Available at: https://www.accessdata.fda.gov/scripts/cdrh/cfdocs/cfcfr/CFRSearch.cfm?CFRPart=56
3. FDA. 21 CFR Part 312 (Drugs) OR 21 CFR Part 812 (Devices). Available at: https://www.accessdata.fda.gov/scripts/cdrh/cfdocs/cfcfr/...
4. ICH E6(R2): Guideline for Good Clinical Practice. Nov 2016. Available at: https://database.ich.org/sites/default/files/E6_R2_Addendum.pdf
5. WMA Declaration of Helsinki: Ethical Principles for Medical Research. 2013. Available at: https://www.wma.net/policies-post/...
[Additional FDA/EMA guidance relevant to intervention/indication]

---

### Step 5: Create Operations File

Create `waypoints/04_protocol_operations.md` with Sections 8-11 only.

**Procedure:**
1. Generate Section 8 content
2. Generate Section 9 content (using sample size calculation results)
3. Generate Section 10 content
4. Generate Section 11 content
5. Write all sections to new file `waypoints/04_protocol_operations.md`
6. Confirm file creation successful

**Note:** The final concatenation of all sections will be performed in Step 5.

### Step 6: Update Protocol Metadata

Update `waypoints/02_protocol_metadata.json`:
- Set `step_4_status` to "completed"
- Add sections 9, 10, 11, 12 to `sections_completed` array
- Update `protocol_status` to "sections_complete" (final concatenation pending)
- Add `waypoint_files` object tracking all protocol section files
- Update notes

**Example:**
```json
{
  "intervention_id": "[from metadata]",
  "intervention_name": "[from metadata]",
  "protocol_version": "1.0 Draft",
  "protocol_date": "[current date]",
  "study_design": "[from Phase 1]",
  "enrollment_target": "[from sample size calculation: adjusted_n_total]",
  "primary_endpoint": "[from Section 4]",
  "duration_months": "[from Phase 1 or generated]",
  "regulatory_pathway": "[IDE or IND]",
  "protocol_status": "sections_complete",
  "waypoint_files": {
    "foundation": "02_protocol_foundation.md",
    "intervention": "03_protocol_intervention.md",
    "operations": "04_protocol_operations.md"
  },
  "step_2_status": "completed",
  "step_3_status": "completed",
  "step_4_status": "completed",
  "sections_completed": [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
  "sections_pending": [],
  "sample_size_calculated": true,
  "sample_size_n_per_arm": "[from calculation]",
  "sample_size_n_total": "[from calculation]",
  "notes": [
    "DRAFT for planning purposes",
    "All sections (1-12) generated",
    "Final concatenation pending in Step 5",
    "Sample size calculation completed",
    "Requires biostatistician review",
    "Requires clinical expert review",
    "Requires IRB approval",
    "Requires FDA feedback"
  ]
}
```

### Step 7: Update Intervention Metadata

Update `waypoints/intervention_metadata.json`:
- Add "04-protocol-operations" to `completed_steps` array
- Set `protocol_status` to "sections_complete"

### Step 8: Display Summary

Display concise summary with:
- Intervention name, protocol version, date
- Step 4 completion status
- ALL Sections generated: 1-12
- Operations file created with size
- Sample size calculation results
- DRAFT disclaimer
- Next steps: Proceed to Step 5 for final protocol concatenation

**Example output:**
```
✅ Step 4: Operations and Statistics - COMPLETED
✅ ALL PROTOCOL SECTIONS GENERATED

Intervention: [Name]
Protocol: Version 1.0 Draft (2025-12-03)

📊 Sample Size Calculation:
  • Primary Endpoint: [Endpoint name]
  • Sample Size Per Arm: [n_per_arm]
  • Total Enrollment Target: [adjusted_n_total]
  • Power: [power]%, Alpha: [alpha]

Protocol Status: All 12 Sections Generated
  ✓ Section 1: Statement of Compliance
  ✓ Section 2: Protocol Summary
  ✓ Section 3: Introduction
  ✓ Section 4: Objectives and Endpoints
  ✓ Section 5: Study Design
  ✓ Section 6: Study Population
  ✓ Section 7: Study Intervention
  ✓ Section 8: Discontinuation
  ✓ Section 9: Study Assessments (with AE/SAE reporting)
  ✓ Section 10: Statistical Considerations (with sample size)
  ✓ Section 10: Supporting Documentation and Operations
  ✓ Section 11: References

Files Created/Updated:
  • waypoints/04_protocol_operations.md (NEW: Sections 8-11, ~[lines] lines)
  • waypoints/02_protocol_foundation.md (Sections 1-5)
  • waypoints/03_protocol_intervention.md (Sections 6-7)
  • waypoints/02_protocol_metadata.json (UPDATED)
  • waypoints/02_sample_size_calculation.json (CREATED)
  • waypoints/intervention_metadata.json (UPDATED)

⚠️  DRAFT STATUS: This protocol is preliminary and requires:
  • Biostatistician review and validation of sample size
  • Clinical expert review of all content
  • IRB approval before implementation
  • FDA Pre-Submission or IND/IDE feedback
  • Legal/compliance review

Next Steps:
  1. Proceed to Step 5 to concatenate all sections into final protocol
  2. Review complete protocol after Step 5
  3. Validate sample size calculation with biostatistician
  4. Submit to FDA for Pre-Submission meeting (if applicable)
  5. Submit to IRB for approval
```

## Output Files

**Created:**
- `waypoints/04_protocol_operations.md` (Sections 8-11)
- `waypoints/02_sample_size_calculation.json` (sample size calculation results)

**Updated:**
- `waypoints/02_protocol_metadata.json` (step 4 marked complete, waypoint_files added)
- `waypoints/intervention_metadata.json` (step 4 marked complete)

**Existing (from prior phases):**
- `waypoints/02_protocol_foundation.md` (Sections 1-6 from Step 2)
- `waypoints/03_protocol_intervention.md` (Sections 7-8 from Step 3)

**To be created in Step 5:**
- `waypoints/protocol_complete.md` (Final concatenated protocol with all 12 sections)

## Error Handling

**If Step 3 not completed:**
```
Error: Step 3 must be completed first.
Current status: step_3_status = [status]

Please complete Step 3 to generate intervention details (Sections 7-8) before proceeding to Phase 4.
```

**If protocol section files missing:**
```
Error: Required protocol section files not found.
Expected:
  - waypoints/02_protocol_foundation.md (Phase 2 output)
  - waypoints/03_protocol_intervention.md (Phase 3 output)

Please ensure Phases 2 and 3 are completed before proceeding to Phase 4.
```

**If sample size calculation fails:**
```
Warning: Sample size calculation could not be performed.
Error: [error message]

Falling back to pattern-based approach using similar trials from Phase 1.
⚠️  IMPORTANT: Sample size requires biostatistician review and validation.

Proceeding with protocol generation using enrollment target from similar trials.
```

```

## Quality Checks

Before finalizing, verify:
- [ ] Sample size calculation completed successfully (or fallback with disclaimer)
- [ ] Section 8 generated with ALL 9 AE/SAE subsections (8.3.1-8.3.9)
- [ ] Section 9 generated with ALL 10 statistical subsections (9.4.1-9.4.10)
- [ ] Sample size section uses actual values from calculation JSON file
- [ ] Section 10 includes all operational subsections
- [ ] Section 11 includes 30-60 references organized by category
- [ ] Content appended successfully to existing protocol draft
- [ ] Protocol metadata updated correctly
- [ ] Intervention metadata updated correctly
- [ ] COMPLETE protocol now contains all 11 sections

## Notes

- **Sample size calculation is interactive** - requires user input
- Output stays within token limits by focusing on Sections 8-11 only
- **This phase generates the final sections** - all 11 sections now generated but not yet concatenated
- User must proceed to Step 5 for final protocol concatenation
