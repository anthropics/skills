# Subskill 1: Intake & Assessment

## Purpose

Collect prior authorization request information, validate credentials and codes, extract clinical data, identify applicable coverage policies, assess medical necessity, and generate approval recommendation - all in a single consolidated subskill.

## Prerequisites

### Required MCP Servers

This subskill uses 3 MCP connectors for healthcare data validation:

1. **NPI MCP Connector** - Provider verification
   - **Tools:** `npi_lookup_provider(npi="...")`, `npi_verify_credentials(...)`
   - **Use Cases:** Verify provider credentials, specialty, license state, active status
   - **Success Notification:** `✅👨‍⚕️ NPI MCP Connector invoked successfully`

2. **ICD-10 MCP Connector** - Diagnosis code validation
   - **Tools:** `icd10_validate(codes=[...])`, `icd10_get_details(code="...")`, `icd10_search_codes(...)`
   - **Use Cases:** Batch validate ICD-10 codes, get detailed code information (descriptions, billable status, chapter info)
   - **Success Notification:** `✅🔢 ICD-10 MCP Connector invoked successfully`

3. **CMS Coverage MCP Connector** - Coverage policy search and retrieval
   - **Tools:** `cms_search_all(...)`, `cms_lcd_details(...)`
   - **Use Cases:** Find applicable LCDs/NCDs, retrieve detailed coverage criteria, check covered codes
   - **Success Notification:** `✅📋 CMS Coverage MCP Connector invoked successfully`

### CPT/HCPCS Code Validation (Web-based)

If a custom MCP connector is available for CPT/HCPCS procedure codes, put it here.  Otherwise, use WebFetch to official CMS websites:

**Allowed Resources:**
- **Primary:** Physician Fee Schedule - https://www.cms.gov/medicare/physician-fee-schedule/search
- **Secondary:** NCCI Edits - https://www.cms.gov/medicare/coding-billing/national-correct-coding-initiative-ncci-edits
- **Reference:** Provider Taxonomy - https://taxonomy.nucc.org/

**Success Notification:** `✅💳 CPT/HCPCS codes validated via CMS Fee Schedule`

**Policy:** Only use WebSearch and WebFetch to official CMS/NUCC sites listed above.

## What This Subskill Does

1. Collects PA request details (member, service, provider, clinical documentation)
2. Validates provider credentials and medical codes via MCP connectors (parallel execution)
3. Searches for applicable coverage policies
4. Extracts clinical data and maps to policy criteria
5. Performs medical necessity assessment
6. Generates recommendation (APPROVE/DENY/PEND)

---

## Execution Flow

### Step 1: Collect PA Request Information

Inform the user you're starting the prior authorization request process.

**Collect the following:**

1. **Member Information:**
   - Member Name: [First Last]
   - Member ID: [Insurance ID]
   - Date of Birth: [MM/DD/YYYY]
   - State: [State abbreviation]

2. **Requested Service:**
   - Service Type: [Procedure/Medication/Imaging/Device/Therapy/Facility]
   - Description: [Brief description]
   - CPT/HCPCS Codes: [Comma-separated list]
   - ICD-10 Diagnosis Codes: [Comma-separated list]

3. **Provider Information:**
   - Ordering Provider NPI: [10-digit NPI]

4. **Clinical Documentation:**
   - Paste clinical notes, upload file, or provide summary
   - Accept multi-line text input

**Generate Request ID:**
```
request_id = f"{member_id}_{timestamp}"
Example: "1EG4TE5MK72_20251207_143022"
```

---

### Step 2: Parallel MCP Validation

Inform the user you're validating credentials and codes.

**Execute the following in parallel for efficiency:**

1. **NPI Lookup** via NPI MCP:

   **First, check for demo/test mode:**

   Demo mode activates ONLY when BOTH conditions are met:
   1. NPI is a recognized demo NPI: `1234567890` or `1234567893`
   2. Member ID matches sample data: `1EG4-TE5-MK72` or `1EG4TE5MK72`

   **IMPORTANT: Demo mode ONLY affects NPI lookup.** All MCP servers must still be connected and operational. Demo mode does NOT skip:
   - ICD-10 MCP validation (still required)
   - CMS Coverage MCP policy search (still required)
   - Any other MCP calls

   If BOTH conditions are met (demo mode):
   - Skip NPPES lookup for this specific NPI only
   - Set `provider_verified = True`
   - Display: "Demo mode: Skipping NPPES lookup for sample NPI. Note: All other MCP validations (ICD-10, CMS Coverage) still apply."
   - Use placeholder provider details: "Demo Provider, MD (Specialty from request)"
   - Proceed with remaining validations (ICD-10, CMS Coverage, etc.)

   If only NPI matches but member ID does not match sample data:
   - Treat as real NPI and proceed with normal NPPES lookup
   - This prevents accidental demo mode activation in production

   **For real NPIs (or demo NPI without matching sample member ID):**

   Display: "Verifying provider credentials via NPI MCP Connector..."

   ```python
   npi_lookup_provider(npi="[provided_npi]")
   ```
   - Verify provider credentials, specialty, license state
   - Confirm active status

   After successful call, display: "NPI MCP Connector completed successfully - Provider verified: Dr. [Name] ([Specialty])"

2. **ICD-10 Validation & Details** via ICD-10 MCP:

   Display: "Validating diagnosis codes via ICD-10 MCP Connector..."

   ```python
   # Batch validate all codes first
   icd10_validate(codes=[])

   # Then get details for each code (can be done in parallel)
   for code in []:
       icd10_get_details(code=code)
   ```
   - Validate all codes in single call
   - Get full details (descriptions, billable status, chapter info) for each
   - Store for use in policy criteria matching

   After successful call, display: "ICD-10 MCP Connector completed successfully - [N] codes validated"

3. **Coverage Policy Search** via CMS Coverage MCP:

   Display: "Searching coverage policies via CMS Coverage MCP Connector..."

   ```python
   cms_search_all(
       search_term="[service description]",
       state="[member_state]",
       max_results=10
   )
   ```
   - Find applicable LCDs/NCDs for service

   After successful call, display: "CMS Coverage MCP Connector completed successfully - Found policy: [Policy ID] - [Title]"

   **Important:** Also display contextual limitation notice:
   > "Note: Coverage policies are sourced from Medicare LCDs/NCDs. If this review is for a commercial or Medicare Advantage plan, payer-specific policies may differ."

**If provider not found:**

Display error: "Provider NPI [number] not found or inactive. Per rubric.md policy, requests without verified provider will result in PENDING status (request credentialing documentation)."

Offer options:
1. Provide corrected NPI and retry validation
2. Continue (recommendation will be PENDING per rubric)
3. Abort review

**Note:** If user selects option 2 or provider verification fails, `provider_verified = False` must be stored. See rubric.md for how this affects the recommendation.

**If no policy found:**

Display warning: "No coverage policy found for this service. This may indicate service not typically covered."

Offer options:
1. Continue with general medical necessity review
2. Abort review

---

### Step 2b: CPT/HCPCS Code Validation

Display: "Validating procedure codes via CMS Fee Schedule..."

**For each CPT/HCPCS code provided:**

```python
# Use CMS Physician Fee Schedule to validate codes
for code in cpt_hcpcs_codes:
    result = WebFetch(
        url=f"https://www.cms.gov/medicare/physician-fee-schedule/search?Y=0&T=4&P=0&L={code}",
        prompt="Extract the following information: 1) Is this CPT/HCPCS code valid and currently active? 2) Short description of the procedure/service 3) Status (active/inactive/deprecated)"
    )

    # Store code details for assessment
    code_details[code] = {
        "valid": result.is_valid,
        "description": result.description,
        "status": result.status
    }

    # If code not found or invalid, warn user
    if not result.is_valid:
        display(f"WARNING: CPT/HCPCS code {code} not found or invalid")
```

After successful validation, display: "CPT/HCPCS codes validated via CMS Fee Schedule - [N] codes checked"

Display brief summary of validated codes with descriptions and status.

**If invalid code found:**

Display error: "Invalid CPT/HCPCS Code [code]. Reason: Not found in CMS Fee Schedule / Deprecated / Invalid format. Per rubric.md policy, requests with invalid codes will result in PENDING status (request code clarification)."

Offer options:
1. Provide corrected code and retry validation
2. Continue (recommendation will be PENDING per rubric)
3. Abort review

**Note:** If user selects option 2 or code validation fails, the invalid code status must be stored. See rubric.md for how this affects the recommendation.

---

### Step 3: Extract Clinical Data

Inform the user you're extracting clinical data from documentation.

**Parse documentation to extract:**

- **Chief Complaint:** Primary reason for service
- **Diagnoses:** Conditions with severity
- **Clinical Findings:** Labs, imaging, exam findings (with dates)
- **Prior Treatments:** Previous therapies tried, dates, outcomes
- **Severity Indicators:** Symptoms, functional limitations, progression
- **Medical History:** Comorbidities, relevant history
- **Provider Assessment:** Clinical reasoning, justification

**Calculate Confidence:**
- Overall confidence = average of extraction confidence scores
- If < 60%, warn user about low confidence

Display brief summary: "Clinical data extracted (Confidence: [X]%) - Found chief complaint, [count] key findings, [count] prior treatments"

---

### Step 4: Get Detailed Policy Criteria

**If policy found in Step 2:**

Inform the user you're retrieving detailed policy criteria.

**Get LCD/NCD Details:**
```python
lcd_details = cms_lcd_details(
    lcd_id="[LCD_ID]",
    include_codes=True
)
```

**Extract:**
- Coverage criteria (requirements to meet)
- Covered indications (diagnoses)
- Documentation requirements
- Exclusions

Display summary: "Policy details retrieved: [Policy ID] - [Title] with [N] coverage criteria"

---

### Step 5: Medical Necessity Assessment

Inform the user you're assessing medical necessity against policy criteria.

**For Each Coverage Criterion:**

1. Search extracted clinical data for supporting evidence
2. Determine status: MET / NOT_MET / INSUFFICIENT
3. Document specific evidence and confidence

**Example Assessment:**
```python
{
    "criterion_number": 1,
    "criterion_text": "Imaging findings suggest need for tissue diagnosis",
    "status": "MET",
    "evidence": [
        "1.2cm RUL nodule on CT",
        "Growth from 8mm to 12mm over 6 months",
        "PET-CT SUV max 4.2 (metabolically active)"
    ],
    "notes": "Growth pattern highly suspicious for malignancy",
    "confidence": 95
}
```

**Calculate Recommendation:**

**IMPORTANT:** Read [rubric.md](rubric.md) FIRST to understand the current decision policy, then apply those rules.

**Steps:**
1. Read rubric.md to understand decision rules
2. Follow the evaluation order specified in rubric
3. Apply the actions (APPROVE/PEND/DENY) as defined in rubric
4. Generate recommendation with supporting rationale

Display assessment summary showing:
- Criteria status (MET/NOT_MET/INSUFFICIENT with confidence %)
- Evidence for each criterion
- Required criteria met count
- Overall confidence
- Recommendation (APPROVE/DENY/PEND) with rationale

---

### Step 5b: Generate Audit Justification Document

**Purpose:** Create a detailed, human-readable audit justification document for regulatory compliance and review.

**File:** `outputs/audit_justification.md`

Inform user: "Generating audit justification document..."

**Generate comprehensive Markdown report with the following sections:**

**0. Disclaimer Header (REQUIRED - must appear at top of document)**

```
⚠️ AI-ASSISTED DRAFT - REVIEW REQUIRED
Coverage policies reflect Medicare LCDs/NCDs only. If this review is for a
commercial or Medicare Advantage plan, payer-specific policies were not applied.
All decisions require human clinical review before finalization.
```

1. **Executive Summary**
   - Request ID, review date, reviewed by
   - Member details (name, ID, DOB)
   - Service description
   - Provider details (name, NPI, specialty)
   - Decision (APPROVE/DENY/PEND)
   - Overall confidence (percentage and level)

2. **Medical Necessity Assessment**
   - **Coverage Policy Applied:** Policy ID, title, type (LCD/NCD), contractor, source (CMS Coverage MCP Connector)
   - **Clinical Evidence Summary:** Chief complaint, key findings from documentation, prior treatments with outcomes, extraction confidence score

3. **Criterion-by-Criterion Evaluation**
   - For each coverage criterion:
     - Criterion text (the specific policy requirement)
     - Status (MET/NOT_MET/INSUFFICIENT) with visual indicator
     - Confidence percentage
     - **Supporting Evidence:** Numbered list of specific clinical facts from documentation
     - **Clinical Rationale:** Explanation of why criterion was met/not met/insufficient

4. **Validation Checks**
   - **Provider Verification:** NPI number, verification status, source (NPI MCP Connector), provider details (name, specialty, license state, active status)
   - **Diagnosis Code Validation:** Table with ICD-10 codes, descriptions, billable status, validation status, source (ICD-10 MCP Connector)
   - **Procedure Code Validation:** Table with CPT/HCPCS codes, descriptions, validation status, source (CMS Physician Fee Schedule)

5. **Decision Rationale**
   - Criteria met count (e.g., "5/5")
   - Key supporting facts (bullet list)
   - Policy compliance statement
   - Overall confidence level
   - Final recommendation

6. **Documentation Gaps** (if any)
   - List each gap with criticality level and impact on assessment

7. **Audit Trail**
   - **Data Sources Consulted:** List all MCP connectors and data sources used
   - **Review Timestamps:** Request received, assessment completed, total review time
   - **Quality Metrics:** Clinical extraction confidence, overall assessment confidence, average criteria evaluation confidence

8. **Regulatory Compliance**
   - Decision Policy Matrix checklist (provider verification, code validation, criteria evaluation results)
   - Appeals process information (if applicable for DENY decisions)

**Document footer:** Timestamp, system version

**Write file to:** `outputs/audit_justification.md`

Display: "Audit justification document created - outputs/audit_justification.md"

---

### Step 6: Documentation Gap Check

**Compare policy requirements to available data:**

```python
gaps = []
for required_doc in policy_documentation_requirements:
    if not found_in_clinical_data(required_doc):
        gaps.append({
            "what": required_doc,
            "critical": determine_if_critical(required_doc),
            "request": specific_request_text(required_doc)
        })
```

**Display if gaps exist:**

Inform user of documentation gaps, listing each gap with criticality level and specific request. Note that gaps exist but medical necessity can still be assessed if non-critical.

---

### Step 7: Code Alignment Check

**Using ICD-10 details from Step 2 and policy codes from Step 4:**

```python
submitted_codes = icd10_codes
policy_covered_codes = lcd_details['covered_icd10_codes']

# Simple set comparison
covered = set(submitted_codes) & set(policy_covered_codes)
non_covered = set(submitted_codes) - set(policy_covered_codes)
```

Display code alignment summary showing which ICD-10 codes match covered indications and which are secondary/comorbidity codes. Confirm primary diagnosis is covered.

---

### Step 8: Create Assessment Waypoint

**File:** `waypoints/assessment.json`

**Consolidated structure:**
```json
{
  "request_id": "...",
  "created": "ISO datetime",
  "status": "assessment_complete",

  "request": {
    "member": {"name": "...", "id": "...", "dob": "...", "state": "..."},
    "service": {"type": "...", "description": "...", "cpt_codes": [...], "icd10_codes": [...]},
    "provider": {"npi": "...", "name": "...", "specialty": "...", "verified": true/false}
  },

  "clinical": {
    "chief_complaint": "...",
    "key_findings": ["...", "..."],
    "prior_treatments": ["..."],
    "extraction_confidence": 0-100
  },

  "policy": {
    "policy_id": "...",
    "policy_title": "...",
    "policy_type": "LCD/NCD",
    "contractor": "...",
    "covered_indications": ["...", "..."]
  },

  "criteria_evaluation": [
    {"criterion": "...", "status": "MET/NOT_MET/INSUFFICIENT", "evidence": [...], "notes": "...", "confidence": 0-100}
  ],

  "recommendation": {
    "decision": "APPROVE/DENY/PENDING",
    "confidence": "HIGH/MEDIUM/LOW",
    "confidence_score": 0-100,
    "rationale": "...",
    "criteria_met": "N/N",
    "gaps": [{"what": "...", "critical": true/false, "request": "..."}]
  }
}
```

**Write file.**

---

### Step 9: Display Subskill Complete Summary

Display concise completion summary with:
- Subskill 1 complete status
- Request ID, member name/DOB, service description
- Coverage policy match (ID, title)
- Medical necessity results (criteria met count, overall confidence)
- Recommendation (APPROVE/DENY/PEND) with brief rationale
- Files created:
  - waypoints/assessment.json
  - outputs/audit_justification.md

Ask if ready to proceed to Subskill 2 (Y/N):
- If Y: Return to orchestrator to execute Subskill 2
- If N: Save state and exit

---

## Output Files

**Created:**
- `waypoints/assessment.json` - Consolidated assessment
- `outputs/audit_justification.md` - Detailed medical necessity justification for audit

---

## Error Handling

### MCP Connector Unavailable

Display error: "MCP Connector Unavailable - Cannot access required healthcare data connectors. This skill requires all three MCP connectors (CMS Coverage, ICD-10, NPI) to function. Please configure the missing connectors and try again. See README Prerequisites for setup instructions."

Exit subskill and return to main menu.

### Low Confidence Clinical Extraction

If overall confidence < 60%:

Display warning: "LOW CONFIDENCE WARNING - Extraction Confidence: [X]%"

List low confidence areas and offer options:
1. Continue (may result in pend/denial)
2. Request additional documentation
3. Abort

### Invalid Codes (ICD-10 or CPT/HCPCS)

**Per rubric.md:** Invalid codes result in automatic PENDING (request code clarification).

Display error: "Invalid Code [Code] - Type: [ICD-10/CPT/HCPCS], Reason: [details]. Per rubric.md policy, requests with invalid codes will result in PENDING status to request code clarification or corrected submission."

Offer options:
1. Provide corrected code and retry validation
2. Continue (recommendation will be PENDING per rubric)
3. Abort review

**Implementation Note:** Store validation failure status. Step 5 will check code validity per rubric.md decision rules.

---

## Quality Checks

Before completing Subskill 1:

- [ ] Request ID generated
- [ ] Provider credentials verified
- [ ] ICD-10 codes validated with details
- [ ] CPT/HCPCS codes validated via CMS Fee Schedule
- [ ] Coverage policy identified (or documented as not found)
- [ ] All policy criteria evaluated
- [ ] Recommendation generated
- [ ] Assessment file created with valid JSON
- [ ] Audit justification document created with all citations and evidence

---

## Notes for Claude

### Implementation Hints

1. **Parallel MCP calls save time:** Execute NPI, ICD-10, and Coverage searches concurrently in Step 2
2. **ICD-10 batch validation:** Use `icd10_validate(codes=[...])` for all codes at once, then `icd10_get_details(code=...)` for each individual code
3. **CPT validation is sequential:** WebFetch each CPT/HCPCS code to CMS Fee Schedule in Step 2b (no MCP available)
4. **Display MCP notifications:** Show success notifications after each MCP connector invocation for user visibility
5. **Policy-aware extraction:** Focus clinical extraction on what policy criteria need
6. **Be specific with evidence:** Document exact clinical facts supporting each criterion
7. **Honest confidence:** Low confidence should trigger warnings/human review

**Display notifications:**
- BEFORE each MCP/WebFetch call: Inform user which connector is being used and what data is being queried
- AFTER receiving results: Display brief summary of findings

**Why this matters:**
- Creates audit trail of all data sources
- Shows thoroughness of review process
- Makes decision-making transparent
- Highlights MCP capabilities to user

### Common Mistakes to Avoid

**MCP and Validation:**
- ❌ Don't call `icd10_validate()` multiple times - validate all codes in one batch
- ❌ Don't call `icd10_get_details()` with array parameter - it takes single code only
- ❌ Don't skip CPT/HCPCS validation - it's required even though no MCP exists
- ❌ Don't forget to display MCP success notifications after each connector invocation

**Decision Policy Enforcement (CRITICAL):**
- ❌ Don't ignore provider verification status when calculating recommendation
- ❌ Don't make decisions without first reading rubric.md
- ❌ Don't use outdated/hardcoded decision logic
- ✅ DO read rubric.md FIRST to understand current policy
- ✅ DO apply the decision rules specified in rubric.md
- ✅ DO store validation failure status (provider_verified, code validity) for Step 5

**Clinical Assessment:**
- ❌ Don't mark criteria as "MET" without specific evidence
- ✅ DO check validation status per rubric.md rules
- ✅ DO follow the evaluation order specified in rubric.md
- ✅ DO execute MCP calls in parallel where possible (Step 2)
- ✅ DO validate CPT codes via WebFetch to CMS Fee Schedule (Step 2b)
- ✅ DO display all success notifications for user visibility
- ✅ DO provide clear, specific evidence for each criterion
- ✅ DO flag borderline cases for human review
