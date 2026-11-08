---
license: Provided under Anthropic's Terms of Service (not the Apache-2.0 LICENSE.txt used by most skills in this repo) — see NOTICE.md
source: https://github.com/anthropics/healthcare/tree/main/plugins/healthcare/skills/prior-auth
name: prior-auth-review-skill
description: Automate payer review of prior authorization (PA) requests. This skill should be used when users say "Review this PA request", "Process prior authorization for [procedure]", "Assess medical necessity", "Generate PA decision", or when processing clinical documentation for coverage policy validation and authorization decisions.
---

# Prior Authorization Review Skill

## Overview

This skill automates the payer review process for prior authorization (PA) requests. It processes clinical documentation, validates medical necessity against coverage policies, and generates authorization decisions with supporting rationale.

**Target Users:** Health insurance payer organizations (Medicare Advantage, Commercial, Medicaid MCOs)

**Value Proposition:** Reduce PA review time from 30-60 minutes to under 5 minutes. Enable auto-approval for 40-60% of clear-cut cases.

---

## Architecture

This skill uses a **simplified 2-subskill workflow**:

```
Subskill 1: Intake & Assessment
  ↓ (validates data, extracts clinical info, assesses medical necessity)
Subskill 2: Decision & Notification
  ↓ (generates auth decision with provider notification)

ONLY REVIEW THE SUBSKILL FILES WHEN THEY ARE NEEDED, DONT PRE-READ THE WHOLE SKILL ON BOOTUP

Output: Authorization Decision Package
```

### Waypoint Files

```
waypoints/
├── assessment.json          # Subskill 1 output (consolidated)
└── decision.json           # Subskill 2 output (final decision)
```

---

## Prerequisites

### Required MCP Servers

This skill requires 3 healthcare MCP connectors:

1. **CMS Coverage MCP Connector** - Medicare coverage policies (NCDs, LCDs)
2. **ICD-10 MCP Connector** - Diagnosis code validation and lookup
3. **NPI MCP Connector** - Healthcare provider verification via NPPES

**For detailed tool usage, parameters, and CMS web resources, see [references/01-intake-assessment.md](references/01-intake-assessment.md#prerequisites).**

### MCP Invocation Notifications

During execution, the skill displays notifications before and after each MCP connector call:
- Before: "Verifying provider credentials via NPI MCP Connector..."
- After: "NPI MCP Connector completed successfully - Provider verified: Dr. [Name]"
- Before: "Validating diagnosis codes via ICD-10 MCP Connector..."
- After: "ICD-10 MCP Connector completed successfully - [N] codes validated"
- Before: "Searching coverage policies via CMS Coverage MCP Connector..."
- After: "CMS Coverage MCP Connector completed successfully - Found policy: [Policy ID]"
- Before: "Validating procedure codes via CMS Fee Schedule..."
- After: "CPT/HCPCS codes validated via CMS Fee Schedule - [N] codes checked"

### File Structure

See README.md File Organization section for complete directory structure and file descriptions.

---

## Decision Policy

This skill enforces a **decision policy rubric** that determines the outcome when validation checks fail. The policy balances regulatory compliance, patient safety, and operational efficiency.

**See [references/rubric.md](references/rubric.md) for:**
- Complete decision policy matrix (STRICT vs LENIENT enforcement)
- Detailed decision logic flow and pseudocode
- Override authority rules
- Customization examples (lenient mode, strict compliance mode, auto-approval mode)

**Quick Summary:**
- **STRICT policies** → Automatic DENY (provider verification, invalid codes, criteria NOT_MET)
- **LENIENT policies** → Automatic PEND (insufficient evidence, missing policy)
- **Default fallback** → PEND (when unclear)

To customize decision logic for your organization, edit [references/rubric.md](references/rubric.md).

---

## How to Use

### Process PA Request

Simply invoke the skill:

```
Use the prior-auth-review-skill
```

The skill will:
1. Check for incomplete requests (auto-resume if found)
2. Collect PA request details
3. Execute Subskill 1: Intake & Assessment
4. Execute Subskill 2: Decision & Notification
5. Output authorization decision package

---

## Execution Flow

When this skill is invoked:

### Startup: Check MCP Configuration

**Before proceeding, verify required MCP connectors are available.**

Check for the following MCP connectors:
1. **CMS Coverage MCP** - Required for coverage policy lookup
2. **ICD-10 MCP** - Required for diagnosis code validation
3. **NPI MCP** - Required for provider verification

**If any MCP connectors are not configured:**

Display error and exit:
> "Missing required MCP connectors: [list missing connectors]. This skill requires all three healthcare MCP connectors to function. Please configure the missing connectors and try again. See README Prerequisites for setup instructions."

Exit skill.

**If all MCP connectors are available:** Proceed silently to next step.

---

### Startup: Request Input Files

**Prompt the user to provide input files or use sample data.**

Display the following prompt:

```
Prior Authorization Review requires the following input files:

REQUIRED FILES:
1. Prior Authorization Request Form (PDF) - Contains member info, requested service, provider details
2. Clinical Notes / H&P (PDF) - History and physical examination documentation
3. Diagnostic Imaging Reports (PDF) - CT, MRI, X-ray, or other imaging results
4. Laboratory Results (PDF) - Relevant lab work supporting medical necessity
5. Additional Supporting Documentation (PDF, optional) - PFTs, specialist consults, etc.

OPTIONS:
(A) Upload your own files - Provide paths to each required document
(B) Use sample files - Load pre-configured sample case (CT-guided lung biopsy)

Enter your choice (A/B): ___
```

**If user selects (A) - Upload own files:**
- Prompt for path to each required file
- Validate files exist and are readable
- Store file paths for use in Subskill 1
- Set `using_sample_files = False`

**If user selects (B) - Use sample files:**
- Load sample files from `assets/sample/`:
  - `01_Prior_Auth_Request_Form.pdf`
  - `02_Clinical_Notes_H_and_P.pdf`
  - `03_CT_Chest_Report.pdf`
  - `04_Laboratory_Results.pdf`
  - `05_Pulmonary_Function_Tests.pdf`
- Display: "Loading sample case: CT-guided transbronchial lung biopsy for 1.2cm RUL nodule"
- Set `using_sample_files = True`
- **Demo mode note:** When sample files are used, the sample data contains demo NPI (`1234567890`) and sample member ID (`1EG4-TE5-MK72`). This combination triggers demo mode, which skips the NPI MCP lookup for this specific provider only. All other MCP calls (ICD-10 validation, CMS Coverage policy search) execute normally.

---

### Startup: Check for Existing Request

**Check if `waypoints/assessment.json` exists:**

- **If exists and incomplete:**
  ```
  Found incomplete PA request: [Request ID]
  Resume this request? (Y/N): ___
  ```
  - If **Y**: Load assessment and continue to Subskill 2
  - If **N**: Archive and start new

- **If does not exist:**
  - Start from Subskill 1

### Subskill 1: Intake & Assessment

**Execute:** Read and follow `references/01-intake-assessment.md`

**What it does:**
1. Collect PA request information
2. Validate provider credentials and codes (parallel MCP calls)
3. Search coverage policies
4. Extract clinical data
5. Assess medical necessity against policy criteria
6. Generate recommendation (APPROVE/DENY/PEND)

**Output:** `waypoints/assessment.json` (consolidated)

**Duration:** 3-4 minutes

**Ask user:**
```
Ready to proceed to Subskill 2? (Y/N): ___
```
- If **Y**: Continue to Subskill 2
- If **N**: Save and exit

### Subskill 2: Decision & Notification

**Execute:** Read and follow `references/02-decision-notification.md`

**What it does:**
1. Load assessment from Subskill 1
2. Confirm or override recommendation
3. Generate decision-specific content:
   - **Approval:** Auth number, validity dates, limitations
   - **Denial:** Specific reasons, policy references, appeal rights
   - **Pend:** Documentation requests, submission deadline
4. Create provider notification letter
5. Document audit trail

**Output:**
- `waypoints/decision.json` (final decision)
- `outputs/notification_letter.txt` (provider notification)

**Duration:** 1-2 minutes

### Final Summary

Display a concise completion message with:
- Request details (ID, member, service, decision outcome)
- Authorization number and validity dates (if approved)
- Files generated (waypoints and notification)
- Next steps based on decision type

Offer user options to:
1. View decision letter
2. Start new PA review
3. Exit

---

## Error Handling

**Missing MCP Servers:**
If required MCP connectors not available, display error listing missing connectors and Removefully.

**Missing Subskill Prerequisites:**
If Subskill 2 invoked without `waypoints/assessment.json`, notify user to complete Subskill 1 first.

**File Write Errors:**
If unable to write waypoint files, display error with file path, check permissions/disk space, and offer retry.

**Data Quality Issues:**
If clinical data extraction confidence <60%, warn user with confidence score and low-confidence areas. Offer options to: continue, request additional documentation, or abort.

For all errors, provide clear, actionable messages and user options for resolution.

---

## Quality Checks

Before completing workflow, verify:

- [ ] All required waypoint files created
- [ ] Decision has clear rationale documented
- [ ] All required fields populated
- [ ] Output files generated successfully

---

## Implementation Requirements

1. **Always read subskill files:** Don't execute from memory. Read the actual subskill markdown file and follow instructions.

2. **Auto-detect resume:** Check for existing `waypoints/assessment.json` on startup. If found and status is not "assessment_complete", offer to resume.

3. **Parallel MCP execution:** In Subskill 1, execute NPI, ICD-10, and Coverage MCP calls in parallel for optimal performance.

4. **Preserve user data:** Never overwrite waypoint files without asking confirmation or backing up.

5. **Clear progress indicators:** Show users what's happening during operations (MCP queries, data analysis).

6. **Graceful degradation:** If optional data missing, continue with available data and note limitations.

7. **Validate outputs:** Check that waypoint files have expected structure before proceeding.

### MCP Tool Call Transparency (REQUIRED)

**CRITICAL:** Every time you invoke an MCP tool or WebFetch for code validation:

**BEFORE the call:**
- Display a simple notification explaining which connector is being used and what data is being queried
- Example: "Verifying provider credentials via NPI MCP Connector..."

**AFTER receiving results:**
- Display a brief summary of findings
- Example: "NPI MCP Connector completed successfully - Provider verified: Dr. [Name] ([Specialty])"

**If there's an issue:**
- Explain what went wrong and what happens next
- Example: "NPI verification failed - Provider NPI not found in database. This will result in automatic DENY per policy."

**Benefits:**
- Provides audit trail of all data sources consulted
- Demonstrates thoroughness of review process
- Highlights MCP connector capabilities
- Makes AI decision-making transparent and explainable
- Helps users understand what information drives recommendations

**Requirements:**
- Display notification BEFORE and AFTER each MCP/WebFetch call
- Keep notifications concise and informative
- Always include brief summary of findings
- Apply to ALL data lookups: NPI, ICD-10, CMS Coverage, and CPT/HCPCS validation

### Common Mistakes to Avoid

- ❌ Don't generate fake data when MCP queries fail
- ❌ Don't skip prerequisite checks
- ❌ Don't overwrite existing files without checking
- ❌ Don't proceed if current subskill had errors
- ❌ Don't call ICD-10 MCP multiple times for same codes
- ✅ DO provide clear, actionable error messages
- ✅ DO give users options when things go wrong
- ✅ DO validate data quality at each step
- ✅ DO execute MCP calls in parallel where possible

---

## Subskill Descriptions

### Subskill 1: Intake & Assessment (3-4 minutes)
- Collects PA request details (member, service, provider, clinical docs)
- Validates provider credentials via **NPI MCP**
- Validates and retrieves ICD-10 code details via **ICD-10 MCP** (single batch call)
- Validates CPT/HCPCS codes via **WebFetch to CMS Fee Schedule**
- Searches coverage policies via **CMS Coverage MCP**
- Extracts structured clinical data from documentation
- Maps clinical evidence to policy criteria
- Performs medical necessity assessment
- Generates recommendation (APPROVE/DENY/PEND)
- **Output:** `waypoints/assessment.json` (consolidated)
- **Data Sources:** NPI MCP, ICD-10 MCP, CMS Coverage MCP (parallel), CMS Fee Schedule (web)

### Subskill 2: Decision & Notification (1-2 minutes)
- Loads assessment from Subskill 1
- Confirms or allows override of recommendation
- Generates authorization number (if approved) or denial rationale (if denied)
- Creates provider notification letter
- Documents complete audit trail
- **Output:** `waypoints/decision.json` and notification letter

