# Step 1: Research Similar Clinical Protocols and Evidence

## Purpose
Research similar clinical trials, FDA guidance documents, and published protocols to inform clinical protocol development.

## Prerequisites
**Required Files:** `waypoints/intervention_metadata.json`
**Required Tools:** ClinicalTrials.gov MCP Server

## Status Reporting Protocol

**Always inform the user when performing regulatory research actions:**

| Action | Format |
|--------|--------|
| Database Query | `🔍 Searching [DATABASE] for [terms]...` |
| Document Review | `📄 Reviewing [TYPE]: [name/number]...` |
| Regulation Lookup | `📋 Checking [CFR REF] for [purpose]...` |
| Results Found | `✓ Found [N] results: [summary]` |
| No Results | `⚠️ No direct matches. Expanding search to [alternative]...` |

**Example grouped output:**
```
**Regulatory Database Research**
🔍 Searching Product Classification Database...
✓ Found: Product Code "GEX", Class II, 21 CFR 876.1500
🔍 Searching 510(k) Database for predicates...
✓ Found 12 cleared devices (filtering to top 5)
📄 Reviewing K201234 summary...
```

---

## Execution Flow

### Step 1: Load Intervention Metadata

Read `waypoints/intervention_metadata.json` for: intervention name, type (device/drug/biologics), description, indication, target population, initial context, discovery clarifications.

---

### Step 2: Device-Specific Regulatory Research
**ONLY if intervention_type is "device".**

**Reporting:** Inform the user when querying databases or reviewing documents.

<details open>
<summary><b>FDA Device Regulations & Databases</b></summary>

| Category | Resource | Use When | Link |
|----------|----------|----------|------|
| **Classification** | Product Classification Database | Determining device class/code | https://www.accessdata.fda.gov/scripts/cdrh/cfdocs/cfPCD/classification.cfm |
| | 21 CFR 860 | Understanding classification criteria | https://www.accessdata.fda.gov/scripts/cdrh/cfdocs/cfcfr/CFRSearch.cfm?CFRPart=860 |
| **510(k) Pathway** | 510(k) Database | Searching for predicate devices | https://www.accessdata.fda.gov/scripts/cdrh/cfdocs/cfpmn/pmn.cfm |
| | 21 CFR 807 Subpart E | Understanding 510(k) requirements | https://www.fda.gov/medical-devices/premarket-submissions-selecting-and-preparing-correct-submission/premarket-notification-510k |
| **De Novo Pathway** | De Novo Database | Finding novel device precedents | https://www.accessdata.fda.gov/scripts/cdrh/cfdocs/cfpmn/denovo.cfm |
| | 21 CFR 860.260 | Understanding De Novo process | https://www.fda.gov/medical-devices/premarket-submissions-selecting-and-preparing-correct-submission/de-novo-classification-request |
| **PMA Pathway** | PMA Database | Researching Class III approvals | https://www.accessdata.fda.gov/scripts/cdrh/cfdocs/cfpma/pma.cfm |
| | 21 CFR 814 | Understanding PMA requirements | https://www.fda.gov/medical-devices/premarket-submissions-selecting-and-preparing-correct-submission/premarket-approval-pma |
| **IDE/Clinical** | 21 CFR 812 | Determining SR/NSR status | https://www.accessdata.fda.gov/scripts/cdrh/cfdocs/cfcfr/CFRSearch.cfm?CFRPart=812 |
| | Clinical Trials Overview | Trial design guidance | https://www.fda.gov/medical-devices/device-advice-comprehensive-regulatory-assistance/clinical-trials-and-human-subject-protection |
| **Other** | GUDID | Device identifiers | https://accessgudid.nlm.nih.gov/ |
| | 21 CFR 820 (QSR) | Quality system requirements | https://www.accessdata.fda.gov/scripts/cdrh/cfdocs/cfcfr/CFRSearch.cfm?CFRPart=820 |
| | 21 CFR 800-1299 | General device regulations | https://www.accessdata.fda.gov/scripts/cdrh/cfdocs/cfcfr/CFRSearch.cfm |

</details>

#### Device Research Workflow

##### Step 2A.1: Device Classification

Query **Product Classification Database** for [device type from metadata].

**Extract:**
- **Device Class:** I, II, or III
- **Product Code:** (e.g., "GEX")
- **CFR Regulation:** 21 CFR XXX.XXXX
- **Special Controls:** (if Class II)
- **Device Name:** Official classification name

##### Step 2A.2: Pathway Decision

**IF Class III (high-risk):**
→ Execute **PMA Research Track** (Step 2A.3a)

**IF Class II (moderate-risk):**
→ Execute **510(k) Research Track** (Step 2A.3b)
→ IF no predicates found → Consider **De Novo Track** (Step 2A.3c)

**IF Class I:**
→ Check exemption status
→ IF exempt → Proceed to Step 3 (FDA Guidance Search)
→ IF not exempt → Execute **510(k) Research Track** (Step 2A.3b)

##### Step 2A.3a: PMA Research Track (Class III Only)

Query **PMA Database** for [device type].

**Extract from 3-5 approved PMAs:**
- **PMA Number, Device Name, Manufacturer**
- **Approval Date** (prioritize recent approvals)
- **Clinical Trial Design:** RCT, single-arm, sample size
- **Primary Endpoint** & success criteria
- **Pivotal Study Requirements:** Number of trials, duration
- **Post-approval Conditions:** (if any)

##### Step 2A.3b: 510(k) Research Track (Class I/II with Predicates)

Query **510(k) Database** for [device type].

**Extract from 3-5 recent predicates** (prioritize last 5-10 years, similar indication):
- **K-Number, Device Name, Manufacturer**
- **Clearance Date**
- **Indications for Use**
- **Technological Characteristics:** Design, materials, mechanism
- **Clinical Data:** Required? Type? Sample size?
- **Testing Performed:** Bench, animal, human studies?

##### Step 2A.3c: De Novo Research Track (Novel Device)

Query **De Novo Database** for [device type or similar mechanism].

**Extract from relevant De Novo grants:**
- **DEN Number, Device Name**
- **Classification Decision:** Class I or II determination
- **Special Controls Imposed:** (if Class II)
- **Clinical Evidence Required:** Study designs, sample sizes
- **Rationale:** Why low-moderate risk determination made

##### Step 2A.4: IDE Risk Determination (All Pathways)

Assess **Significant Risk (SR) vs Non-Significant Risk (NSR)** per 21 CFR 812.3(m):

| Factor | Evaluation Question | SR Signal |
|--------|---------------------|-----------|
| **Implanted?** | Permanent, >30 days, or invasive implant? | Yes → SR |
| **Life Support?** | Sustains or supports life? | Yes → SR |
| **Critical Diagnostic?** | Substantial importance to diagnosis/treatment? | Yes → SR |
| **Failure Risk?** | Serious injury or death possible from failure? | Yes → SR |
| **Precedent?** | Similar devices classified as SR/NSR? | Match precedent |

**Determination:**
- **SR (Significant Risk)** → Requires FDA IDE approval + IRB approval
- **NSR (Non-Significant Risk)** → IRB approval only

**Document:** Rationale with specific 21 CFR 812.3(m) criteria cited and precedent analysis.

---

### Step 2.2: Drug/Biologics-Specific Regulatory Research
**ONLY if intervention_type is "drug" or "biologics".**

**Reporting:** Inform the user when querying databases or reviewing documents.

<details open>
<summary><b>FDA Drug/Biologics Regulations & Databases</b></summary>

| Category | Resource | Use When | Link |
|----------|----------|----------|------|
| **IND Process** | 21 CFR 312 | IND requirements & regulations | https://www.accessdata.fda.gov/scripts/cdrh/cfdocs/cfcfr/CFRsearch.cfm?CFRPart=312 |
| | IND Overview | Understanding IND process | https://www.fda.gov/drugs/types-applications/investigational-new-drug-ind-application |
| | IND Content/Format | Preparing IND submission | https://www.fda.gov/media/71203/download |
| | IND Safety Reporting | Safety reporting requirements | https://www.fda.gov/regulatory-information/search-fda-guidance-documents/safety-reporting-requirements-inds-investigational-new-drug-applications-and-babe |
| | Sponsor-Investigator IND | Academic/investigator INDs | https://www.fda.gov/files/drugs/published/Investigational-New-Drug-Applications-Prepared-and-Submitted-by-Sponsor-Investigators.pdf |
| | When IND Required | Determining IND necessity | https://www.fda.gov/regulatory-information/search-fda-guidance-documents/investigational-new-drug-applications-inds-determining-whether-human-research-studies-can-be |
| **NDA Pathway** | 21 CFR 314 | NDA regulations | https://www.accessdata.fda.gov/scripts/cdrh/cfdocs/cfcfr/CFRSearch.cfm?CFRPart=314 |
| | NDA Overview | Understanding NDA process | https://www.fda.gov/drugs/types-applications/new-drug-application-nda |
| **ANDA Pathway** | ANDA Format Guidance | Preparing generic applications | https://www.fda.gov/files/drugs/published/ANDA-Submissions-%E2%80%94-Content-and-Format-of-Abbreviated-New-Drug-Applications.pdf |
| | Orange Book | Finding RLD for generics | https://www.accessdata.fda.gov/scripts/cder/ob/ |
| **505(b)(2) Pathway** | 505(b)(2) Guidance | Understanding 505(b)(2) pathway | https://www.fda.gov/regulatory-information/search-fda-guidance-documents/applications-covered-section-505b2 |
| | 505(b)(2) vs ANDA | Pathway selection guidance | https://www.fda.gov/regulatory-information/search-fda-guidance-documents/determining-whether-submit-anda-or-505b2-application |
| | 505(b)(2) Overview | Detailed pathway overview | https://www.fda.gov/media/156350/download |
| **BLA Pathway** | 21 CFR 601 | BLA regulations | https://www.accessdata.fda.gov/scripts/cdrh/cfdocs/cfcfr/CFRSearch.cfm?CFRPart=601 |
| | BLA Overview | Understanding BLA process | https://www.fda.gov/vaccines-blood-biologics/development-approval-process-cber/biologics-license-applications-bla-process-cber |
| | CBER INDs | Biologics IND guidance | https://www.fda.gov/vaccines-blood-biologics/development-approval-process-cber/investigational-new-drug-applications-inds-cber-regulated-products |
| | Purple Book | Biologics & biosimilars | https://purplebooksearch.fda.gov/ |
| **Databases** | Drugs@FDA | Approved drugs, labels, reviews | https://www.accessdata.fda.gov/scripts/cder/daf/ |
| | NDC Directory | Drug codes | https://www.accessdata.fda.gov/scripts/cder/ndc/ |
| **Submission** | eCTD Format | Electronic submission standards | https://www.fda.gov/drugs/electronic-regulatory-submission-and-review/electronic-common-technical-document-ectd |
| | CTD Organization | CTD structure guidance | https://www.fda.gov/media/71666/download |
| **Manufacturing** | 21 CFR 210-211 (cGMP) | Manufacturing requirements | https://www.accessdata.fda.gov/scripts/cdrh/cfdocs/cfcfr/CFRSearch.cfm?CFRPart=211 |

</details>

#### Drug/Biologics Research Workflow

##### Step 2B.1: Drug Classification Assessment

Query **Drugs@FDA** and **Orange Book** for [drug name from metadata].

**Determine:**
- **Novelty:** NCE (new chemical entity) vs previously approved moiety
- **Regulatory Status:**
  - OTC vs Rx (21 CFR 330-358)
  - Controlled substance? (21 CFR 1308, Schedule I-V)
- **Product Type:** Small molecule, biologic, biosimilar

##### Step 2B.2: Pathway Decision

**IF Generic of approved drug:**
→ Execute **ANDA Research Track** (Step 2B.3a)

**IF Modified approved product** (new dose/route/indication/formulation):
→ Execute **505(b)(2) Research Track** (Step 2B.3b)

**IF New Chemical Entity:**
→ Execute **NDA Research Track** (Step 2B.3c)

**IF Biologic:**
→ Execute **BLA Research Track** (Step 2B.3d)

##### Step 2B.3a: ANDA Research Track (Generic Drug)

Query **Orange Book** for Reference Listed Drug (RLD).

**Extract:**
- **NDA Number, Drug Name**
- **Active Ingredient(s):** Name, strength
- **Dosage Form & Route:** (e.g., tablet, oral)
- **Patent Information:** Numbers, expiration dates
- **Exclusivity Expiration:** Date when generic can be approved
- **TE Code:** Therapeutic equivalence rating

**Clinical Data Required:** Bioequivalence (BE) studies only
- Single-dose pharmacokinetic study
- Steady-state PK study (if applicable)
- No efficacy or safety trials needed (relies on RLD data)

##### Step 2B.3b: 505(b)(2) Research Track (Modified Product)

Query **Drugs@FDA** for similar approved products.

**Extract from similar approvals:**
- Approval history for condition/indication
- Changes from reference product that required new data
- Bridging study designs used in precedent 505(b)(2) applications
- Prior 505(b)(2) approvals for this type of modification

**Clinical Data Required:** Varies based on change
- May leverage RLD safety/efficacy data for some aspects
- Typically requires 1 pivotal trial + bridging studies
- Examples: BA/BE studies, dose-ranging, PK in new population

##### Step 2B.3c: NDA Research Track (New Chemical Entity)

Query **Drugs@FDA** and **ClinicalTrials.gov** for condition/MOA precedents.

**Extract from approved trials:**
- Phase 1/2/3 study designs for similar indications
- Safety database size requirements (typically 1500+ patients for chronic use)
- Number of pivotal trials required (typically 2 adequate & well-controlled Phase 3 trials)
- Common primary/secondary endpoints for indication
- Special population studies (pediatric, geriatric, renal/hepatic impairment)

##### Step 2B.3d: BLA Research Track (Biologics)

Query **Purple Book** and **CBER guidance** for biologic class.

**Extract from approved biologics:**
- Similar biologics in therapeutic class
- Immunogenicity assessment approaches used
- Manufacturing/CMC complexity considerations
- Biosimilar development pathways (if reference product exists)

**Clinical Data Required:** Similar to NDA
- Potency assays critical for biologics
- Immunogenicity monitoring throughout development
- Manufacturing consistency demonstration
- May require post-market safety studies (REMS)

##### Step 2B.4: IND Requirements (All Pathways)

**Key Difference from Devices:** IND required for ALL investigational drugs/biologics
- No "NSR exemption" equivalent (unlike device IDE NSR)
- Must submit IND before initiating Phase 1 clinical trials
- 30-day FDA review period before study start

**Assess Clinical Hold Risk Factors** per 21 CFR 312.42:

| Risk Factor | Evaluation Question | Hold Risk |
|-------------|---------------------|-----------|
| **Novel MOA?** | Limited precedent for mechanism? | High if yes |
| **Safety Signals?** | Preclinical toxicology concerns? | High if unresolved |
| **Tox Data?** | Adequate animal studies for proposed dose/duration? | High if inadequate |
| **CMC Concerns?** | Manufacturing, stability, or quality issues? | High if present |
| **High-Risk Population?** | Vulnerable, pediatric, or critically ill patients? | Moderate-High |
| **Study Design?** | Unsafe dose escalation or inadequate monitoring? | High if unsafe |

**Document:**
- IND submission strategy (Type A/B/C meeting needs)
- Clinical hold risk mitigation plan
- Relevant CFR citations (21 CFR 312 for IND)
- ICH guideline compliance (E6-GCP, E9-Statistics, E10-Control Group)

---

### Step 3: Search ClinicalTrials.gov for Similar Trials

**Reporting:** Inform the user when searching ClinicalTrials.gov and reviewing trial details.

Use ClinicalTrials.gov MCP Server:

| Tool | Parameters |
|------|------------|
| `search_clinical_trials` | condition, intervention, sponsor, location, status ("recruiting"/"active"/"completed"/"all"), phase ("1"/"2"/"3"/"4"), max_results (default 25, max 100) |
| `get_trial_details` | nct_id (e.g., "NCT04267848") → eligibility, outcomes, design, contacts |

**Extract:** Study design (RCT, single-arm, crossover), phase, sample size, primary/secondary endpoints, duration, inclusion/exclusion criteria, comparator, status/results.

---

### Step 4: Search for Published Protocols

**Reporting:** Inform the user when searching for published protocols.

**CONSTRAINT: Use ONLY ClinicalTrials.gov MCP Server** - Do not perform generic web searches.

**Primary Source:** ClinicalTrials.gov MCP Server (see Step 3 for MCP tool usage)
- Use `get_trial_details` to retrieve protocol documents for relevant NCT IDs
- Extract protocol PDFs when available through MCP interface

**Extract:** Protocol structure, endpoint definitions, inclusion/exclusion structure, statistical analysis plans, visit schedules, safety monitoring.

---

### Step 5: Analyze and Summarize Findings

Synthesize into actionable insights:

| Category | What to Summarize |
|----------|-------------------|
| **Study Design** | Most common design, comparators, blinding, phases |
| **Endpoints** | Primary/secondary endpoints, measurement methods, timing |
| **Sample Size** | Range by phase/study type, powering considerations |
| **Duration** | Treatment period, follow-up, total duration |
| **Population** | Common inclusion/exclusion, age ranges, disease severity |

---

### Step 6: Write Research Summary Waypoint

Create `waypoints/01_clinical_research_summary.json` with all findings.

**Data Retention:**
- **Keep:** Top 5-10 similar trials (structured summary), key FDA regulatory pathway info from Step 2, design/endpoint recommendations
- **Discard:** Full trial details beyond summary

---

### Step 7: Display Summary

1. Create an artifact displaying Step 7 summary format (see below)

Display concise summary to user:
- Steps taken and key findings
- Regulatory pathway determination (from Step 2)
- Clinical trial search results
- Next steps for protocol development

4. **STOP and ask the user:** "Would you like me to proceed with the research step?"
5. Only continue to Step 2 if the user confirms

---

## Output Files

| File | Size | Content |
|------|------|---------|
| `waypoints/01_clinical_research_summary.json` | ~10-15KB | Research findings |
| `waypoints/intervention_metadata.json` | Updated | With regulatory info |

---

## Quality Checks

### All Interventions
- [ ] At least 3-5 similar trials identified
- [ ] Study designs appropriate for intervention type
- [ ] Primary endpoint recommendations clear
- [ ] Sample size considerations provided
- [ ] FDA guidance relevant to intervention/indication
- [ ] Duration recommendations realistic
- [ ] Population criteria specific enough

### Devices Only
- [ ] Device classification (Class I/II/III)
- [ ] Product code found
- [ ] Regulatory pathway (510(k)/De Novo/PMA/Exempt)
- [ ] Predicates identified (3-5 for 510(k)) OR De Novo/PMA precedents
- [ ] Special Controls (if Class II)
- [ ] IDE risk determination (SR/NSR) with rationale
- [ ] Clinical data requirements understood

### Drugs/Biologics Only
- [ ] Classification (OTC/Rx, controlled schedule, NCE status)
- [ ] Regulatory pathway (NDA/ANDA/505(b)(2)/BLA)
- [ ] CFR references documented
- [ ] Reference drug identified (ANDA/505(b)(2): Orange Book; BLA: Purple Book)
- [ ] Clinical data requirements for pathway
- [ ] IND requirements and clinical hold risks
- [ ] ICH guideline requirements (E6, E9, E10)
- [ ] Special population needs (pediatric, geriatric)
- [ ] Manufacturing/CMC considerations (biologics)

---

## Notes for Claude

- **Be thorough** — protocol quality depends on good research
- **Always report status** — user should see database queries and document reviews in real-time
- **Devices:** Predicate devices are critical; classification determines pathway and requirements
- **Drugs/Biologics:** Pathway determines everything; IND required for ALL (no NSR exemption); Orange Book and Purple Book are essential
- **NCE status** affects exclusivity and data requirements
- **ICH guidelines** are mandatory for protocol design
