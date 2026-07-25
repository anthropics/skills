---
name: "quality-documentation-manager"
description: Document control system management for medical device QMS. Covers document numbering, version control, change management, and 21 CFR Part 11 compliance. Use when working on document control procedures, change control workflows, document numbering, version management, electronic signature compliance, or regulatory documentation review.
triggers:
  - document control
  - document numbering
  - version control
  - change control
  - document approval
  - electronic signature
  - 21 CFR Part 11
  - audit trail
  - document lifecycle
  - controlled document
  - document master list
  - record retention
---

# Quality Documentation Manager

Document control system design and management for ISO 13485-compliant quality management systems, including numbering conventions, approval workflows, change control, and electronic record compliance.

---

## Table of Contents

- [Document Control Workflow](#document-control-workflow)
- [Document Numbering System](#document-numbering-system)
- [Approval and Review Process](#approval-and-review-process)
- [Change Control Process](#change-control-process)
- [21 CFR Part 11 Compliance](#21-cfr-part-11-compliance)
- [Reference Documentation](#reference-documentation)
- [Tools](#tools)

---

## Document Control Workflow

Implement document control from creation through obsolescence:

1. Assign document number per numbering procedure
2. Create document using controlled template
3. Route for review to required reviewers
4. Address review comments and document responses
5. Obtain required approval signatures
6. Assign effective date and distribute
7. Update Document Master List
8. **Validation:** Document accessible at point of use; obsolete versions removed

### Document Lifecycle Stages

| Stage | Definition | Actions Required |
|-------|------------|------------------|
| Draft | Under creation or revision | Author editing, not for use |
| Review | Circulated for review | Reviewers provide feedback |
| Approved | All signatures obtained | Ready for training/distribution |
| Effective | Training complete, released | Available for use |
| Superseded | Replaced by newer revision | Remove from active use |
| Obsolete | No longer applicable | Archive per retention schedule |

### Document Types and Prefixes

| Prefix | Document Type | Typical Content |
|--------|---------------|-----------------|
| QM | Quality Manual | QMS overview, scope, policy |
| SOP | Standard Operating Procedure | Process-level procedures |
| WI | Work Instruction | Task-level step-by-step |
| TF | Template/Form | Controlled forms |
| SPEC | Specification | Product/process specs |
| PLN | Plan | Quality/project plans |

### Required Reviewers by Document Type

| Document Type | Required Reviewers | Required Approvers |
|---------------|-------------------|-------------------|
| SOP | Process Owner, QA | QA Manager, Process Owner |
| WI | Area Supervisor, QA | Area Manager |
| SPEC | Engineering, QA | Engineering Manager, QA |
| TF | Process Owner | QA |
| Design Documents | Design Team, QA | Design Control Authority |

---

## Document Numbering System

Assign consistent document numbers for identification and retrieval.

### Numbering Format

Standard format: `PREFIX-CATEGORY-SEQUENCE[-REVISION]`

```
Example: SOP-02-001-A

SOP = Document type (Standard Operating Procedure)
02  = Category code (Document Control)
001 = Sequential number
A   = Revision indicator
```

### Category Codes

| Code | Functional Area | Description |
|------|-----------------|-------------|
| 01 | Quality Management | QMS procedures, management review |
| 02 | Document Control | This area |
| 03 | Human Resources | Training, competency |
| 04 | Design & Development | Design control processes |
| 05 | Purchasing | Supplier management |
| 06 | Production | Manufacturing procedures |
| 07 | Quality Control | Inspection, testing |
| 08 | CAPA | Corrective/preventive actions |
| 09 | Risk Management | ISO 14971 processes |
| 10 | Regulatory Affairs | Submissions, compliance |

### Numbering Workflow

1. Author requests document number from Document Control
2. Document Control verifies category assignment
3. Document Control assigns next available sequence number
4. Number recorded in Document Master List
5. Author creates document using assigned number
6. **Validation:** Number format matches standard; no duplicates in Master List

### Revision Designation

| Change Type | Revision Increment | Example |
|-------------|-------------------|---------|
| Major revision | Increment number | Rev 01 → Rev 02 |
| Minor revision | Increment sub-revision | Rev 01 → Rev 01.1 |
| Administrative | No change or letter suffix | Rev 01 → Rev 01a |

See `references/document-control-procedures.md` for complete numbering guidance.

---

## Approval and Review Process

Obtain required reviews and approvals before document release.

### Review Workflow

1. Author completes document draft
2. Author submits for review via routing form or DMS
3. Reviewers assigned based on document type
4. Reviewers provide comments within review period (5-10 business days)
5. Author addresses comments and documents responses
6. Author resubmits revised document
7. Approvers sign and date
8. **Validation:** All required reviewers completed; all comments addressed with documented disposition

### Comment Disposition

| Disposition | Action Required |
|-------------|-----------------|
| Accept | Incorporate comment as written |
| Accept with modification | Incorporate with changes, document rationale |
| Reject | Do not incorporate, document justification |
| Defer | Address in future revision, document reason |

### Approval Matrix

```
Document Level 1 (Policy/QM): CEO or delegate + QA Manager
Document Level 2 (SOP): Department Manager + QA Manager
Document Level 3 (WI/TF): Area Supervisor + QA Representative
```

### Signature Requirements

| Element | Requirement |
|---------|-------------|
| Name | Printed name of signer |
| Signature | Handwritten or electronic signature |
| Date | Date signature applied |
| Role | Function/role of signer |

---

## Change Control Process

Manage document changes systematically through review and approval.

### Change Control Workflow

1. Identify need for document change
2. Complete Change Request Form with justification
3. Document Control assigns change number and logs request
4. Route to reviewers for impact assessment
5. Obtain approvals based on change classification
6. Author implements approved changes
7. Update revision number and change history
8. **Validation:** Changes match approved scope; change history complete

### Change Classification

| Class | Definition | Approval Level | Examples |
|-------|------------|----------------|----------|
| Administrative | No content impact | Document Control | Typos, formatting |
| Minor | Limited content change | Process Owner + QA | Clarifications |
| Major | Significant content change | Full review cycle | New requirements |
| Emergency | Urgent safety/compliance | Expedited + retrospective | Safety issues |

### Impact Assessment Checklist

| Impact Area | Assessment Questions |
|-------------|---------------------|
| Training | Does change require retraining? |
| Equipment | Does change affect equipment or systems? |
| Validation | Does change require revalidation? |
| Regulatory | Does change affect regulatory filings? |
| Other Documents | Which related documents need updating? |
| Records | What records are affected? |

### Change History Documentation

Each document must include change history:

```
| Revision | Date | Description | Author | Approver |
|----------|------|-------------|--------|----------|
| 01 | 2023-01-15 | Initial release | J. Smith | M. Jones |
| 02 | 2024-03-01 | Updated workflow | J. Smith | M. Jones |
```

---

## 21 CFR Part 11 Compliance

Implement electronic record and signature controls for FDA compliance.

### Part 11 Scope

| Applies To | Does Not Apply To |
|------------|-------------------|
| Records required by FDA regulations | Paper records |
| Records submitted to FDA | Internal non-regulated documents |
| Electronic signatures on required records | General email communication |

### Electronic Record Controls

1. Validate system for accuracy and reliability
2. Implement secure audit trail for all changes
3. Restrict system access to authorized individuals
4. Generate accurate copies in human-readable format
5. Protect records throughout retention period
6. **Validation:** Audit trail captures who, what, when for all changes

### Audit Trail Requirements

| Requirement | Implementation |
|-------------|----------------|
| Secure | Cannot be modified by users |
| Computer-generated | System creates automatically |
| Time-stamped | Date and time of each action |
| Original values | Previous values retained |
| User identity | Who made each change |

### Electronic Signature Requirements

| Requirement | Implementation |
|-------------|----------------|
| Unique to individual | Not shared between persons |
| At least 2 components | User ID + password minimum |
| Signature manifestation | Name, date/time, meaning displayed |
| Linked to record | Cannot be excised or copied |

### Signature Manifestation

Every electronic signature must display:

| Element | Example |
|---------|---------|
| Printed name | John Smith |
| Date and time | 2024-03-15 14:32:05 EST |
| Meaning | Approved for Release |

### System Controls Checklist

**Access Controls:**
- [ ] Unique user ID for each person
- [ ] Password complexity enforced
- [ ] Account lockout after failed attempts
- [ ] Session timeout after inactivity

**Audit Trail:**
- [ ] All record creation logged
- [ ] All modifications logged with old/new values
- [ ] User identity captured
- [ ] Date/time stamp on all entries

**Security:**
- [ ] Role-based access control
- [ ] Encryption for data at rest and in transit
- [ ] Regular backup and tested recovery

See `references/21cfr11-compliance-guide.md` for detailed compliance requirements.

---

## Reference Documentation

### Document Control Procedures

`references/document-control-procedures.md` contains:

- Document numbering system and format
- Document lifecycle stages and transitions
- Review and approval workflow details
- Change control process with classification criteria
- Distribution and access control methods
- Record retention periods and disposal procedures
- Document Master List requirements

### 21 CFR Part 11 Compliance Guide

`references/21cfr11-compliance-guide.md` contains:

- Part 11 scope and applicability
- Electronic record requirements (§11.10)
- Electronic signature requirements (§11.50, 11.100, 11.200)
- System control specifications
- Validation approach and documentation
- Compliance checklist and gap assessment template
- Common FDA deficiencies and prevention

---

## Tools

### Document Validator

```bash
# Validate document metadata
python scripts/document_validator.py --doc document.json

# Interactive validation mode
python scripts/document_validator.py --interactive

# JSON output for integration
python scripts/document_validator.py --doc document.json --output json

# Generate sample document JSON
python scripts/document_validator.py --sample > sample_doc.json
```

Validates:
- Document numbering convention compliance
- Title and status requirements
- Date validation (effective, review due)
- Approval requirements by document type
- Change history completeness
- 21 CFR Part 11 controls (audit trail, signatures)

### Sample Document Input

```json
{
  "number": "SOP-02-001",
  "title": "Document Control Procedure",
  "doc_type": "SOP",
  "revision": "03",
  "status": "Effective",
  "effective_date": "2024-01-15",
  "review_date": "2025-01-15",
  "author": "J. Smith",
  "approver": "M. Jones",
  "change_history": [
    {"revision": "01", "date": "2022-01-01", "description": "Initial release"},
    {"revision": "02", "date": "2023-01-15", "description": "Updated workflow"},
    {"revision": "03", "date": "2024-01-15", "description": "Added e-signature requirements"}
  ],
  "has_audit_trail": true,
  "has_electronic_signature": true,
  "signature_components": 2
}
```

---

## Document Control Metrics

Track document control system performance.

### Key Performance Indicators

| Metric | Target | Calculation |
|--------|--------|-------------|
| Document cycle time | <30 days | Average days from draft to effective |
| Review completion rate | >95% | Reviews completed on time / Total reviews |
| Change request backlog | <10 | Open change requests at month end |
| Overdue review rate | <5% | Documents past review date / Total effective |
| Audit finding rate | <2 per audit | Document control findings per internal audit |

### Periodic Review Schedule

| Document Type | Review Frequency |
|---------------|------------------|
| Policy | Every 3 years |
| SOP | Every 2 years |
| WI | Every 2 years |
| Specifications | As needed or with product changes |
| Forms/Templates | Every 3 years |

---

## Regulatory Requirements

### ISO 13485:2016 Clause 4.2

| Sub-clause | Requirement |
|------------|-------------|
| 4.2.1 | Quality management system documentation |
| 4.2.2 | Quality manual |
| 4.2.3 | Medical device file (technical documentation) |
| 4.2.4 | Control of documents |
| 4.2.5 | Control of records |

### FDA document & record control — ISO 13485 §4.2 under the QMSR (legacy QSR sections, historical)

> **⚠️ STATUS — QMSR transition (effective 2026-02-02):** FDA's Quality Management System Regulation (QMSR) final rule (89 FR 7496) amended 21 CFR Part 820 to **incorporate ISO 13485:2016 by reference** and removed the legacy QSR subsection structure. The section numbers in the table below (820.40/.180/.181/.184/.186) **no longer exist in the CFR**; they are retained only as a familiar index. Current document/record control authority is **ISO 13485:2016 §4.2** (esp. §4.2.4 control of documents, §4.2.5 control of records), with the medical device file in §4.2.3 and records additions in retained **21 CFR 820.35**. Cite the ISO 13485 clauses — not the 820.x numbers — in current compliance documentation.

| Legacy QSR Section (historical, pre-2026) | Requirement | Current authority under QMSR (legacy QSR shown for index) |
|-------------------------------------------|-------------|------------------------------|
| 820.40 | Document controls | ISO 13485 §4.2.4 |
| 820.180 | General record requirements | ISO 13485 §4.2.5 + 21 CFR 820.35 (retained) |
| 820.181 | Device master record | ISO 13485 §4.2.3 (medical device file) |
| 820.184 | Device history record | ISO 13485 §4.2.5 + 21 CFR 820.35 (retained) |
| 820.186 | Quality system record | ISO 13485 §4.2.5 + 21 CFR 820.35 (retained) |

### Common Audit Findings

| Finding | Prevention |
|---------|------------|
| Obsolete documents in use | Implement distribution control |
| Missing approval signatures | Enforce workflow before release |
| Incomplete change history | Require history update with each revision |
| No periodic review schedule | Establish and enforce review calendar |
| Inadequate audit trail | Validate DMS for Part 11 compliance |

> **Decision discipline:** The validator scripts in this skill check structure and completeness — they do not certify a document or record as compliant. Approval and release decisions are yours and the document owner's to make under your controlled procedure; route regulatory-classification or submission-record questions to Regulatory Affairs.
