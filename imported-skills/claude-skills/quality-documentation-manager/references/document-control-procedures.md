# Document Control Procedures

Implementation guide for ISO 13485-compliant document control systems.

---

## Table of Contents

- [Document Numbering System](#document-numbering-system)
- [Document Lifecycle](#document-lifecycle)
- [Review and Approval Workflow](#review-and-approval-workflow)
- [Change Control Process](#change-control-process)
- [Distribution and Access Control](#distribution-and-access-control)
- [Record Retention](#record-retention)

---

## Document Numbering System

### Numbering Format

Standard format: `[PREFIX]-[CATEGORY]-[SEQUENCE]-[REVISION]`

| Component | Format | Example | Description |
|-----------|--------|---------|-------------|
| PREFIX | 2-3 letters | SOP, WI, TF | Document type identifier |
| CATEGORY | 2-3 digits | 01, 02, 10 | Functional area code |
| SEQUENCE | 3-4 digits | 001, 0001 | Sequential number within category |
| REVISION | Letter or number | A, 01 | Revision indicator |

### Document Type Prefixes

| Prefix | Document Type | Description |
|--------|---------------|-------------|
| QM | Quality Manual | Top-level QMS description |
| SOP | Standard Operating Procedure | Process procedures |
| WI | Work Instruction | Task-level instructions |
| TF | Template/Form | Controlled forms and templates |
| POL | Policy | Policy statements |
| SPEC | Specification | Product/process specifications |
| PLN | Plan | Project and quality plans |
| RPT | Report | Technical and quality reports |

### Category Codes

| Code | Functional Area | Examples |
|------|-----------------|----------|
| 01 | Quality Management | QMS procedures, audits |
| 02 | Document Control | This area |
| 03 | Human Resources | Training, competency |
| 04 | Design & Development | Design control |
| 05 | Purchasing | Supplier management |
| 06 | Production | Manufacturing |
| 07 | Quality Control | Inspection, testing |
| 08 | CAPA | Corrective/preventive actions |
| 09 | Risk Management | ISO 14971 processes |
| 10 | Regulatory Affairs | Submissions, compliance |

### Numbering Workflow

1. Author requests document number from Document Control
2. Document Control verifies category and assigns next sequence number
3. Document number recorded in Document Master List
4. Author creates document using assigned number
5. **Validation:** Number format matches standard; no duplicates exist

---

## Document Lifecycle

### Lifecycle Stages

```
DRAFT → REVIEW → APPROVED → EFFECTIVE → SUPERSEDED → OBSOLETE
  │        │         │          │            │           │
  │        │         │          │            │           └── Archived/Destroyed
  │        │         │          │            └── New revision effective
  │        │         │          └── Training complete, distribution done
  │        │         └── All approvals obtained
  │        └── Under review/revision
  └── Initial creation
```

### Stage Definitions

| Stage | Definition | Actions Required |
|-------|------------|------------------|
| Draft | Document under creation or revision | Author editing, not for use |
| Review | Circulated for review and comment | Reviewers provide feedback |
| Approved | All required signatures obtained | Ready for training/distribution |
| Effective | Training complete, document released | Available for use |
| Superseded | Replaced by newer revision | Remove from active use |
| Obsolete | No longer applicable | Archive per retention schedule |

### Document Status Indicators

| Status | Indicator | Location |
|--------|-----------|----------|
| Draft | "DRAFT" watermark | Header or footer |
| Approved | Approval signatures with dates | Signature page |
| Effective | Effective date | Header |
| Obsolete | "OBSOLETE" stamp | Across all pages |

---

## Review and Approval Workflow

### Document Review Workflow

1. Author completes document draft
2. Author submits for review via DMS or routing form
3. Reviewers assigned based on document type and content
4. Reviewers provide comments within review period (typically 5-10 business days)
5. Author addresses comments and documents responses
6. Author resubmits for approval
7. Approvers sign and date
8. **Validation:** All required reviewers completed; all comments addressed

### Required Reviewers by Document Type

| Document Type | Required Reviewers | Required Approvers |
|---------------|-------------------|-------------------|
| SOP | Process Owner, QA | QA Manager, Process Owner |
| WI | Area Supervisor, QA | Area Manager |
| SPEC | Engineering, QA | Engineering Manager, QA |
| TF | Process Owner | QA |
| POL | Department Heads | Management Representative |
| Design Documents | Design Team, QA | Design Control Authority |

### Approval Matrix

```
APPROVAL AUTHORITY MATRIX

Document Level 1 (Policy): CEO or delegate + QA Manager
Document Level 2 (SOP): Department Manager + QA Manager
Document Level 3 (WI/TF): Area Supervisor + QA Representative

Regulatory Submissions: RA Manager + QA Manager + Technical Expert
Design Documents: Design Authority + QA Manager
```

### Review Comment Template

```
REVIEW COMMENT LOG

Document: [Document Number and Title]
Reviewer: [Name, Role]
Review Date: [Date]

| Section | Line/Para | Comment | Disposition | Response |
|---------|-----------|---------|-------------|----------|
| [Ref] | [Location] | [Issue/suggestion] | Accept/Reject/Modify | [Explanation] |
```

---

## Change Control Process

### Change Request Workflow

1. Identify need for document change
2. Complete Change Request Form (CRF)
3. Submit CRF to Document Control
4. Document Control assigns change number
5. Route to reviewers for impact assessment
6. Obtain approvals based on change classification
7. Author implements approved changes
8. **Validation:** Changes match approved scope; version number incremented

### Change Classification

| Class | Definition | Approval Level | Examples |
|-------|------------|----------------|----------|
| Administrative | No impact on content meaning | Document Control | Typos, formatting, references |
| Minor | Limited content change, no process impact | Process Owner + QA | Clarifications, minor additions |
| Major | Significant content change, process impact | Full review cycle | New requirements, process changes |
| Emergency | Urgent change required for safety/compliance | Expedited approval + retrospective review | Safety issues, regulatory mandates |

### Change Impact Assessment

| Impact Area | Assessment Questions |
|-------------|---------------------|
| Training | Does change require retraining? Who? |
| Equipment | Does change affect equipment or systems? |
| Validation | Does change require revalidation? |
| Regulatory | Does change affect regulatory filings? |
| Other Documents | Which related documents need updating? |
| Records | What records are affected? |

### Version Control Rules

| Change Type | Version Increment | Example |
|-------------|-------------------|---------|
| Major revision | Increment revision number | Rev 01 → Rev 02 |
| Minor revision | Increment sub-revision | Rev 01 → Rev 01.1 |
| Administrative | No version change (or sub-increment) | Rev 01 → Rev 01a |
| Draft iterations | Use draft version | Draft 1, Draft 2 |

### Change History Template

```
DOCUMENT CHANGE HISTORY

| Revision | Date | Description of Change | Author | Approver |
|----------|------|----------------------|--------|----------|
| 01 | YYYY-MM-DD | Initial release | [Name] | [Name] |
| 02 | YYYY-MM-DD | [Change description] | [Name] | [Name] |
```

---

## Distribution and Access Control

### Distribution Methods

| Method | Use Case | Control Mechanism |
|--------|----------|-------------------|
| Electronic (DMS) | Primary method | Access permissions |
| Controlled Print | Manufacturing floor | Signature log |
| Uncontrolled Copy | External distribution | Watermark "UNCONTROLLED" |
| Reference Copy | Training/archive | Watermark "REFERENCE ONLY" |

### Access Permission Levels

| Level | Permissions | Typical Roles |
|-------|-------------|---------------|
| Read | View documents only | General users |
| Print | View and print controlled copies | Area supervisors |
| Review | View, print, add comments | Reviewers |
| Author | Create, edit drafts | Document authors |
| Approve | Approve documents | Approvers |
| Admin | Full system access | Document Control |

### Controlled Print Log

```
CONTROLLED PRINT LOG

Document: [Document Number]
Revision: [Revision Number]

| Copy # | Location | Issued To | Date Issued | Date Returned | Signature |
|--------|----------|-----------|-------------|---------------|-----------|
| 001 | Production Area 1 | [Name] | [Date] | [Date] | [Sig] |
| 002 | QC Lab | [Name] | [Date] | [Date] | [Sig] |
```

### Obsolete Document Control

1. Mark document as "OBSOLETE" in DMS
2. Notify copy holders of obsolescence
3. Collect and destroy controlled prints
4. Update Document Master List
5. Archive master copy per retention schedule
6. **Validation:** No obsolete copies remain in active use areas

---

## Record Retention

### Retention Periods

> **⚠️ STATUS — QMSR transition (effective 2026-02-02):** Under FDA's Quality Management System Regulation (QMSR, 89 FR 7496), 21 CFR Part 820 now **incorporates ISO 13485:2016 by reference** and the legacy QSR subsection numbers below (820.30/.181/.184/.198) **no longer exist in the CFR** — they are shown as a historical index. The current authority is **ISO 13485:2016 §4.2.5 (control of records)** plus retained **21 CFR 820.35** (records). The record-retention rule itself is in ISO 13485 §4.2.5 ("at least the lifetime of the medical device as defined by the organization, but not less than two years"). Cite the ISO 13485 clause in current documentation.

| Record Type | Retention Period | Basis (current authority — legacy QSR shown for index) |
|-------------|------------------|-------|
| Device Master Record (DMR) | Life of device + 2 years | ISO 13485 §4.2.3/§4.2.5 (legacy QSR 820.181, historical) |
| Device History Record (DHR) | Life of device + 2 years | ISO 13485 §4.2.5 (legacy QSR 820.184, historical) |
| Design History File (DHF) | Life of device + 2 years | ISO 13485 §7.3.10/§4.2.5 (legacy QSR 820.30, historical) |
| Quality Records | 2 years beyond device discontinuation | ISO 13485 §4.2.5 |
| Training Records | Duration of employment + 3 years | Best practice |
| Audit Records | 7 years | Best practice |
| Complaint Records | Life of device + 2 years | ISO 13485 §8.2.2/§4.2.5 + 21 CFR 820.35(b) (legacy QSR 820.198, historical) |
| CAPA Records | 7 years | Best practice |
| Calibration Records | 2 years beyond equipment disposal | Best practice |
| Supplier Records | Life of relationship + 3 years | Best practice |

### Archive Requirements

| Requirement | Specification |
|-------------|---------------|
| Storage Conditions | Temperature 15-25°C, RH 30-60% |
| Access Control | Restricted to authorized personnel |
| Indexing | Searchable by document number, date, type |
| Media | Original format or validated conversion |
| Backup | Offsite backup for electronic records |
| Integrity Checks | Periodic verification of record legibility |

### Disposal Procedure

1. Verify retention period has expired
2. Check for legal holds or ongoing litigation
3. Obtain disposal authorization
4. Execute secure destruction (shred paper, wipe electronic)
5. Document disposal in Disposal Log
6. **Validation:** No premature disposal; disposal documented

### Disposal Log Template

```
RECORD DISPOSAL LOG

| Document/Record ID | Description | Retention Expired | Disposal Date | Method | Witness |
|--------------------|-------------|-------------------|---------------|--------|---------|
| [ID] | [Description] | [Date] | [Date] | Shred/Wipe | [Name] |
```

---

## Document Master List

### Master List Content

| Field | Description | Required |
|-------|-------------|----------|
| Document Number | Unique identifier | Yes |
| Title | Document title | Yes |
| Current Revision | Active revision number | Yes |
| Effective Date | Date document became effective | Yes |
| Status | Draft/Effective/Obsolete | Yes |
| Process Owner | Responsible party | Yes |
| Review Date | Next scheduled review | Yes |
| Category | Functional area | Yes |
| Storage Location | Physical or electronic location | Yes |

### Master List Maintenance

- Update within 24 hours of document status change
- Review quarterly for accuracy
- Audit annually for completeness
- Archive historical versions

### Sample Master List Entry

```
| Doc # | Title | Rev | Eff Date | Status | Owner | Review Date |
|-------|-------|-----|----------|--------|-------|-------------|
| SOP-02-001 | Document Control | 03 | 2024-01-15 | Effective | QA Mgr | 2025-01-15 |
| WI-06-012 | Assembly Line Setup | 02 | 2024-03-01 | Effective | Prod Mgr | 2025-03-01 |
```
