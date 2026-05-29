# FRAP 28 Opening Brief Template - Ninth Circuit

This document defines the structure and markers for a Ninth Circuit Opening Brief.
The assembler script replaces markers with exact text from `sections.json`.

---

## Document Structure

```
{{COVER_PAGE}}

{{DISCLOSURE_STATEMENT}}

i
─────────────────────────────────────────────────────────────

{{TABLE_OF_CONTENTS}}

iv
─────────────────────────────────────────────────────────────

{{TABLE_OF_AUTHORITIES}}

1
─────────────────────────────────────────────────────────────

INTRODUCTION

{{INTRODUCTION}}

─────────────────────────────────────────────────────────────

JURISDICTIONAL STATEMENT

{{JURISDICTIONAL_STATEMENT}}

─────────────────────────────────────────────────────────────

STATUTORY [AND REGULATORY] AUTHORITIES

{{STATUTORY_AUTHORITIES}}

─────────────────────────────────────────────────────────────

ISSUE(S) PRESENTED

{{ISSUES_PRESENTED}}

─────────────────────────────────────────────────────────────

STATEMENT OF THE CASE

{{STATEMENT_OF_CASE}}

─────────────────────────────────────────────────────────────

SUMMARY OF THE ARGUMENT

{{SUMMARY_OF_ARGUMENT}}

─────────────────────────────────────────────────────────────

STANDARD OF REVIEW

{{STANDARD_OF_REVIEW}}

─────────────────────────────────────────────────────────────

ARGUMENT

{{ARGUMENT}}

─────────────────────────────────────────────────────────────

CONCLUSION

{{CONCLUSION}}

─────────────────────────────────────────────────────────────

STATEMENT OF RELATED CASES

{{RELATED_CASES}}

─────────────────────────────────────────────────────────────

CERTIFICATE OF COMPLIANCE

{{CERTIFICATE_COMPLIANCE}}

─────────────────────────────────────────────────────────────

CERTIFICATE OF SERVICE

{{CERTIFICATE_SERVICE}}

─────────────────────────────────────────────────────────────

ADDENDUM

{{ADDENDUM}}
```

---

## Section Requirements (FRAP 28)

### Cover Page
- Case number (Ninth Circuit)
- Caption (parties)
- District court info
- Document title
- Counsel info

### Disclosure Statement (FRAP 26.1)
- Required for corporate parties
- Pro se individuals: Not required

### Table of Contents
- Auto-generated from headings
- Page numbers required

### Table of Authorities
- Cases: alphabetical by name, with pages cited
- Statutes: numerical by U.S.C. title/section
- Rules: FRAP, FRCP, local rules
- Other: treatises, articles

### Introduction (Optional)
- Max 2 pages
- Summarize case and why you should win

### Jurisdictional Statement (Required)
1. District court jurisdiction (28 U.S.C. § 1331, etc.)
2. Appellate jurisdiction (28 U.S.C. § 1291)
3. Date of judgment appealed
4. Date of notice of appeal
5. Timeliness statute/rule
6. Final judgment or other basis

### Issues Presented (Required)
- One sentence per issue
- Numbered
- Should match Argument headings

### Statement of the Case (Required)
- Facts relevant to issues
- Procedural history
- Rulings being appealed
- Citations to ER for every assertion

### Summary of Argument (Required)
- Succinct statement of arguments
- Follow same structure as Argument
- Not mere repetition of headings

### Standard of Review (Required)
- State standard for each issue
- Cite authority
- Types: de novo, abuse of discretion, clear error

### Argument (Required)
- Begin with strongest argument
- Roman numerals for main issues
- Include contentions, reasons, citations
- Address opponent's arguments

### Conclusion (Required)
- One sentence
- State precise relief sought

### Statement of Related Cases (Form 17)
- Cases in Ninth Circuit from same district case
- Cases raising same/related issues
- Cases involving same transaction

### Certificate of Compliance (Form 8)
- Word count
- Typeface compliance

### Certificate of Service
- How and when served
- On whom

### Addendum
- Constitutional provisions
- Statutes
- Regulations
- Rules cited

---

## Word Limits (9th Cir. R. 32-1)

| Brief Type   | Limit  |
| ------------ | ------ |
| Opening      | 14,000 |
| Answering    | 14,000 |
| Reply        | 7,000  |
| Cross-Appeal | 16,500 |

---

## Formatting Requirements

- **Font**: 14-point proportional serif (Times New Roman, Georgia) or 10.5 cpi monospace
- **Spacing**: Double-spaced text; single-spaced for quotes >2 lines, headings, footnotes
- **Margins**: 1 inch minimum all sides
- **Page numbers**: May be in margins

---

## Marker Reference

| Marker                         | Source                            | Type           |
| ------------------------------ | --------------------------------- | -------------- |
| `{{COVER_PAGE}}`               | case_info                         | Auto-generated |
| `{{DISCLOSURE_STATEMENT}}`     | sections.disclosure_statement     | User text      |
| `{{TABLE_OF_CONTENTS}}`        | headings                          | Auto-generated |
| `{{TABLE_OF_AUTHORITIES}}`     | authorities.json                  | Auto-generated |
| `{{INTRODUCTION}}`             | sections.introduction             | User text      |
| `{{JURISDICTIONAL_STATEMENT}}` | sections.jurisdictional_statement | User text      |
| `{{STATUTORY_AUTHORITIES}}`    | sections.statutory_authorities    | User text      |
| `{{ISSUES_PRESENTED}}`         | sections.issues_presented         | User text      |
| `{{STATEMENT_OF_CASE}}`        | sections.statement_of_case        | User text      |
| `{{SUMMARY_OF_ARGUMENT}}`      | sections.summary_of_argument      | User text      |
| `{{STANDARD_OF_REVIEW}}`       | sections.standard_of_review       | User text      |
| `{{ARGUMENT}}`                 | sections.argument                 | User text      |
| `{{CONCLUSION}}`               | sections.conclusion               | User text      |
| `{{RELATED_CASES}}`            | sections.related_cases            | User text      |
| `{{CERTIFICATE_COMPLIANCE}}`   | word_count                        | Auto-generated |
| `{{CERTIFICATE_SERVICE}}`      | case_info                         | Auto-generated |
| `{{ADDENDUM}}`                 | sections.addendum                 | User text      |
