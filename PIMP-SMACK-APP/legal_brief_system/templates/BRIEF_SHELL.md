# NINTH CIRCUIT BRIEF SHELL - SECTION MARKERS

This document defines the exact sections required for a Ninth Circuit brief.
Scripts use these markers to copy exact text from source files.

## SECTION ORDER (FRAP 28)

| #   | Section                    | Marker                         | Source File                         | Required  |
| --- | -------------------------- | ------------------------------ | ----------------------------------- | --------- |
| 1   | Cover Page                 | (separate file)                | COVER_GENERATOR                     | Yes       |
| 2   | Disclosure Statement       | `{{DISCLOSURE_STATEMENT}}`     | case_info.json                      | Yes*      |
| 3   | Table of Contents          | `{{TABLE_OF_CONTENTS}}`        | Auto-generated                      | Yes       |
| 4   | Table of Authorities       | `{{TABLE_OF_AUTHORITIES}}`     | authorities.json                    | Yes       |
| 5   | Introduction               | `{{INTRODUCTION}}`             | arguments.json                      | Optional  |
| 6   | Jurisdictional Statement   | `{{JURISDICTIONAL_STATEMENT}}` | case_info.json                      | Yes       |
| 7   | Statutory Authorities      | `{{STATUTORY_AUTHORITIES}}`    | authorities.json                    | Optional  |
| 8   | Issues Presented           | `{{ISSUES_PRESENTED}}`         | issues_presented.json               | Yes       |
| 9   | Statement of the Case      | `{{STATEMENT_OF_CASE}}`        | evidence_pool.json                  | Yes       |
| 10  | Summary of Argument        | `{{SUMMARY_OF_ARGUMENT}}`      | arguments.json                      | Yes       |
| 11  | Standard of Review         | `{{STANDARD_OF_REVIEW}}`       | arguments.json                      | Yes       |
| 12  | Argument I                 | `{{ARGUMENT_I}}`               | arguments.json + evidence_pool.json | Yes       |
| 13  | Argument II                | `{{ARGUMENT_II}}`              | arguments.json + evidence_pool.json | If needed |
| 14  | Argument III               | `{{ARGUMENT_III}}`             | arguments.json + evidence_pool.json | If needed |
| 15  | Conclusion                 | `{{CONCLUSION}}`               | case_info.json                      | Yes       |
| 16  | Statement of Related Cases | `{{RELATED_CASES}}`            | case_info.json                      | Yes       |
| 17  | Certificate of Compliance  | `{{CERT_COMPLIANCE}}`          | Auto-generated                      | Yes       |
| 18  | Certificate of Service     | `{{CERT_SERVICE}}`             | case_info.json                      | Yes       |
| 19  | Addendum                   | `{{ADDENDUM}}`                 | authorities.json                    | If needed |

*Pro se individuals exempt from Disclosure Statement

---

## MARKER DETAILS

### {{DISCLOSURE_STATEMENT}}
- Pro se: "Appellant is a natural person proceeding pro se and is not required to file a disclosure statement pursuant to FRAP 26.1."
- Corporate: Identify parent corp and 10%+ stockholders

### {{JURISDICTIONAL_STATEMENT}}
Must include:
1. District court jurisdiction basis + statute (e.g., 28 U.S.C. § 1331)
2. Appellate jurisdiction basis + statute (e.g., 28 U.S.C. § 1291)
3. Date of judgment/order appealed
4. Date of notice of appeal
5. Timeliness statute/rule
6. Final judgment status

### {{ISSUES_PRESENTED}}
- Each issue = one sentence
- Start with "Whether"
- Phrase to suggest answer
- Number each issue
- Map to Argument sections (Issue I → Argument I)

### {{STATEMENT_OF_CASE}}
- Facts relevant to issues
- Procedural history
- Rulings presented for review
- **EVERY FACT MUST CITE TO ER** (9th Cir. R. 28-2.8)
- Format: `ER-123` or `1-ER-234` (multi-volume)

### {{SUMMARY_OF_ARGUMENT}}
- Succinct, clear, accurate
- NOT just repeat headings
- Follow same organization as Argument
- Can use Roman numerals to map to sections

### {{STANDARD_OF_REVIEW}}
- State standard for EACH issue
- Cite statute or 9th Cir. decision
- If challenging ruling: state where objection preserved in record

### {{ARGUMENT_I}}, {{ARGUMENT_II}}, etc.
- Contentions with reasons
- Citations to authorities
- Citations to record (ER)
- Address weaknesses head-on
- Start with strongest argument

### {{CONCLUSION}}
- One sentence
- Precise relief sought
- Example: "For the foregoing reasons, the judgment of the district court should be reversed, and the case remanded for trial."

### {{CERT_COMPLIANCE}}
Auto-generated:
- Word count
- Type size confirmation
- Typeface confirmation

### {{CERT_SERVICE}}
- Date of service
- Method of service
- Names of persons served

---

## FORMATTING REQUIREMENTS

- **Font**: 14pt proportional serif (Times New Roman, Georgia, Century Schoolbook)
- **Spacing**: Double-spaced body; single-spaced for block quotes, headings, footnotes
- **Margins**: 1 inch all sides
- **Page numbers**: May be in margins
- **Footnotes**: Same size as body (14pt)
- **Word limit**: 14,000 (opening/answering), 7,000 (reply)

## ER CITATION FORMAT

| Type          | Format           | Example  |
| ------------- | ---------------- | -------- |
| Single volume | ER-[page]        | ER-123   |
| Multi-volume  | [vol]-ER-[page]  | 1-ER-234 |
| Supplemental  | [vol]-SER-[page] | 1-SER-56 |
| Further       | [vol]-FER-[page] | 1-FER-78 |
