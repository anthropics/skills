# Ninth Circuit Opening Brief Skill

## Purpose
Assemble FRAP 28-compliant Opening Briefs for the Ninth Circuit Court of Appeals.

**CRITICAL RULE: This skill COPIES text - it does NOT generate, rewrite, or modify content.**

## When To Use
- User needs to assemble an Opening Brief from their written sections
- User wants to format an existing brief for Ninth Circuit requirements
- User needs Table of Contents / Table of Authorities generated from their text

## Architecture

```
┌─────────────────┐     ┌──────────────────┐     ┌─────────────────┐
│  brief_data/    │────▶│  assemble_       │────▶│  OUTBOX/briefs/ │
│  (JSON sections)│     │  opening_brief.py│     │  (formatted doc)│
└─────────────────┘     └──────────────────┘     └─────────────────┘
        │                        │
        │                        ▼
        │               ┌──────────────────┐
        └──────────────▶│  FRAP28_TEMPLATE │
                        │  (markers)       │
                        └──────────────────┘
```

## Required Files

### 1. Brief Data (JSON) - User's Exact Text
Location: `brief_data/sections.json`

```json
{
  "case_info": {
    "ninth_circuit_no": "25-XXXXX",
    "district_court": "District of Oregon",
    "district_case_no": "3:24-cv-00839-SB",
    "judge": "Hon. Stacy Beckerman",
    "appellant": "Tyler Allen Lofall",
    "appellee": "Clackamas County, et al."
  },
  "sections": {
    "disclosure_statement": { "id": "DISC_001", "text": "..." },
    "introduction": { "id": "INTRO_001", "text": "..." },
    "jurisdictional_statement": { "id": "JURIS_001", "text": "..." },
    "issues_presented": { "id": "ISSUES_001", "text": "..." },
    "statement_of_case": { "id": "SOC_001", "text": "..." },
    "summary_of_argument": { "id": "SUMM_001", "text": "..." },
    "standard_of_review": { "id": "SOR_001", "text": "..." },
    "argument": { "id": "ARG_001", "text": "..." },
    "conclusion": { "id": "CONC_001", "text": "..." },
    "related_cases": { "id": "REL_001", "text": "..." },
    "addendum": { "id": "ADD_001", "text": "..." }
  }
}
```

### 2. Authorities (JSON) - Auto-extracted or Manual
Location: `brief_data/authorities.json`

```json
{
  "cases": [
    {
      "name": "Hazel-Atlas Glass Co. v. Hartford-Empire Co.",
      "citation": "322 U.S. 238 (1944)",
      "pages_cited": [4, 15, 22]
    }
  ],
  "statutes": [
    {
      "citation": "42 U.S.C. § 1983",
      "pages_cited": [1, 6, 18]
    }
  ],
  "rules": [
    {
      "citation": "Fed. R. App. P. 4(a)(4)(A)(iv)",
      "pages_cited": [3, 5]
    }
  ]
}
```

## Commands

### Assemble Full Brief
```bash
python assemble_opening_brief.py --all --case-no 25-XXXXX
```

### Assemble Single Section
```bash
python assemble_opening_brief.py --section introduction
python assemble_opening_brief.py --section statement_of_case
```

### Generate Table of Authorities
```bash
python assemble_opening_brief.py --toa
```

### Generate Table of Contents
```bash
python assemble_opening_brief.py --toc
```

### Validate Brief
```bash
python assemble_opening_brief.py --validate
```

### Word Count
```bash
python assemble_opening_brief.py --word-count
```

## Output
- Primary: `OUTBOX/briefs/{case_no}-opening-brief-{datetime}.docx`
- Chronological: `OUTBOX/chronological/{datetime}-{case_no}-opening-brief.docx` (read-only)

## FRAP 28 Section Order

| Order | Section                   | Marker                       | Required                 |
| ----- | ------------------------- | ---------------------------- | ------------------------ |
| 1     | Cover Page                | {{COVER_PAGE}}               | Yes                      |
| 2     | Disclosure Statement      | {{DISCLOSURE_STATEMENT}}     | If applicable            |
| 3     | Table of Contents         | {{TABLE_OF_CONTENTS}}        | Yes                      |
| 4     | Table of Authorities      | {{TABLE_OF_AUTHORITIES}}     | Yes                      |
| 5     | Introduction              | {{INTRODUCTION}}             | Optional but recommended |
| 6     | Jurisdictional Statement  | {{JURISDICTIONAL_STATEMENT}} | Yes                      |
| 7     | Statement of Issues       | {{ISSUES_PRESENTED}}         | Yes                      |
| 8     | Statement of the Case     | {{STATEMENT_OF_CASE}}        | Yes                      |
| 9     | Summary of Argument       | {{SUMMARY_OF_ARGUMENT}}      | Yes                      |
| 10    | Standard of Review        | {{STANDARD_OF_REVIEW}}       | Yes                      |
| 11    | Argument                  | {{ARGUMENT}}                 | Yes                      |
| 12    | Conclusion                | {{CONCLUSION}}               | Yes                      |
| 13    | Related Cases             | {{RELATED_CASES}}            | Yes (Form 17)            |
| 14    | Certificate of Compliance | {{CERTIFICATE_COMPLIANCE}}   | Yes (Form 8)             |
| 15    | Certificate of Service    | {{CERTIFICATE_SERVICE}}      | Yes                      |
| 16    | Addendum                  | {{ADDENDUM}}                 | If statutes cited        |

## Word Limits (Ninth Circuit Rule 32-1)

| Brief Type         | Word Limit   |
| ------------------ | ------------ |
| Opening Brief      | 14,000 words |
| Answering Brief    | 14,000 words |
| Reply Brief        | 7,000 words  |
| Cross-Appeal Brief | 16,500 words |

## Workflow for Claude

1. **User provides section text** → Store in `sections.json`
2. **Never rewrite user text** → Copy byte-for-byte
3. **Extract citations** → Build `authorities.json`
4. **Run assembler** → Output formatted brief
5. **Validate** → Check word count, required sections

## Example Usage

```
User: "Here's my introduction: [paste text]"
Claude: 
1. Store text in sections.json under "introduction"
2. Run: python assemble_opening_brief.py --section introduction
3. Report: "Introduction saved. Section ID: INTRO_001"
```

## DO NOT

- Generate any substantive text
- Reword or "improve" user's writing
- Add content not provided by user
- Modify citations
- Change case names or numbers

## Source Files Reference

- `assemble_opening_brief.py` - Main assembler
- `extract_authorities.py` - Pull citations from text
- `templates/FRAP28_OPENING_BRIEF.md` - Template with markers
- `brief_data/sections.json` - User's section text
- `brief_data/authorities.json` - Citation database
