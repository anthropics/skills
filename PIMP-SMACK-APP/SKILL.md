---
name: pimp-formatting-skills
description: Legal Document Formatter for Pro Se Litigants. Uses taxonomy files to format ANY legal document with correct structure and jurisdiction-specific styling. READ PimpJuice_instructions/MODEL_INSTRUCTIONS.md FIRST.
license: Apache-2.0
allowed-tools: []
metadata:
  version: 2.0.0
  author: Tyler A. Lofall
  suite: pimp-formatting-skills
---

# Pimp Formatting Skills — Legal Document Formatter

## .\[READ FIRST]

**YOU MUST READ THESE FILES IN ORDER:**

1. `PimpJuice_instructions/MODEL_INSTRUCTIONS.md` — **HOW TO USE THE TAXONOMY FILES**
2. `PimpJuice_instructions/taxonomy/build_manifest.json` — 14 filing types with build_order + heading_order
3. `PimpJuice_instructions/taxonomy/heading1_definitions.json` — Section definitions + LEGAL REASONS
4. `PimpJuice_instructions/jurisdictions/courts.json` — Formatting rules per court

---

## WHAT THIS SKILL DOES

This is a **FORMATTER** — not a drafter.

| Does | Does NOT |
|------|----------|
| Define document structure (what sections, what order) | Write legal content |
| Apply jurisdiction formatting (font, size, margins) | Provide legal advice |
| Validate required sections | Draft boilerplate |
| Generate XML/DOCX structure | Decide case strategy |

---

## HOW TO USE

### Step 1: User tells you what they need
- "Format my motion for summary judgment"
- "Format my Ninth Circuit appellate brief"
- "Format my complaint"

### Step 2: Look up filing type
Open `PimpJuice_instructions/taxonomy/filing_types.json` and find the matching type.

### Step 3: Get construct_order
This is the PHYSICAL BUILD SEQUENCE (what pieces in what order).

### Step 4: Get heading1_groups
These are the SECTIONS that go in the Body.

### Step 5: Look up each heading
Open `PimpJuice_instructions/taxonomy/heading1_definitions.json` for display names and legal reasons.

### Step 6: Get jurisdiction formatting
Open `PimpJuice_instructions/jurisdictions/courts.json` for font, size, margins, word limits.

### Step 7: Build the document
Generate each piece in construct_order with correct formatting.

---

## FILE STRUCTURE

```
Pimp_Formatting_skills/
├── SKILL.md                              # THIS FILE
├── LICENSE                               # Apache 2.0
└── PimpJuice_instructions/               # ALL INSTRUCTIONS HERE
```

---

## QUICK REFERENCE

### Filing Types (14)
`MOTION`, `BRIEF`, `APPELLATE_BRIEF`, `COMPLAINT`, `ANSWER`, `DECLARATION`, `NOTICE`, `ORDER`, `STIPULATION`, `DISCOVERY`, `EXHIBIT`, `JUDGMENT`, `LETTER`, `SUBPOENA`

### Common Heading1 Groups
- **Motion/Brief:** INTRODUCTION, BACKGROUND, LEGAL_STANDARD, ARGUMENT, CONCLUSION
- **Appellate Brief:** JURISDICTIONAL_STATEMENT, ISSUES, CASE_STATEMENT, FACTS, SUMMARY, STANDARD_OF_REVIEW, ARGUMENT, CONCLUSION
- **Complaint:** PARTIES, JURISDICTION_VENUE, FACTS, CLAIMS, PRAYER

### XML Styles
- `<LEGAL_H1>` — Major section heading
- `<LEGAL_H2>` — Subsection (Roman numerals)
- `<LEGAL_H3>` — Sub-subsection (Letters)
- `<LEGAL_BODY>` — Body text

---

## JURISDICTION QUICK LOOKUP

| Court | Font | Size | Word Limit (Brief) |
|-------|------|------|-------------------|
| 9th Circuit | Century Schoolbook | 14pt | 14,000 |
| 7th Circuit | Century Schoolbook | 12pt | 14,000 |
| 11th Circuit | Times New Roman | 14pt | 14,000 |
| N.D. Cal. | Times New Roman | 12pt | 7,000 (motion) |
| D. Oregon | Times New Roman | 12pt | varies |

See `courts.json` for complete list.

---

## VERSION

| Version | Date | Changes |
|---------|------|---------|
| 1.0.0 | 2024-12-20 | Initial |
| 2.0.0 | 2024-12-21 | Complete rewrite with MODEL_INSTRUCTIONS.md |
