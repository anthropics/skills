# MODEL INSTRUCTIONS: HOW TO USE THE TAXONOMY FILES

> **YOU MUST READ THIS ENTIRE FILE BEFORE FORMATTING ANY LEGAL DOCUMENT.**

---

## WHAT YOU HAVE

You have 5 taxonomy/config files that define EVERYTHING about legal document formatting:

| File | Location | Purpose |
|------|----------|---------|
| `filing_types.json` | `PimpJuice_instructions/taxonomy/` | 14 filing types (simple version) |
| `build_manifest.json` | `PimpJuice_instructions/taxonomy/` | **DETAILED** - build_order, heading_order, attachments per type |
| `heading1_definitions.json` | `PimpJuice_instructions/taxonomy/` | ~25 H1 section definitions with legal reasoning |
| `courts.json` | `PimpJuice_instructions/jurisdictions/` | Formatting rules per court (fonts, margins, word limits) |
| `local_rules_override.json` | `PimpJuice_instructions/jurisdictions/` | Cascading override system |

### WHICH TO USE?
- **Use `build_manifest.json`** for detailed build info (it has `build_order` with slot notes and `heading_order` with display names)
- **Use `heading1_definitions.json`** for the LEGAL REASON why each section matters
- **Use `courts.json`** for jurisdiction-specific formatting

---

## THE WORKFLOW (YOU MUST FOLLOW THIS ORDER)

```
┌─────────────────────────────────────────────────────────────────────────────┐
│ STEP 1: IDENTIFY FILING TYPE                                                │
│         User says "motion" or "appellate brief" or "complaint"              │
│         → Look up in build_manifest.json → FILING_TYPES[TYPE]               │
└─────────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│ STEP 2: GET BUILD_ORDER                                                     │
│         This is the PHYSICAL BUILD SEQUENCE                                 │
│         → build_manifest.json → FILING_TYPES[TYPE].build_order              │
│         Each slot has: {slot, alt, note, required, optional}                │
└─────────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│ STEP 3: GET HEADING_ORDER                                                   │
│         These are the SECTIONS that go in the Body                          │
│         → build_manifest.json → FILING_TYPES[TYPE].heading_order            │
│         Each has: {h1, display, optional, note}                             │
└─────────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│ STEP 4: LOOK UP LEGAL REASONS                                               │
│         Get the LEGAL REASON why each section matters                       │
│         → heading1_definitions.json → HEADINGS[HEADING_KEY].legal_reason    │
└─────────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│ STEP 5: GET JURISDICTION FORMATTING                                         │
│         Font, size, margins, word limits, special rules                     │
│         → courts.json → [CATEGORY][COURT_ID]                                │
└─────────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│ STEP 6: APPLY OVERRIDES (if any)                                            │
│         Local rules beat district beat circuit beat FRAP                    │
│         → local_rules_override.json                                         │
└─────────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│ STEP 7: BUILD THE DOCUMENT                                                  │
│         For each slot in build_order:                                       │
│         → Generate that piece with correct formatting                       │
│         → Fill placeholders with user content                               │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## STEP 1: IDENTIFY FILING TYPE

### How to do it:

Read `[instructions]/taxonomy/build_manifest.json` → `FILING_TYPES` and find the matching type.

### The 14 Filing Types:

| Type | When to Use |
|------|-------------|
| `MOTION` | Any motion to the court (MTD, MSJ, MTC, etc.) |
| `BRIEF` | Opposition, reply, trial brief, memorandum |
| `APPELLATE_BRIEF` | Circuit court appeal brief |
| `COMPLAINT` | Initiating civil action |
| `ANSWER` | Response to complaint |
| `DECLARATION` | Sworn statement under 28 USC 1746 |
| `NOTICE` | NOA, notice of appearance, etc. |
| `ORDER` | Proposed order or court order |
| `STIPULATION` | Party agreement |
| `DISCOVERY` | Interrogatories, RFPs, RFAs |
| `EXHIBIT` | Evidence submission, exhibit lists |
| `JUDGMENT` | Final or proposed judgment |
| `LETTER` | Court correspondence |
| `SUBPOENA` | Subpoena for testimony/documents |

### Example:

User says: "I need to format my opening brief for the Ninth Circuit"

→ Filing type = `APPELLATE_BRIEF`

---

## STEP 2: GET BUILD_ORDER

### How to do it:

```
build_manifest.json → FILING_TYPES → [YOUR_TYPE] → build_order
```

### What build_order means:

This is the PHYSICAL SEQUENCE of document pieces. You build them IN THIS ORDER.

Each item in build_order is an object with:
- `slot`: The construct slot name
- `alt`: Alternative slot (e.g., Caption or Coverpage)
- `note`: Special instructions
- `required`: true if mandatory
- `optional`: true if optional

### Example for APPELLATE_BRIEF:

```json
"build_order": [
  {"slot": "Coverpage", "required": true},
  {"slot": "TOC"},
  {"slot": "TOA"},
  {"slot": "Body"},
  {"slot": "Cert_of_Compliance"},
  {"slot": "Cert_of_Service"},
  {"slot": "Addendum", "optional": true}
]
```

### Example for MOTION:

```json
"build_order": [
  {"slot": "Caption", "alt": "Coverpage", "note": "Caption for district, Coverpage for appeals"},
  {"slot": "Header"},
  {"slot": "Body"},
  {"slot": "Signature"},
  {"slot": "Cert_of_Service"}
]
```

---

## STEP 3: GET HEADING_ORDER

### How to do it:

```
build_manifest.json → FILING_TYPES → [YOUR_TYPE] → heading_order
```

### What heading_order means:

These are the SECTION HEADINGS that go inside the Body construct.

Each item in heading_order is an object with:
- `h1`: The heading key (used to look up in heading1_definitions.json)
- `display`: The exact text to display as the heading
- `optional`: true if the section is optional
- `note`: Special instructions (e.g., "Numbered: FIRST CAUSE OF ACTION, SECOND...")

### Example for APPELLATE_BRIEF:

```json
"heading_order": [
  {"h1": "JURISDICTIONAL_STATEMENT", "display": "JURISDICTIONAL STATEMENT"},
  {"h1": "STATEMENT_OF_ISSUES", "display": "STATEMENT OF THE ISSUES"},
  {"h1": "STATEMENT_OF_THE_CASE", "display": "STATEMENT OF THE CASE"},
  {"h1": "STATEMENT_OF_FACTS", "display": "STATEMENT OF FACTS"},
  {"h1": "SUMMARY_OF_ARGUMENT", "display": "SUMMARY OF ARGUMENT"},
  {"h1": "STANDARD_OF_REVIEW", "display": "STANDARD OF REVIEW"},
  {"h1": "ARGUMENT", "display": "ARGUMENT"},
  {"h1": "CONCLUSION", "display": "CONCLUSION"},
  {"h1": "RELATED_CASES", "display": "RELATED CASES STATEMENT", "optional": true}
]
```

### Example for MOTION:

```json
"heading_order": [
  {"h1": "INTRODUCTION", "display": "INTRODUCTION"},
  {"h1": "FACTUAL_BACKGROUND", "display": "FACTUAL BACKGROUND"},
  {"h1": "LEGAL_STANDARD", "display": "LEGAL STANDARD"},
  {"h1": "ARGUMENT", "display": "ARGUMENT"},
  {"h1": "CONCLUSION", "display": "CONCLUSION"}
]
```

---

## STEP 4: LOOK UP LEGAL REASONS

### How to do it:

For EACH heading in heading_order, use the `h1` key to look up legal reasons in `heading1_definitions.json`:

```
heading1_definitions.json → HEADINGS → [HEADING_KEY]
```

### What you get:

```json
"JURISDICTIONAL_STATEMENT": {
  "display": "JURISDICTIONAL STATEMENT",
  "style": "LEGAL_H1",
  "used_in": ["APPELLATE_BRIEF"],
  "legal_reason": "FRAP 28(a)(4) MANDATORY. Must cite 28 USC 1291/1292. Must state finality, timeliness. Jurisdictional defect = dismissal. First thing court checks."
}
```

### Use this information to:

1. **display** - The exact text to show as the heading
2. **style** - The XML/Word style to apply (LEGAL_H1, LEGAL_H2, etc.)
3. **legal_reason** - WHY this section matters (tell user if they skip it)

---

## STEP 5: GET JURISDICTION FORMATTING

### How to do it:

User tells you the court. Look it up in `courts.json`:

```
courts.json → [CATEGORY] → [COURT_ID]
```

### Categories:

- `FEDERAL_APPELLATE` - Circuit courts (NINTH_CIRCUIT, SEVENTH_CIRCUIT, etc.)
- `FEDERAL_DISTRICT` - District courts (NDCA, CDCA, DOR, etc.)
- `STATE_APPELLATE` - State appellate courts

### What you get:

```json
"NINTH_CIRCUIT": {
  "display": "United States Court of Appeals for the Ninth Circuit",
  "abbreviation": "9th Cir.",
  "formatting": {
    "font": "Century Schoolbook",
    "font_size": "14pt",
    "line_spacing": "double",
    "margins": "1 inch all sides"
  },
  "word_limits": {
    "opening_brief": 14000,
    "answering_brief": 14000,
    "reply_brief": 7000
  },
  "required_sections": [...],
  "special_rules": {...}
}
```

### APPLY THESE VALUES:

- Use the exact font specified
- Use the exact font size specified
- Use the specified line spacing
- Check word limits and warn if exceeded
- Check required_sections and warn if missing
- Note special_rules and apply them

---

## STEP 6: APPLY OVERRIDES

### How it works:

Formatting rules CASCADE. Later rules override earlier ones:

```
FRAP (base) → Circuit Rules → District Rules → Local Rules → User Override
```

### When to use local_rules_override.json:

If the user specifies a district court case that's now on appeal, OR if they have a specific local rule or court order that changes formatting.

### Example cascade for D. Oregon case in 9th Circuit:

1. Start with `base_frap` from local_rules_override.json
2. Apply `circuit_overrides.9th_circuit`
3. Apply `district_overrides.D_OR`
4. Apply any user-specified override

---

## STEP 7: BUILD THE DOCUMENT

### For each construct in construct_order:

#### A. COVERPAGE (Appellate only)

Generate with:
- Court name (from courts.json → display)
- Case number
- Party names
- Document title
- Lower court info
- Filer info

#### B. CAPTION (District court filings)

Generate with:
- Court name
- Case number
- Judge name (if known)
- Party names in caption format
- Document title

#### C. TOC (Table of Contents)

Auto-generate from:
- All heading1_groups with page numbers
- All LEGAL_H2 subheadings with page numbers

#### D. TOA (Table of Authorities)

Auto-generate from:
- All case citations in document
- All statute citations
- All rule citations
- Grouped by type, alphabetized

#### E. BODY

For each heading in heading1_groups:
1. Output the heading with LEGAL_H1 style
2. Output the content with LEGAL_BODY style
3. For subheadings, use LEGAL_H2, LEGAL_H3, LEGAL_H4

#### F. SIGNATURE

Generate with:
- "Respectfully submitted,"
- Date line
- Signature line
- Filer name
- Filer designation (Pro Se or Attorney for...)
- Address
- Phone
- Email

#### G. CERT_OF_COMPLIANCE (Appellate only)

Generate with:
- Word count
- Font name (from jurisdiction)
- Font size (from jurisdiction)
- Software used

#### H. CERT_OF_SERVICE

Generate with:
- Service date
- Service method (CM/ECF or mail)
- List of served parties (if mail)

---

## XML TAG REFERENCE

Use these tags when generating XML output:

| Tag | Purpose | Example |
|-----|---------|---------|
| `<LEGAL_H1>` | Major section heading | `<LEGAL_H1>ARGUMENT</LEGAL_H1>` |
| `<LEGAL_H2>` | Subsection | `<LEGAL_H2>I. The Court Erred</LEGAL_H2>` |
| `<LEGAL_H3>` | Sub-subsection | `<LEGAL_H3>A. Standard of Review</LEGAL_H3>` |
| `<LEGAL_H4>` | Paragraph-level | `<LEGAL_H4>1. First point</LEGAL_H4>` |
| `<LEGAL_BODY>` | Body text | `<LEGAL_BODY>The court erred...</LEGAL_BODY>` |

---

## PLACEHOLDER REFERENCE

When generating templates, use these placeholders:

### Case Info
- `{{CASE_NUMBER}}` - e.g., "24-1234"
- `{{COURT_NAME}}` - e.g., "United States Court of Appeals for the Ninth Circuit"
- `{{COURT_ABBREV}}` - e.g., "9th Cir."
- `{{DISTRICT_COURT}}` - Lower court name
- `{{DISTRICT_CASE_NO}}` - Lower court case number

### Parties
- `{{APPELLANT_NAME}}` or `{{PLAINTIFF_NAME}}`
- `{{APPELLEE_NAME}}` or `{{DEFENDANT_NAME}}`
- `{{PARTIES}}` - Full caption block

### Filer
- `{{FILER_NAME}}`
- `{{FILER_DESIGNATION}}` - "Pro Se Appellant" or "Attorney for..."
- `{{FILER_ADDRESS}}`
- `{{FILER_PHONE}}`
- `{{FILER_EMAIL}}`

### Document
- `{{DOCUMENT_TITLE}}` - e.g., "APPELLANT'S OPENING BRIEF"
- `{{FILING_DATE}}`
- `{{WORD_COUNT}}`

### Formatting
- `{{FONT}}` - from jurisdiction
- `{{FONT_SIZE}}` - from jurisdiction
- `{{LINE_SPACING}}` - from jurisdiction
- `{{MARGINS}}` - from jurisdiction

---

## COMPLETE EXAMPLE: NINTH CIRCUIT APPELLATE BRIEF

### User Input:
"Format my opening brief for the Ninth Circuit. Case No. 24-1234. Tyler Lofall v. State of Oregon. Appeal from D. Oregon Case No. 3:23-cv-01234."

### Step 1: Filing Type
→ `APPELLATE_BRIEF`

### Step 2: Construct Order
→ `["Coverpage", "TOC", "TOA", "Body", "Cert_of_Compliance", "Cert_of_Service", "Addendum"]`

### Step 3: Heading1 Groups
→ `["JURISDICTIONAL_STATEMENT", "ISSUES", "CASE_STATEMENT", "FACTS", "SUMMARY", "STANDARD_OF_REVIEW", "ARGUMENT", "CONCLUSION"]`

### Step 4: Heading1 Definitions
Look up each:
- JURISDICTIONAL_STATEMENT → "FRAP 28(a)(4) MANDATORY..."
- STATEMENT_OF_ISSUES → "FRAP 28(a)(5). Issues not stated = waived..."
- (etc.)

### Step 5: Jurisdiction Formatting
→ `courts.json` → `FEDERAL_APPELLATE` → `NINTH_CIRCUIT`
- Font: Century Schoolbook
- Size: 14pt
- Line spacing: double
- Margins: 1 inch all sides
- Word limit: 14,000

### Step 6: Build Document

Generate in this order:
1. **COVERPAGE** with case info, parties, title
2. **TOC** with all headings
3. **TOA** with all citations
4. **BODY** with each section:
   - `<LEGAL_H1>JURISDICTIONAL STATEMENT</LEGAL_H1>`
   - `<LEGAL_BODY>[User's content]</LEGAL_BODY>`
   - (repeat for each section)
5. **CERT_OF_COMPLIANCE** with word count, Century Schoolbook 14pt
6. **CERT_OF_SERVICE** with date and CM/ECF
7. **ADDENDUM** if constitutional issues

---

## VALIDATION CHECKLIST

Before outputting, verify:

- [ ] Filing type matches user's request
- [ ] All required_sections from jurisdiction are present
- [ ] Word count is within word_limits
- [ ] Font and size match jurisdiction requirements
- [ ] All construct_order pieces are generated
- [ ] All placeholders are filled
- [ ] Special rules from jurisdiction are noted/applied

---

## COMMON MISTAKES TO AVOID

1. **Don't invent sections** - Only use sections from heading1_groups for that filing type
2. **Don't guess formatting** - Always look up in courts.json
3. **Don't skip certificates** - Required in appellate briefs
4. **Don't mix filing types** - Motion sections ≠ appellate brief sections
5. **Don't ignore legal_reason** - Warn user if skipping required sections

---

## FILE QUICK REFERENCE

```
[instructions]/
├── taxonomy/
│   ├── filing_types.json      ← 14 types, construct_order, heading1_groups
│   └── heading1_definitions.json ← H1 definitions, display, legal_reason
├── jurisdictions/
│   ├── courts.json            ← Formatting rules per court
│   └── local_rules_override.json ← Cascading override system
└── MODEL_INSTRUCTIONS.md      ← THIS FILE
```

---

**END OF MODEL INSTRUCTIONS**
