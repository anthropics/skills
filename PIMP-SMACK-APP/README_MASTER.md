# PIMP SMACK - Master Documentation
## Pro Se Intelligent Motion Processor

---

## THE SYSTEM

```
┌─────────────────────────────────────────────────────────────────────────┐
│                         USER'S MODEL                                     │
│   (Fills out INTAKE_FORM.md → Produces MASTER_SCHEMA.json)              │
└─────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────────┐
│                         PIMP FORMATTER                                   │
│   (Reads MASTER_SCHEMA.json → Uses taxonomy → Outputs documents)        │
└─────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────────┐
│                      COURT-READY FILINGS                                 │
│   (Properly formatted DOCX/PDF ready for CM/ECF)                        │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## FILE MAP

### Core Schema Files
| File | Purpose |
|------|---------|
| `MASTER_SCHEMA.json` | Single source of truth - all case data |
| `MASTER_CASE_CONFIG.json` | Active case configuration |
| `LEGAL_XML_TAGS.json` | Legal XML tag reference (LegalDocML + OOXML) |

### Intake & Instructions
| File | Purpose |
|------|---------|
| `INTAKE_FORM.md` | Step-by-step guide for user's model |
| `CHEAT_SHEET.md` | Quick reference for template generator |

### Taxonomy (Filing Structure)
| File | Purpose |
|------|---------|
| `PimpJuice_instructions/taxonomy/build_manifest.json` | Filing types + build order + heading order |
| `PimpJuice_instructions/taxonomy/filing_types.json` | Construct templates with placeholders |
| `PimpJuice_instructions/taxonomy/heading1_definitions.json` | H1 sections with legal reasons |

### Templates
| File | Purpose |
|------|---------|
| `templates/MOTION_TEMPLATE.xml` | Motion Word 2003 XML template |
| `templates/DECLARATION_TEMPLATE.xml` | Declaration template |
| `templates/NOTICE_TEMPLATE.xml` | Notice template |
| `templates/BUILDING_BLOCKS.xml` | Reusable XML components |
| `templates/TEMPLATE_REGISTRY.json` | Template registry + playlists |
| `templates/FORMATTING_BLOCKS.md` | Formatting reference |

### Generators
| File | Purpose |
|------|---------|
| `template_generator.py` | Main document generator |
| `declaration-builder/scripts/document_builder.py` | Full declaration builder |
| `pimp_collector.py` | Data collection utilities |

### Research
| File | Purpose |
|------|---------|
| `CLAUDE XML research.xml` | LegalDocML research notes |

---

## THE WORKFLOW

### Phase 1: Story Collection (User's Model)
1. User tells their story in plain language
2. Model asks clarifying questions
3. Model fills out `INTAKE_FORM.md` sections
4. Output: Populated `MASTER_SCHEMA.json`

### Phase 2: Claim Building (Backwards)
1. Start with proven facts
2. Model suggests claims that fit
3. User confirms/rejects claims
4. Model maps elements to facts
5. Model assigns UIDs

### Phase 3: Evidence Linking
1. For each piece of evidence:
   - Send to Gemini with complaint + UID system
   - Gemini assigns up to 3 UIDs
   - Screenshots marked on timeline
2. Identify gaps (elements without evidence)
3. Target gaps with RFAs

### Phase 4: Document Generation (PIMP Formatter)
1. Read `MASTER_SCHEMA.json`
2. Look up filing type in `build_manifest.json`
3. Get build order (slots)
4. Get heading order (sections)
5. Fill templates with data
6. Output formatted documents

---

## UID SYSTEM

### Format: [Claim][Element][Defendant]
- **100s place** = Claim number
- **10s place** = Element number
- **1s place** = Defendant number (0 = all)

### Example
```
Claim 1: 42 USC 1983
  Element 1: Color of state law
  Element 2: Deprivation of rights
  
Defendant 1: Officer Smith
Defendant 2: City of LA
Defendant 0: ALL DEFENDANTS

UID 111 = Claim 1, Element 1, Defendant 1 (Officer acted under color of law)
UID 120 = Claim 1, Element 2, All Defendants (All violated rights)
UID 211 = Claim 2, Element 1, Defendant 1
```

### Evidence Linking
Each piece of evidence gets assigned UIDs it satisfies:
```json
{
  "evidence_id": "EV001",
  "description": "Body cam footage",
  "uids_satisfied": ["111", "121", "131"]
}
```

---

## PIMP CLAP CARDS

Track deadlines to avoid procedural traps:

| Card | What | Rule | Consequence |
|------|------|------|-------------|
| **ANSWER** | Response to complaint | FRCP 12(a) - 21 days | Default judgment |
| **DISCOVERY** | Initial disclosures | FRCP 26(a) - 14 days after 26(f) | Sanctions |
| **RFA** | Response to RFA | FRCP 36 - 30 days | Deemed admitted |
| **MSJ** | Motion for Summary Judgment | Per scheduling order | Can't file |
| **PRETRIAL** | Pretrial statement | Per court order | Sanctions |

---

## HEADING SYSTEM

### Level 1 (LEGAL_H1) - Major Sections
Defined in `heading1_definitions.json` with legal reasons.

**Motion/Brief:**
1. INTRODUCTION
2. FACTUAL BACKGROUND
3. LEGAL STANDARD
4. ARGUMENT
5. CONCLUSION

**Appellate Brief (FRAP 28):**
1. JURISDICTIONAL STATEMENT
2. STATEMENT OF THE ISSUES
3. STATEMENT OF THE CASE
4. STATEMENT OF FACTS
5. SUMMARY OF ARGUMENT
6. STANDARD OF REVIEW
7. ARGUMENT
8. CONCLUSION

**Complaint:**
1. PARTIES
2. JURISDICTION AND VENUE
3. FACTUAL ALLEGATIONS
4. CAUSES OF ACTION
5. PRAYER FOR RELIEF

### Level 2 (LEGAL_H2) - Subsections
Numbered I., II., III.

### Level 3 (LEGAL_H3) - Sub-subsections
Lettered A., B., C.

---

## FORMATTING RULES

| Court | Font | Size | Spacing |
|-------|------|------|---------|
| District Court | Times New Roman | 12pt | Double |
| Court of Appeals | Century Schoolbook | 14pt | Double |
| California State | Times New Roman | 12pt | Double |

**All Courts:**
- 1 inch margins
- Letter size (8.5" x 11")
- Page numbers in footer

---

## XML TAGS (Quick Reference)

### Structure
```xml
<LEGAL_H1>ARGUMENT</LEGAL_H1>
<LEGAL_H2>I. The Court Erred</LEGAL_H2>
<LEGAL_H3>A. Standard of Review</LEGAL_H3>
<LEGAL_BODY>Text here...</LEGAL_BODY>
```

### Citations
```xml
<LEGAL_CITE type="case">Twombly, 550 U.S. at 555</LEGAL_CITE>
<LEGAL_CITE type="statute">42 U.S.C. § 1983</LEGAL_CITE>
<LEGAL_CITE type="record">2-ER-345</LEGAL_CITE>
```

### Evidence Links
```xml
<UID_REF>123</UID_REF>
<EVI_REF id="EV001">Exhibit A</EVI_REF>
```

---

## CONSISTENCY MODEL DETECTION

### Idea: Run Multiple Passes

If you run 4 independent model passes on the same evidence:
- **Consistent errors** (same wrong answer 4x) = Model bias/hallucination
- **Consistent correct** (same right answer 4x) = High confidence
- **Inconsistent** (different answers) = Needs human review

This can detect:
- Systematic bias in opposing counsel's filings
- Fraudulent claims with fabricated facts
- Inconsistent testimony

---

## GETTING STARTED

### For User's Model
1. Read `INTAKE_FORM.md`
2. Ask user questions
3. Fill out `MASTER_SCHEMA.json`
4. Send to PIMP for formatting

### For Formatter
1. Read `MASTER_SCHEMA.json`
2. Run `python template_generator.py --help`
3. Generate documents

### Quick Test
```bash
cd d:\Nineth Circuit\CLAUDE_COPILOT HLP\NINTH CIR5\skills\PIMP-SMACK-APP
python template_generator.py --demo
```

---

## NEXT STEPS

1. [ ] Build story intake UI (iPhone compatible)
2. [ ] Integrate Gemini evidence analyzer
3. [ ] Build PIMP CLAP card tracker
4. [ ] Create consistency checker (multi-pass)
5. [ ] Build cyberpunk web interface
6. [ ] Test end-to-end workflow

---

**Built for Pro Se Litigants**
*A-Team Productions*
