# PIMP SMACK - CHEAT SHEET
## Legal Document Generation System

---

## GOLDEN RULE
```
NO FILE EDITING REQUIRED
Everything is programmatic - call functions with data, get documents out.
```

---

## QUICK START

### Generate a Motion
```python
from template_generator import TemplateGenerator

gen = TemplateGenerator()
gen.generate_and_save_motion({
    "INTRODUCTION_TEXT": "Your intro here...",
    "STATEMENT_OF_FACTS_TEXT": "Facts here...",
    "ARGUMENT_I_TITLE": "THE COURT SHOULD GRANT THIS MOTION",
    "ARGUMENT_I_TEXT": "Because...",
    "CONCLUSION_TEXT": "For these reasons...",
    "DOCUMENT_TITLE": "Motion for Summary Judgment"
}, "my_motion")
```

### Generate a Declaration
```python
gen.generate_and_save_declaration({
    "DECLARANT_NAME": "Tyler Allen Lofall",
    "DECLARANT_NAME_CAPS": "TYLER ALLEN LOFALL",
    "FACT_1_IDENTITY": "I am the Plaintiff in this action...",
    "FACT_2_RELATIONSHIP": "I have personal knowledge...",
    "FACT_3_PRIMARY": "On October 1, 2025...",
    "FACT_4_SUPPORTING": "The CM/ECF system confirmed...",
    "FACT_5_CONCLUSION": "Based on the foregoing..."
}, "my_declaration")
```

### Generate a Notice
```python
gen.generate_and_save_notice({
    "NOTICE_TITLE": "NOTICE OF MOTION",
    "NOTICE_RECIPIENTS": "All Counsel of Record",
    "NOTICE_BODY": "Appellant will move this Court..."
}, "my_notice")
```

---

## FILE LOCATIONS

| File | Purpose |
|------|---------|
| `template_generator.py` | **MAIN SCRIPT** - Call this |
| `MASTER_CASE_CONFIG.json` | Your case data (auto-fills placeholders) |
| `templates/TEMPLATE_REGISTRY.json` | Lists all templates & placeholders |
| `templates/BUILDING_BLOCKS.xml` | Individual XML components |
| `templates/FORMATTING_BLOCKS.md` | Formatting reference |
| `output/` | Generated documents go here |

---

## TEMPLATES AVAILABLE

### 1. MOTION (`motion`)
**File:** `templates/MOTION_TEMPLATE.xml`

**Required Data:**
- `INTRODUCTION_TEXT` - Opening paragraph
- `STATEMENT_OF_FACTS_TEXT` - Facts section
- `ARGUMENT_I_TITLE` - First argument heading
- `ARGUMENT_I_TEXT` - First argument body
- `CONCLUSION_TEXT` - Closing paragraph
- `DOCUMENT_TITLE` - For certificate of service

**Optional:**
- `ARGUMENT_II_TITLE`, `ARGUMENT_II_TEXT`
- `ARGUMENT_III_TITLE`, `ARGUMENT_III_TEXT`

---

### 2. DECLARATION (Two Options)

#### Option A: XML Template (`declaration`)
**File:** `templates/DECLARATION_TEMPLATE.xml`
**Output:** `.xml` (Word 2003)

**Required Data:**
- `DECLARANT_NAME` - "Tyler Allen Lofall"
- `DECLARANT_NAME_CAPS` - "TYLER ALLEN LOFALL"
- `FACT_1_IDENTITY` - Who you are
- `FACT_2_RELATIONSHIP` - Connection to case
- `FACT_3_PRIMARY` - Main substantive fact
- `FACT_4_SUPPORTING` - Supporting fact
- `FACT_5_CONCLUSION` - Summary fact

#### Option B: DOCX Builder (Recommended)
**File:** `declaration-builder/scripts/document_builder.py`
**Output:** `.docx` (standard)

```python
gen.generate_declaration_docx([
    {
        "title": "Identity and Knowledge",
        "circumstance_time_place": "At all times relevant...",
        "circumstance_parties": "I am the Plaintiff...",
        "element_primary": "I have personal knowledge...",
        "element_supporting": "I reviewed the documents...",
        "party_link": "Defendants failed to..."
    }
], "my_declaration")
```

**Features:** Multi-jurisdiction, proper 2+2+1 structure, cover page included

---

### 3. NOTICE (`notice`)
**File:** `templates/NOTICE_TEMPLATE.xml`

**Required Data:**
- `NOTICE_TITLE` - "NOTICE OF MOTION"
- `NOTICE_RECIPIENTS` - "All Counsel of Record"
- `NOTICE_BODY` - What you're giving notice of

**Optional:**
- `NOTICE_DATE`, `NOTICE_TIME`, `NOTICE_LOCATION`
- `ADDITIONAL_NOTICE`

---

### 4. COVER PAGE (`cover`)
**File:** `COVER_GENERATOR_COMPLETE/TEMPLATE_CAPTION.docx`
**Generator:** `COVER_GENERATOR_COMPLETE/generate_cover.py`

**Already programmatic!** Call directly:
```python
# From COVER_GENERATOR_COMPLETE directory
python generate_cover.py
```

---

## AUTO-FILLED FROM CONFIG

These placeholders are automatically filled from `MASTER_CASE_CONFIG.json`:

| Placeholder | Source |
|-------------|--------|
| `{{CASE_NUMBER}}` | `case_info.case_number` |
| `{{PARTY_NAME}}` | `party_info.name` |
| `{{PARTY_NAME_CAPS}}` | `party_info.name.upper()` |
| `{{ADDRESS_LINE_1}}` | `party_info.address_line_1` |
| `{{CITY_STATE_ZIP}}` | `party_info.city_state_zip` |
| `{{EMAIL}}` | `party_info.email` |
| `{{PHONE}}` | `party_info.phone` |
| `{{DAY}}` | Current day |
| `{{MONTH}}` | Current month name |
| `{{YEAR}}` | Current year |
| `{{SERVICE_DATE}}` | Today's date formatted |
| `{{JUDGE_NAME}}` | `case_info.judge_name` |

---

## PLAYLISTS (Document Packages)

### Full Motion Package
```python
gen.generate_playlist("full_motion_package", {
    # Motion data
    "INTRODUCTION_TEXT": "...",
    # Declaration data
    "FACT_1_IDENTITY": "...",
    # etc.
})
```

**Outputs:** Cover + Motion + Declaration (merged)

### Opposition Package
```python
gen.generate_playlist("opposition", {...})
```

**Outputs:** Cover + Motion

### Notice Package
```python
gen.generate_playlist("notice_package", {...})
```

**Outputs:** Cover + Notice + Declaration

---

## BUILDING BLOCKS

For custom documents, use individual blocks from `BUILDING_BLOCKS.xml`:

| Block ID | What It Does |
|----------|--------------|
| `HEADING_1` | Centered section title |
| `HEADING_2` | Numbered subsection (I., II.) |
| `BODY_PARAGRAPH` | Double-spaced body text |
| `NUMBERED_FACT` | Declaration fact (1., 2.) |
| `SIGNATURE_LINE` | Edwardian Script /s/ |
| `NAME_BLOCK` | NAME IN CAPS, Pro se |
| `ADDRESS_BLOCK` | Full address with MAIL ONLY |
| `CERTIFICATE_OF_SERVICE` | CM/ECF certificate |
| `HEADER` | Case number header |
| `FOOTER` | Page number footer |

---

## OUTPUT FORMAT

All documents output as `.xml` files that:
- ✓ Open directly in Microsoft Word
- ✓ Preserve all formatting
- ✓ Include headers/footers
- ✓ Have page numbers (field codes)
- ✓ Use correct fonts (Californian FB, Edwardian Script ITC)

---

## FORMATTING SPECS

| Element | Font | Size | Style |
|---------|------|------|-------|
| Heading 1 | Californian FB | 14pt | Bold, Centered |
| Heading 2 | Californian FB | 14pt | Bold, Numbered |
| Body | Californian FB | 14pt | Normal |
| Signature | Edwardian Script ITC | 26pt | Bold, Italic, Underline |
| Header | Californian FB | 14pt | Bold |
| Footer | Times New Roman | 10pt | Normal |

**Page:** Letter (8.5" x 11"), 1" margins all around

---

## TROUBLESHOOTING

**Document won't open in Word?**
- Check XML is valid (no unclosed tags)
- Ensure file has `.xml` extension

**Placeholders not replaced?**
- Check spelling matches exactly: `{{PLACEHOLDER}}`
- Check data dict has the key

**Wrong case number?**
- Update `MASTER_CASE_CONFIG.json`

---

## RELATED FILES

- **Cover Generator:** `d:\Nineth Circuit\CLAUDE_COPILOT HLP\NINTH CIR5\COVER_GENERATOR_COMPLETE\`
- **Declaration Builder:** `d:\Nineth Circuit\CLAUDE_COPILOT HLP\NINTH CIR5\skills\declaration-builder\`
- **Brief Assembler:** `d:\Nineth Circuit\CLAUDE_COPILOT HLP\NINTH CIR5\skills\ninth-circuit-opening-brief\`

---

## REMEMBER

```
┌─────────────────────────────────────────────────────────┐
│  NO MANUAL EDITING                                       │
│  Call template_generator.py → Pass data → Get document  │
└─────────────────────────────────────────────────────────┘
```
