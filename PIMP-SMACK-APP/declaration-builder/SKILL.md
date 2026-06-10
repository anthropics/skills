---
name: pro-se-domination
description: "Complete pro se litigation toolkit. Creates declarations with proper structure (2 circumstances, 2 elements, 1 party-link per fact), applies jurisdiction-specific formatting via XML, generates pimp slap marketing cards, and coordinates peer review with GPT-5.2. Use when Tyler needs to create court documents, declarations, briefs, or any litigation materials."
license: MIT - See LICENSE.txt
author: Tyler 'Oooo-pus Pimp-Daddy' Lofall & Claude (A-Team Productions)
version: 2.0.0
---

# Pro Se Domination Skill

## "Big Claude Pimpin' Service - Pimp Slap the Otha' Paaaarty!"

Complete litigation automation for pro se litigants.

## Core Capabilities

### 1. Declaration Formatting
Structures raw facts into proper legal declarations:
- **2 Circumstance Statements** - Time/place + parties/roles context
- **2 Element Descriptions** - Primary fact + supporting detail  
- **1+ Party-Link Statement** - Connects opposing party to liability
- **Witnesses** - Optional corroboration
- **Evidence UIDs** - Links to evi-card system

### 2. Jurisdiction Engine
Multi-circuit support for all 13 Federal Circuit Courts:
- Base template (universal FRAP structure)
- GPT-5.2 fetches circuit-specific rules on demand
- XML overlay applied to generate compliant documents
- Cover page uses [PLACEHOLDER_COVER] → resolved to jurisdiction template

### 3. Pimp Slap Card Generator
Collectible marketing cards for completed documents:
- Numbered by litigation stage (01-Complaint → 14-Victory)
- Rarity: Common, Uncommon, Rare, Epic, Legendary
- Referral codes baked in
- 1980s Batman comic style with white glove slap

### 4. Peer Review Integration
- GPT-5.2 reviews completed documents
- Gemini available as backup
- Returns structured feedback
- Tracks revisions

## Document Creation Workflow

```
USER NARRATIVE
     ↓
ELEMENT EXTRACTION (find claims, facts, elements)
     ↓
DECLARATION DRAFTING (2+2+1 structure per fact)
     ↓
[PLACEHOLDER_COVER] inserted
     ↓
JURISDICTION OVERLAY (XML string replacement)
     ↓
PEER REVIEW (GPT-5.2 or Gemini)
     ↓
FINAL DOCUMENT + PIMP SLAP CARD
```

## Placeholder System

Documents use placeholders that resolve to jurisdiction-specific values:

| Placeholder | Resolves To |
|-------------|-------------|
| `[PLACEHOLDER_COVER]` | Full cover page XML for target circuit |
| `[CASE_NUMBER]` | e.g., "25-6461" |
| `[CIRCUIT]` | e.g., "NINTH CIRCUIT" |
| `[FILING_NAME]` | e.g., "DECLARATION IN SUPPORT OF..." |
| `[DECLARANT]` | e.g., "TYLER LOFALL" |
| `[JUDGE_NAME]` | e.g., "Hon. Susan Brnovich" |
| `[JURISDICTION]` | e.g., "Oregon" |
| `[EXECUTION_DATE]` | Date of signing |
| `[EXECUTION_LOCATION]` | City, State of signing |

## File Structure

```
pro-se-domination/
├── SKILL.md              # This file
├── LICENSE.txt           # MIT License
├── instructions/
│   ├── BUILD_DECLARATION.md    # How to build declarations
│   ├── BUILD_COVER.md          # How to build cover pages
│   └── BUILD_CARD.md           # How to build pimp slap cards
├── templates/
│   ├── DECLARATION_BASE.xml    # Base declaration structure
│   ├── COVER_NINTH.xml         # Ninth Circuit cover XML
│   └── CARD_TEMPLATE.html      # Card HTML template
├── scripts/
│   ├── document_builder.py     # Pure Python XML document builder
│   ├── jurisdiction_rules.py   # Circuit rules database
│   ├── card_generator.py       # Card generator
│   └── peer_review.py          # GPT-5.2 integration
└── references/
    ├── FRAP_RULES.md           # Federal Rules summary
    ├── CIRCUIT_OVERRIDES.yaml  # Per-circuit rule differences
    └── UID_SYSTEM.md           # Evidence card UID format
```

## Usage

### Create Declaration
```python
# Read instructions/BUILD_DECLARATION.md first
from scripts.document_builder import DeclarationBuilder

builder = DeclarationBuilder(
    jurisdiction="ninth",
    case_number="25-6461",
    declarant="Tyler Lofall"
)

# Add facts (2+2+1 structure auto-generated)
builder.add_fact(
    title="False Statements in Motion to Dismiss",
    narrative="Defendants stated in their Motion to Dismiss filed on...",
    time_place="December 2024, in the Motion to Dismiss filing",
    parties="Clackamas County, their counsel",
    opposing_link="Defendants deliberately misrepresented facts to the court"
)

# Build with cover
doc = builder.build(cover_template="COVER_NINTH")

# Peer review
from scripts.peer_review import review_with_gpt52
feedback = review_with_gpt52(doc)

# Output
builder.save("/mnt/user-data/outputs/DECLARATION.docx")
```

### Generate Card
```python
from scripts.card_generator import PimpSlapCard

card = PimpSlapCard.create(
    stage="06-Opposition",
    slapped="Clackamas County",
    custom_quote="HALF TRUTHS ARE WHOLE LIES!"
)
card.save_html("/mnt/user-data/outputs/card.html")
```

## The 10-Doc Suite

1. **Complaint** - Initial filing with all claims
2. **Declaration** - Sworn statement of facts ($10/pop)
3. **Request for Judicial Notice** - Official records
4. **Motion Template** - 59(e), 60(b), etc.
5. **Opposition/Reply** - Response briefs
6. **Notice of Appeal** - Initiates appellate review
7. **Appellate Brief** - Main appellate argument
8. **Cover Page** - Circuit-specific covers
9. **Table of Authorities** - Citation index
10. **Evidence Index** - UID-linked evidence cards

## Pricing Model

| Tier | Price | What They Get |
|------|-------|---------------|
| Single Doc | $10 | One formatted document |
| 3-Pack | $15 | Three docs (half off!) |
| Lifetime | $25 | All templates forever |
| After 120 days | $12.50 | Lifetime fire sale |

### Indigent Program
- Post story + pimp slap card on social media = FREE access
- 3 referrals = FREE lifetime membership

## Integration Points

- **council-hub**: GPT-5.2 peer review
- **skill-factory**: Generate new document types
- **ninth-circuit-brief-formatter**: Full brief formatting
- **ninth-circuit-cover-generator**: Cover page templates

## Technical Notes

### XML Approach (No python-docx)
All documents built via direct XML manipulation:
1. Load base template XML
2. String replacement for placeholders
3. Insert structured content blocks
4. Pack to .docx via zipfile (no subprocess)

### No Subprocess Calls
All file operations use pure Python:
- `zipfile` for .docx packing/unpacking
- Direct file I/O for XML
- No `os.system()` or `subprocess`

### UID System (Planned)
Evidence cards use 3-4 character UIDs:
- Position 1: Claim type (C=Constitutional, F=Fraud, P=Procedural)
- Position 2-3: Chronological sequence
- Position 4: Defendant identifier

Example: `C01A` = Constitutional claim #1 against Defendant A
