---
name: declaration-builder
description: "This is a piece of a larger Complete pro se litigation toolkit. This skill Creates declarations with proper structure (2 matching factual actions linking facts to elements; and then to the opposing parties. This applies multi level  rule based that will take a simple routine based variables such as the declaration and adds independant sub class with specific rules to the development of the document. Here we have the Declaration-Builder, and and building away... how ever the begining generic placeholder only tells us the basics, not what type, LR, about what... and then we get into specifics for example here jurisdiction. Every Jurisdiction has its own set of specific rules, formats, procedures, and this will change the coverpage, the  and while we  can make the changes manually to the documents, here we are going to bridge the gap, the ninth cir Juristiction-specific formatting were going to tweak via XML... and make it perfect every time."
license: MIT - See LICENSE.txt
allowed-tools: []
compatibility: "claude-code"
metadata:
     author: "Tyler 'Oooo-pus Pimp-Daddy' Lofall & Claude (A-Team Productions)"
     version: "2.0.0"
---


## Shared Map (Matrix / Cheat Sheet)

Use the shared drafting map to keep document-type definitions and build-order consistent across skills:

- [LEGAL_DOCUMENT_DRAFTING_MAP.md](../_shared/LEGAL_DOCUMENT_DRAFTING_MAP.md)


## Core Capabilities

### 1. Declaration Formatting
Structures raw facts into proper legal declarations:
- **2 Circumstance Statements** - Time/place + parties/roles context
- **2 Element Descriptions** - Primary fact + supporting detail  
- **1+ Party-Link Statement** - Connects opposing party to liability
- **Witnesses** - Optional corroboration


### 2. Jurisdiction Engine
Multi-circuit support for all 13 Federal Circuit Courts:
- Base template (universal FRAP structure)
- GPT-5.2 fetches circuit-specific rules on demand
- XML overlay applied to generate compliant documents
- Cover page uses [PLACEHOLDER_COVER] → resolved to jurisdiction template

### 3. Pimp Slap Card Generator
Collectible marketing cards for completed document Generated:
- Numbered by litigation stage (01-Complaint → 14-Victory)
- Rarity: Common, Uncommon, Rare, Epic, Legendary
- Referral codes baked in
- Think Classic Lawyer Bully picking on Pro Se Plaintiffs with prtocedural-iissue games, false  and half truths, the real 'wolf pack'... not this time! thi Plaintiff is super charged with A-team power! with a world class domination where the rise of the Pro Se Plaintiffs are stepping it up! think cartoon "husstle and flow" meats Risky Business, and every card is styled with white glove slap, frozen in timee at the slap. ALWAYS A court room scene, over the top comedy, attempt to make the Plaintiff as close to real life and matching other 'Pimp Slap Cards' While keeping the art cartoon, heads bigger than normal, the Plaintiff should be slightly miss dressed like he was struggliong, and the opposition should be over the top dirty court room people  and when they get pimp slapped  from the motion or other document filed there should be extreme detail in a freeze frame of their facem, sweat and tears flying from the face, symbolizing the Plaintiff putting them in their place... goal is comedy, showing the corruption of the courts, and fearlessness of the Pro se Party now that they have the 'A-Team' On their side!

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
| `[JUDGE_NAME]` | e.g., "Hon. Stacy F. Beckerman" |
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
# Read instructions/BUILD_DECLARATION.md first STOP FUCKING MAKING UP SHIT !!!!!
from scripts.document_builder import DeclarationBuilder

builder = DeclarationBuilder(
    jurisdiction="ninth",
    case_number="25-6461",
    declarant="Tyler Lofall"

# Build with cover
doc = builder.build(cover_template="COVER_NINTH")

# Peer review
from scripts.peer_review import review_with_gpt52
feedback = review_with_gpt52(doc)

# Output
builder.save("/mnt/user-data/outputs/DECLARATION.docx")
```

card.save_html("/mnt/user-data/outputs/card.html")
```

### Indigent Program
- Post story + pimp slap card on social media = FREE access
- 3 referrals = FREE lifetime membership

## Integration Points

- **council-hub**: GPT-5.2 peer review
- **skill-factory**: Generate new document type
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

