# Building Pimp Slap Cards

## Overview

Every completed legal document earns a collectible Pimp Slap Card.
Cards are numbered by litigation stage and have rarity levels.

## Card Structure

```
╔════════════════════════════════════════════════╗
║  [RARITY SYMBOL] [CARD TITLE]                  ║
║────────────────────────────────────────────────║
║                                                ║
║              🖐️  *SLAP*  🖐️                    ║
║                                                ║
║    [SLAPPER] → [SLAPPED]                       ║
║                                                ║
║────────────────────────────────────────────────║
║  "[ACTION QUOTE]"                              ║
║                                                ║
║  [FLAVOR TEXT]                                 ║
║                                                ║
║────────────────────────────────────────────────║
║  Rarity: [RARITY LEVEL]                        ║
║  Date: [DATE EARNED]                           ║
║  Code: [REFERRAL CODE]                         ║
╚════════════════════════════════════════════════╝
```

## Litigation Stages (Numbered)

| Stage | Name | Default Card Title | Rarity |
|-------|------|-------------------|--------|
| 01 | Complaint | First Strike | Common |
| 02 | Answer | The Response | Common |
| 03 | Discovery | Uncovering Truth | Uncommon |
| 04 | Motion to Dismiss | Dismissal Deflector | Uncommon |
| 05 | Summary Judgment | The Slam Dunk | Rare |
| 06 | Opposition | Counter-Slap | Uncommon |
| 07 | Reply | The Last Word | Uncommon |
| 08 | Trial Prep | Battle Ready | Rare |
| 09 | Trial | The Main Event | Epic |
| 10 | Post-Trial | Aftermath | Rare |
| 11 | Notice of Appeal | Round Two | Rare |
| 12 | Appellate Brief | The Supreme Slap | Rare |
| 13 | Oral Argument | Face to Face | Epic |
| 14 | Victory | Total Domination | Legendary |

## Rarity Levels

| Rarity | Symbol | Color | Meaning |
|--------|--------|-------|---------|
| Common | ○ | Gray | Basic filings |
| Uncommon | ◐ | Green | Response documents |
| Rare | ● | Blue | Significant motions |
| Epic | ★ | Purple | Major milestones |
| Legendary | ✦ | Orange | Victory / Fraud exposed |

## Creating Cards

### Basic Card

```python
from scripts.card_generator import PimpSlapCard, LitigationStage

card = PimpSlapCard.create(
    stage=LitigationStage.S06_OPPOSITION,
    slapped="Clackamas County",
    custom_quote="HALF TRUTHS ARE WHOLE LIES!",
)
```

### With Custom Title

```python
card = PimpSlapCard.create(
    stage=LitigationStage.S06_OPPOSITION,
    slapped="Clackamas County",
    custom_title="Declaration vs False Statements",
    custom_quote="YOU SAID IT TWICE AND LIED TWICE!",
    case_number="25-6461",
)
```

### Special Cards

```python
from scripts.card_generator import create_special_card

card = create_special_card(
    "FRAUD_EXPOSED",
    slapped="Clackamas County",
    case_number="25-6461",
)
```

## Output Formats

### ASCII (Terminal)

```python
print(card.render_ascii())
```

### HTML (App/Web)

```python
card.save_html("/path/to/card.html")
```

The HTML version uses:
- 1980s Batman comic style
- Animated slap effect
- Glowing rarity borders
- Bangers font for impact

## Referral System

Each card has a unique referral code:
- Format: `SLAP-XXXXXXXX`
- Generated from card ID + date + slapper name
- Used for indigent program tracking

## Integration with Documents

After creating a document:

```python
# 1. Build declaration
builder = DeclarationBuilder(...)
builder.save("/path/to/declaration.docx")

# 2. Generate matching card
card = PimpSlapCard.create(
    stage=LitigationStage.S06_OPPOSITION,  # Match document type
    slapped="Clackamas County",
    case_number=builder.case_number,
)
card.save_html("/path/to/card.html")
```

## Prompt Template for AI Image Generation

When requesting a comic-style card image:

```
Create a 1980s Batman comic style courtroom sketch showing:
- Tyler (hero) wearing a white glove delivering a dramatic slap
- Clackamas County representative (villain) recoiling from the impact
- "POW!" or "SLAP!" effect text in classic comic style
- Courtroom background with dramatic lighting
- Style: Bold lines, halftone dots, primary colors
- Text: "[ACTION_QUOTE]"
- Include case number badge: "[CASE_NUMBER]"

Follow the style defined in the pimp slap card system.
Make it dramatic and victorious.
```

## Special Cards Available

| Key | Title | Quote | Rarity |
|-----|-------|-------|--------|
| FRAUD_EXPOSED | Fraud Upon the Court | FIVE YEARS OF LIES EXPOSED! | Legendary |
| HALF_TRUTHS | Half Truths Are Whole Lies | YOU SAID IT TWICE AND LIED TWICE! | Epic |
| LATE_FILING | Time's Up, Clown | YOUR REPLY IS LATE - STRIKE IT! | Rare |
