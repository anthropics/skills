# Building Cover Pages

## Overview

Cover pages are built using XML templates with placeholder resolution.
Each jurisdiction has its own cover template stored as XML strings.

## Placeholder System

| Placeholder | Description | Example |
|-------------|-------------|---------|
| `{CASE_NUMBER}` | Case number | 25-6461 |
| `{CIRCUIT}` | Circuit name | NINTH |
| `{APPELLANT}` | Appellant name | TYLER LOFALL |
| `{APPELLEE}` | Appellee name | CLACKAMAS COUNTY, ET AL. |
| `{FILING_NAME}` | Document title | DECLARATION IN SUPPORT OF... |
| `{JUDGE_NAME}` | District judge | Hon. Susan Brnovich |

## How It Works

1. **Select Template**: Based on jurisdiction, load the appropriate cover XML
2. **Resolve Placeholders**: String replacement for all placeholders
3. **Insert at Document Start**: Cover XML prepended to document body
4. **Page Break**: Automatic page break after cover

## Ninth Circuit Cover Structure

```
┌─────────────────────────────────────────┐
│           Case No. 25-6461              │
│                                         │
│  IN THE UNITED STATES COURT OF APPEALS  │
│        FOR THE NINTH CIRCUIT            │
│                                         │
│           TYLER LOFALL,                 │
│         Plaintiff-Appellant,            │
│                                         │
│                 v.                      │
│                                         │
│      CLACKAMAS COUNTY, ET AL.,         │
│        Defendants-Appellees.            │
│                                         │
│  DECLARATION IN SUPPORT OF REQUEST      │
│        FOR JUDICIAL NOTICE              │
│                                         │
│  Appeal from the United States District │
│       Court for the District of Oregon  │
│     Hon. Susan Brnovich, District Judge │
└─────────────────────────────────────────┘
                [PAGE BREAK]
```

## Adding New Jurisdictions

1. Create XML template string in `document_builder.py`
2. Add to `COVER_TEMPLATES` dict with circuit key
3. Add jurisdiction config to `JURISDICTIONS` dict

## Template Format

Cover templates use Word Open XML format:

```xml
<w:p>
  <w:pPr><w:jc w:val="center"/></w:pPr>
  <w:r><w:t>Case No. {CASE_NUMBER}</w:t></w:r>
</w:p>
```

## Integration with Declaration Builder

```python
builder = DeclarationBuilder(
    jurisdiction="ninth",
    case_number="25-6461",
    declarant="Tyler Lofall",
    appellant="Tyler Lofall",
    appellee="Clackamas County, et al.",
    judge_name="Hon. Susan Brnovich",
)

# Build with cover page
doc = builder.build(
    filing_name="DECLARATION IN SUPPORT OF REQUEST FOR JUDICIAL NOTICE",
    include_cover=True  # Default is True
)
```

## Circuit-Specific Requirements

### Ninth Circuit
- Case number and short title on cover
- "Appeal from..." block required
- District judge name required

### DC Circuit
- Requires 8 paper copies within 2 days
- Glossary page for acronym-heavy cases

### Federal Circuit
- Technical addendum required for patent cases
- Times New Roman preferred

## Validation

Before finalizing, verify:
- [ ] Case number correct
- [ ] All party names accurate
- [ ] Filing name matches document type
- [ ] Judge name correct
- [ ] Circuit-specific requirements met
