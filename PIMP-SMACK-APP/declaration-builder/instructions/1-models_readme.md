1. [Description]
This skill is a complete "pro se domination" toolkit for building legal declarations and associated documents (marketing cards, covers). It features a "Jurisdiction Engine" that applies XML-based formatting overlays for any of the 13 Federal Circuits, defaulting to the Ninth Circuit. It builds declarations using a strict 2+2+1 structure (2 Circumstance, 2 Element, 1 Party-Link statements per fact) and generates "Pimp Slap" trading cards for social media. It integrates with GPT-5.2 for peer review.

2. [requirements]
- Python 3.x
- Standard library modules only (`xml`, `zipfile`, `datetime`, `io`). NO subprocesses, NO `python-docx` dependency.
- `scripts/document_builder.py`: Core XML document builder.
- `scripts/card_generator.py`: HTML/CSS generator for trading cards.
- `templates/`: XML templates for covers and declaration base.

3. [Cautions]
- Do not use `python-docx` or `subprocess` calls; this skill uses direct XML manipulation for performance and compliance.
- Ensure the 2+2+1 fact structure is followed strictly for the declaration logic to work.
- Placeholders like `[CASE_NUMBER]` are case-sensitive and must be populated.
- The "Jurisdiction Engine" relies on XML string replacement; valid XML syntax in templates is critical.

4. [Definitions]
- **2+2+1 Structure**: A strict format for facts: 2 Circumstance statements (context), 2 Element descriptions (primary/supporting fact), 1 Party-Link statement (connection to opponent).
- **Jurisdiction Engine**: System that replaces `[PLACEHOLDER_COVER]` with circuit-specific XML (e.g., `COVER_NINTH.xml`).
- **Pimp Slap Card**: A gamified "trading card" generated as HTML to celebrate litigation milestones.
- **Peer Review**: Automated feedback loop using GPT-5.2 to check legal sufficiency.

5. [log]
(No run logs available yet. This section will be populated by the system upon successful execution.)

6. [model_readme]
To use this skill:

### 1. Build a Declaration
```python
from scripts.document_builder import DeclarationBuilder

# Initialize builder
builder = DeclarationBuilder(
    jurisdiction="ninth", 
    case_number="25-6461", 
    declarant="Tyler Lofall"
)

# Add structured facts
builder.add_fact(
    title="False Statements",
    narrative="Defendants claimed...",
    time_place="Dec 2024",
    parties="Counsel",
    opposing_link="Intentional fraud"
)

# Generate DOCX
builder.save("output_declaration.docx")
```

### 2. Generate a Card
```python
from scripts.card_generator import PimpSlapCard
card = PimpSlapCard.create(stage="06-Opposition", slapped="Clackamas County")
card.save_html("output_card.html")
```
