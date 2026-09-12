```markdown
1. [Description]
This skill is a PURE PYTHON XML-BASED DOCX GENERATOR that creates legal declarations using direct XML manipulation and zipfile packing. NO subprocess calls. Implements the "2+2+1" declaration structure (2 circumstances + 2 elements + 1 party link per fact). Supports jurisdiction-specific formatting rules (Ninth, First, DC circuits). Builds complete DOCX files from scratch by generating document.xml, styles.xml, and package files, then zipping into .docx format. This is the clean, self-contained approach.

2. [requirements]
- Python 3.x standard library only (os, io, zipfile, datetime, typing, dataclasses, xml.sax.saxutils)
- NO external dependencies (no python-docx, no subprocesses)
- Jurisdiction config database built-in (JURISDICTIONS dict)
- XML templates for document structure, styles, content types, relationships
- DeclarationFact dataclass for 2+2+1 fact structure

3. [Cautions]
- XML must be well-formed or Word will reject the file
- Margins, font sizes, line spacing use Word's measurement units (twips, half-points, twentieths of a point)
- Jurisdiction rules are hardcoded in JURISDICTIONS dict - must update for new circuits
- No validation of fact structure - assumes DeclarationFact objects are properly formed
- Generated files have no edit history or metadata beyond basic document properties

4. [Definitions]
- **2+2+1 Structure**: Declaration format with 2 circumstances (time/place + parties), 2 elements (primary + supporting), 1 party link
- **Twips**: 1/1440th of an inch (Word's base measurement unit for margins)
- **Half-points**: Font size unit where 28 = 14pt
- **XML Manipulation**: Directly editing document.xml instead of using library like python-docx
- **Zipfile Packing**: Creating .docx by zipping XML files (DOCX is a ZIP container)
- **DeclarationFact**: Dataclass representing single fact with title, circumstances, elements, party links, evidence UIDs

5. [log]
(No run logs available yet. This section will be populated by the system upon successful execution.)

6. [model_readme]
This is the GOLD STANDARD approach for document generation:
- No external dependencies beyond Python stdlib
- No subprocess calls
- Direct XML control = perfect formatting preservation
- Jurisdiction-aware via JURISDICTIONS config
- Uses proper legal structure (2+2+1 facts)

Key components:
- document_builder.py: Main XML generator (633 lines)
- DOCUMENT_XML_TEMPLATE: Base document structure
- STYLES_XML: Formatting rules template
- COVER_NINTH_XML: Ninth Circuit cover page template
- JURISDICTIONS: Circuit-specific configs (font, margins, rules)

This should be the model for refactoring other skills.

```
