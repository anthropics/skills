# Legal Brief Automation System

## 🎯 Overview

This system automates the creation of Ninth Circuit appellate briefs by:
1. **Separating data from formatting** - Edit JSON files, not Word docs
2. **Modular section generation** - Each brief section generated independently
3. **FRAP-compliant formatting** - Proper margins, fonts, spacing
4. **AI-friendly structure** - Claude/GPT can help populate JSON data

---

## 📁 Directory Structure

```
legal_brief_system/
├── data/                      # Your case data (edit these!)
│   ├── case_info.json         # Case numbers, parties, jurisdiction
│   ├── issues_presented.json  # Issues and standards of review
│   ├── authorities.json       # Cases, statutes, rules cited
│   ├── timeline.json          # Statement of case events
│   └── arguments.json         # Argument structure and headings
├── templates/                 # Master templates (READ-ONLY)
│   └── BRIEF_TEMPLATE.docx    # Optional: formatted template
├── output/                    # Generated briefs go here
├── generate_brief.py          # Main generator script
└── GENERATE_BRIEF.bat         # Windows launcher
```

---

## 🚀 Quick Start

### 1. Edit Your Data Files

Each JSON file contains one aspect of your brief. Edit them with any text editor or use AI assistance:

**case_info.json** - Basic case information
```json
{
    "case": {
        "ninth_circuit_number": "24-1234",
        "district_court_number": "3:24-cv-00839-SB"
    },
    "parties": {
        "appellant": {
            "name": "YOUR NAME",
            "pro_se": true
        }
    }
}
```

**issues_presented.json** - Your legal issues
```json
{
    "issues": [
        {
            "number": 1,
            "heading": "Access to Courts",
            "issue_statement": "Whether the district court erred...",
            "standard_of_review": "de novo"
        }
    ]
}
```

**authorities.json** - All citations (auto-generates Table of Authorities)
```json
{
    "cases": [
        {
            "name": "Bounds v. Smith",
            "bluebook": "Bounds v. Smith, 430 U.S. 817 (1977)",
            "pages_cited": [8, 13, 15]
        }
    ]
}
```

### 2. Generate the Brief

**Windows:**
```
Double-click GENERATE_BRIEF.bat
```

**Command Line:**
```bash
python generate_brief.py
```

### 3. Review and Fill In

The generated brief includes:
- ✅ Disclosure Statement
- ✅ Table of Contents (with structure)
- ✅ Table of Authorities (auto-generated from citations)
- ✅ Jurisdictional Statement
- ✅ Issues Presented
- ✅ Statement of the Case (from timeline)
- ✅ Standards of Review
- ✅ Argument Structure (headings and subheadings)
- ✅ Conclusion with signature block
- ✅ Certificate of Compliance
- ✅ Certificate of Service

You then fill in:
- Argument text under each heading
- Introduction (optional)
- Summary of Argument
- Page numbers (after pagination)
- Word count

---

## 🤖 AI Integration

### Using Claude/GPT to Help

You can ask AI to:

1. **Generate argument content:**
   > "Based on this timeline and these authorities, write the argument for Issue I about access to courts"

2. **Add citations:**
   > "Add relevant Ninth Circuit cases about access to courts to my authorities.json"

3. **Build timeline:**
   > "Extract key dates from these court documents and format as timeline.json"

4. **Draft issue statements:**
   > "Write issue-presented statements that favor the appellant based on these facts"

### MCP Server Integration

This system works with the `lofall_evidence_server.py` MCP server:

```python
# Evidence from MCP database can populate timeline.json
events = get_timeline_events()

# Contradictions can inform argument structure
contradictions = get_all_contradictions()

# Court statements become record citations
statements = get_court_statements()
```

---

## 📋 FRAP Formatting Rules (Built-in)

The generator enforces:

| Requirement   | Setting              |
| ------------- | -------------------- |
| Font          | Times New Roman 14pt |
| Margins       | 1 inch all sides     |
| Line spacing  | Double-spaced        |
| Footnote font | Same size as text    |
| Page size     | 8.5 x 11 inches      |

---

## 🔧 Customization

### Adding New Sections

Edit `generate_brief.py` to add sections:

```python
def generate_introduction(self) -> str:
    """Generate introduction section"""
    return '\n'.join([
        self.xml.heading("INTRODUCTION", 1),
        self.xml.paragraph("Your intro text here")
    ])
```

### Modifying Formatting

Edit `BriefConfig` class:

```python
class BriefConfig:
    FONT_SIZE = 28  # Half-points (28 = 14pt)
    LINE_SPACING_DOUBLE = 480
```

---

## 📝 Data File Reference

### case_info.json
- Case numbers (district and circuit)
- Party names and types
- Counsel information
- Jurisdiction details

### issues_presented.json  
- Issue numbers and headings
- Issue statements (one sentence)
- Standards of review with citations

### authorities.json
- Cases (with Bluebook citations and page refs)
- Statutes (by U.S.C. title/section)
- Rules (FRAP, FRCP)
- Constitutional provisions

### timeline.json
- Chronological events
- Record citations (ER-XX format)
- Significance notes

### arguments.json
- Roman numeral main arguments
- Letter subarguments
- Citation references per argument

---

## 🎯 Workflow

```
1. [You] Fill in case_info.json with your case details
2. [You] Add timeline events to timeline.json
3. [You] List all citations in authorities.json
4. [You/AI] Structure arguments in arguments.json
5. [You/AI] Write issue statements in issues_presented.json
6. [Script] Generate brief structure
7. [You] Fill in argument text
8. [You] Finalize and file
```

---

## 🔄 Version Control Friendly

Since everything is JSON:
- Track changes with git
- Compare versions easily
- Multiple people can work on different sections
- AI can review and suggest edits to specific files

---

## Questions?

The system is designed to be:
- **Modular** - Change one thing without breaking others
- **Data-driven** - Edit JSON, not complex Word formatting
- **AI-assisted** - Let models help populate content
- **FRAP-compliant** - Formatting rules built in
