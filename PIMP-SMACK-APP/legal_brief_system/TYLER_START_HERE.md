# TYLER'S LEGAL BRIEF AUTOMATION SYSTEM

## 🎯 What This Does

Automatically generates FRAP-compliant Ninth Circuit briefs from small JSON data files. No Word editing required for structure - just fill in your data and the system builds:

- ✅ Cover page (formatted correctly)
- ✅ Table of Contents (auto-structured)
- ✅ Table of Authorities (auto-generated from citations)
- ✅ All required sections in correct order
- ✅ Signature blocks, certificates, everything
- ✅ **Footnotes auto-generated** from cross-references
- ✅ **Validation** checks everything before generating

---

## 🚀 WORKFLOW (Do These In Order)

### 1️⃣ ADD YOUR FACTS → `evidence_pool.json`
This is your **central evidence pool**. Each fact stays grouped with:
- The statement itself
- Record citation (ER-XX)
- Cross-references to related facts
- Footnote text (so main text flows smoothly)
- Which sections it's used in

### 2️⃣ VALIDATE → Run `VALIDATE.bat`
Checks everything for compliance before you generate.

### 3️⃣ BUILD REVIEW → Run `BUILD_FROM_EVIDENCE.bat`
Creates a readable text file showing how facts flow into sections.

### 4️⃣ GENERATE FILING → Run `GENERATE_FILING.bat`
Creates the final Word documents.

---

## 📁 Data Files (in `data/` folder)

| File                         | Purpose                                           |
| ---------------------------- | ------------------------------------------------- |
| `evidence_pool.json`         | **YOUR MAIN FILE** - Facts with linked references |
| `case_info.json`             | Case numbers, party names, jurisdiction           |
| `issues_presented.json`      | Your legal issues (1 sentence each)               |
| `authorities.json`           | All cases/statutes you cite                       |
| `timeline.json`              | Key dates for Statement of Case                   |
| `arguments.json`             | Argument headings/structure                       |
| `frap_compliance_rules.json` | Complete FRAP rules reference                     |

### Step 2: Generate Your Brief

**Windows**: Double-click `GENERATE_FILING.bat`

Or run:
```powershell
cd "D:\SKilz\NINTH CIR5\legal_brief_system"
python generate_filing_package.py
```

### Step 3: Review and Finalize

Output goes to `legal_brief_system/output/FILING_[case#]_[timestamp]/`

You get:
- `00_FILING_CHECKLIST.md` - Checklist for filing
- `01_COVER_PAGE.docx` - Ready cover page
- `02_BRIEF_BODY.docx` - Full brief structure

---

## 📂 System Structure

```
NINTH CIR5/
├── legal_brief_system/
│   ├── data/                          ← YOUR DATA FILES
│   │   ├── case_info.json             ← Case basics
│   │   ├── issues_presented.json      ← Legal issues
│   │   ├── authorities.json           ← Citations (auto-TOA)
│   │   ├── timeline.json              ← Key dates
│   │   ├── arguments.json             ← Argument structure
│   │   └── argument_content.json      ← Argument drafts
│   ├── output/                        ← GENERATED FILES GO HERE
│   ├── templates/                     ← Master templates
│   ├── generate_brief.py              ← Brief generator
│   ├── generate_cover_integrated.py   ← Cover generator
│   ├── generate_filing_package.py     ← Full package generator
│   ├── GENERATE_FILING.bat            ← Windows launcher
│   └── README.md                      ← Documentation
│
├── COVER_GENERATOR_COMPLETE/          ← Your original cover system
└── (other files)
```

---

## 🤖 Using AI to Help

### Ask Claude/GPT to:

**Add citations:**
> "Read this case and add it to my authorities.json in the correct format"

**Draft arguments:**
> "Based on my timeline.json and the facts in ECF_QUOTES.csv, draft argument I.A about access to courts"

**Build timeline:**
> "Extract key dates from these court documents and format them for timeline.json"

**Fix Bluebook citations:**
> "Check these citations in authorities.json for proper Bluebook format"

---

## 📋 Data File Examples

### case_info.json
```json
{
    "case": {
        "ninth_circuit_number": "24-1234",
        "district_court_number": "3:24-cv-00839-SB"
    },
    "parties": {
        "appellant": {"name": "TYLER ALLEN LOFALL", "pro_se": true}
    }
}
```

### authorities.json (auto-generates Table of Authorities)
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

---

## 🔄 Workflow

```
┌─────────────────────────────────────────────────────────────┐
│  1. EDIT DATA FILES                                         │
│     - Fill in case_info.json (once)                         │
│     - Add citations to authorities.json (as you write)      │
│     - Build timeline.json from your evidence                │
│     - Structure arguments in arguments.json                 │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────┐
│  2. RUN GENERATOR                                           │
│     Double-click GENERATE_FILING.bat                        │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────┐
│  3. REVIEW OUTPUT                                           │
│     - Check cover page format                               │
│     - Fill in argument text sections                        │
│     - Update page numbers in TOC                            │
│     - Add word count                                        │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────┐
│  4. EXPORT & FILE                                           │
│     - Export to PDF                                         │
│     - Combine cover + body                                  │
│     - File via CM/ECF                                       │
└─────────────────────────────────────────────────────────────┘
```

---

## 🛠 Integration with Your Other Tools

### Connect to ECF_QUOTES.csv
The timeline and arguments can pull from your extracted quotes:
- Quotes become record citations
- Page references become ER cites
- Legal points inform argument structure

### Connect to MCP Evidence Server
If using `lofall_evidence_server.py`:
- Timeline events → timeline.json
- Court statements → record citations
- Contradictions → argument points

---

## ❓ Troubleshooting

**"Python not found"**
- Install Python from python.org
- Or run: `winget install Python.Python.3.12`

**"Module not found"**
- No external dependencies needed - pure Python

**"Output looks wrong"**
- Check JSON syntax in data files
- Use jsonlint.com to validate

---

## 📝 Next Steps

1. Open `data/case_info.json` and update with your case details
2. Run `GENERATE_FILING.bat` to see the structure
3. Fill in argument text in generated document
4. Or use `argument_content.json` to pre-draft arguments

The system handles all the formatting - you focus on the substance.
