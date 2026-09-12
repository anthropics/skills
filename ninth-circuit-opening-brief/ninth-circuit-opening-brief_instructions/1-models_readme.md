```markdown
1. [Description]
This skill assembles complete Ninth Circuit opening briefs by processing tagged section files (=== SECTION NAME === format) and combining them in proper FRAP 28 order. Three-script pipeline: (1) 6-ingest_brief_sections.py parses tagged text into sections.json, (2) 5-copy_plain_sections.py updates sections from tagged files with backup option, (3) 4-assemble_opening_brief.py builds final brief from JSON data with TOC/TOA generation, word count validation, and compliance checking. CRITICAL: NO TEXT GENERATION - scripts only copy/assemble existing text verbatim.

2. [requirements]
- Python 3.x standard library (json, argparse, pathlib, re, datetime, collections)
- Brief data files in 9-brief_data/ (sections.json, authorities.json)
- Templates in 8-templates/ (if needed for formatting)
- References in 7-references/ (formatting standards, local rules)
- Tagged input files with === SECTION NAME === markers

3. [Cautions]
- Scripts are READ-ONLY copiers - they NEVER reword or generate text
- Must run scripts in order: 6 (ingest), then 5 (copy), then 4 (assemble)
- FRAP 32 word limit default 14000 words (excludes cover, TOC, TOA, certificates)
- Tagged section names must match SECTION_MAP exactly (case-sensitive)
- sections.json case_info is never touched by ingest/copy scripts
- Use --backup flag before modifying existing sections.json

4. [Definitions]
- **Tagged Sections**: Text format using === HEADING === to mark section boundaries
- **Verbatim Copy**: Exact text transfer with no rewording, styling, or generation
- **FRAP 28**: Federal Rule of Appellate Procedure 28 defining brief structure and order
- **TOC**: Table of Contents (auto-generated from headings)
- **TOA**: Table of Authorities (auto-generated from citations in authorities.json)
- **SECTION_MAP**: Dictionary mapping tag names to JSON section keys

5. [log]
(No run logs available yet. This section will be populated by the system upon successful execution.)

6. [model_readme]
Three-script workflow:

**6-ingest_brief_sections.py** - Parse tagged text into sections.json
```
python 6-ingest_brief_sections.py --input pasted_brief.txt --backup
```

**5-copy_plain_sections.py** - Update specific sections from tagged file
```
python 5-copy_plain_sections.py --input updated_sections.txt --backup
```

**4-assemble_opening_brief.py** - Build final brief
```
python 4-assemble_opening_brief.py --all --case-no 25-XXXXX
python 4-assemble_opening_brief.py --validate  # Check structure
python 4-assemble_opening_brief.py --word-count  # Verify limits
```

Data structure: 9-brief_data/sections.json contains case_info + sections
AUTO_GENERATED sections: cover_page, TOC, TOA, certificates (built by assembler)

```
