```markdown
1. [Description]
This skill is a BUILD ORCHESTRATOR that creates complete Ninth Circuit declarations by calling multiple external scripts in sequence: (1) regenerates template with strict formatting from styles.json, (2) generates cover page via COVER_GENERATOR, (3) populates declaration body via RENDER_SCRIPT with placeholder replacement, (4) merges cover + body into final DOCX. Takes a single JSON config file and outputs a 2-page formatted declaration. This is a pipeline coordinator, not a document builder itself.

2. [requirements]
- Python 3.x
- External scripts: COVER_GENERATOR (PIMP-SMACK-APP/_archive/COVER_GENERATOR_COMPLETE/generate_cover.py), RENDER_SCRIPT (universal-motion-brief/scripts/render_docx.py), MERGE_SCRIPT (scripts/merge_docs.py)
- generator.py in 4-scripts folder for template regeneration
- styles.json in skill root (3-styles.json)
- declaration_template.docx in 5-templates folder
- Valid JSON config file (supports both simple legacy format and advanced metadata format)

3. [Cautions]
- All external script paths are hardcoded - they MUST exist or build fails
- Uses subprocess.run() to call external scripts (violates no-subprocess rule)
- Temporary files created in .outbox are deleted after merge
- Config file must have either 'metadata' key (advanced) or 'case_metadata' key (legacy)
- Output filename enforced as YYYY-MM-DD_ToolName-Filename.docx format

4. [Definitions]
- **Build Orchestrator**: Script that coordinates multiple other scripts rather than doing work itself
- **Strict Styles**: Formatting rules from legal_styles_strict.json enforcing court compliance
- **Simple Config**: Legacy format with case_metadata, document_content, formatting keys
- **Advanced Config**: New format with metadata, placeholders.standard, placeholders.runtime, styles keys
- **Merge**: Combining cover page and body into single DOCX file

5. [log]
(No run logs available yet. This section will be populated by the system upon successful execution.)

6. [model_readme]
Run with: `python 4-scripts/build.py [config_file]`
Default config: filing_config.json in current directory

The orchestrator executes this pipeline:
1. generator.py regenerates template with styles from 3-styles.json
2. COVER_GENERATOR creates temp_cover.docx from case metadata
3. RENDER_SCRIPT populates temp_body.docx from document_content placeholders
4. MERGE_SCRIPT combines into final output

WARNING: This uses subprocesses and external dependencies. Does NOT follow self-contained skill pattern. Candidate for refactoring.

```
