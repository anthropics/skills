# Copilot Instructions for Skills Repository

## Repository Purpose

This repository contains **Agent Skills** - modular packages that extend Claude's capabilities with specialized knowledge, workflows, and tool integrations. Skills are self-contained folders with a `SKILL.md` file (YAML frontmatter + Markdown instructions) and optional bundled resources (scripts, references, assets).

## Core Architecture

### Skill Anatomy
```
skill-name/
├── SKILL.md (required)
│   ├── YAML frontmatter: name, description, license
│   └── Markdown: instructions loaded when skill triggers
├── scripts/          - Executable code (Python/Bash/etc.) for deterministic operations
├── references/       - Documentation loaded into context as needed
└── assets/          - Output resources (templates, icons, fonts) not loaded into context
```

### Two Plugin Collections
Located in `.claude-plugin/marketplace.json`:
- **document-skills**: OOXML manipulation (xlsx, docx, pptx, pdf) - source-available, proprietary
- **example-skills**: Open source skills (Apache 2.0) demonstrating various capabilities

## Key Conventions

### SKILL.md Structure
- **Frontmatter**: Only `name` and `description` determine when skill triggers - be comprehensive
- **Body**: Only loaded AFTER skill triggers. Keep concise - context window is shared resource
- **Principle**: Default assumption is Claude is already smart. Only add context Claude doesn't have
- Use `**MANDATORY - READ ENTIRE FILE**` or `**CRITICAL**` for essential instructions in workflows

### Resource Organization
- **scripts/**: For tasks that would be rewritten repeatedly or need deterministic reliability
- **references/**: For documentation loaded on-demand (schemas, API docs, detailed guides)
  - If >10k words, include grep search patterns in SKILL.md
  - Avoid duplication between SKILL.md and references/
- **assets/**: For files used in output, not loaded into context

### Python Script Patterns
- Use `#!/usr/bin/env python3` shebang
- Import from `skills.<skill-name>.scripts.module` (e.g., `from skills.docx.scripts.document import Document`)
- `__init__.py` exists to make scripts directories importable packages
- Common utilities in `utilities.py`, main classes in specific modules (e.g., `document.py`)

## OOXML Document Skills (docx/pptx/xlsx/pdf)

### Common Workflow Pattern
1. **Read specification files completely**: Files like `ooxml.md`, `docx-js.md` contain complete APIs
   - Never set line range limits when reading these
   - They document the full library API and XML patterns
2. **Unpack**: `python ooxml/scripts/unpack.py <office_file> <output_dir>`
3. **Edit**: Use Python libraries or direct XML manipulation
4. **Pack**: `python ooxml/scripts/pack.py <input_dir> <office_file>`

### DOCX Specific
- **Document library** (`skills/docx/scripts/document.py`): High-level API for OOXML manipulation
  - Auto-handles RSIDs, author attribution, date stamps for tracked changes
  - `doc["word/document.xml"]` for DOM access
- **Redlining workflow**: For document review with tracked changes
  - Minimal, precise edits: only mark text that actually changes
  - Batch changes in groups of 3-10 for debugging
  - Extract original `<w:r>` elements with RSID for unchanged text
- **docx-js**: For creating new documents from scratch using JavaScript/TypeScript

### PPTX Specific  
- **html2pptx workflow**: Convert HTML slides to PowerPoint with accurate positioning
- Always analyze theme (`ppt/theme/theme1.xml`) and slide content for typography/colors when emulating designs

## MCP Builder Skill

Specialized skill for creating Model Context Protocol servers:
- **Evaluation harness**: `scripts/evaluation.py` tests MCP servers against Claude
- **References**: `reference/` contains best practices, TypeScript/Python patterns
- Emphasizes comprehensive API coverage, clear tool naming, actionable error messages

## Skill Creator Skill

Meta-skill for creating new skills:
- **Three degrees of freedom**:
  - High: text-based instructions (multiple valid approaches)
  - Medium: pseudocode/scripts with parameters (preferred patterns)
  - Low: specific scripts (fragile operations requiring consistency)
- Keep SKILL.md concise, move detailed info to references/
- Use `references/workflows.md` for workflow pattern examples

## Development Commands

### Python Skills
```bash
# Most Python skills have requirements.txt in scripts/ or root
pip install -r requirements.txt

# OOXML operations (docx/pptx/xlsx)
python ooxml/scripts/unpack.py <file> <dir>
python ooxml/scripts/pack.py <dir> <file>

# Document conversion
pandoc --track-changes=all input.docx -o output.md
python -m markitdown input.pptx  # For presentations
```

### Testing
- MCP servers: Use `scripts/evaluation.py` with test questions and Claude API
- No centralized test suite - each skill is self-contained

## Writing Style Guidelines

- **Concise**: Context window is public good, challenge every paragraph's token cost
- **Specific examples**: Prefer concrete examples from codebase over verbose explanations
- **Critical markers**: Use `**MANDATORY**`, `**CRITICAL**` for essential non-negotiable instructions
- **Workflow decision trees**: Use conditional branching (e.g., docx editing vs. creating)
- **Action-oriented**: Focus on what to do, not what the skill can theoretically do

## Common Patterns to Follow

1. **Workflow-first organization**: Skills start with "when to use" decision trees
2. **Read-first mandates**: Complex APIs documented in reference files that must be read completely
3. **Batching strategies**: For operations like tracked changes, group related edits (3-10 changes)
4. **Template directories**: Many skills include `templates/` for boilerplate code
5. **License clarity**: Mix of Apache 2.0 (open source) and proprietary (source-available) - always check LICENSE.txt
