# Copilot Instructions for Skills Repository

## Repository Overview

This is Anthropic's Skills repository - a collection of modular instruction packages that extend Claude's capabilities for specialized tasks. Skills are loaded dynamically by AI agents to perform domain-specific work, from document creation (DOCX, PDF, PPTX, XLSX) to MCP server development, web testing, and creative applications.

## Architecture & Organization

### Skill Structure

Every skill follows this pattern:
```
skills/<skill-name>/
├── SKILL.md              # Required: YAML frontmatter + markdown instructions
├── LICENSE.txt           # License terms
├── scripts/              # Optional: Executable code (Python/JS/Bash)
├── references/           # Optional: Documentation loaded as needed
└── assets/              # Optional: Templates, fonts, media for output
```

**Critical pattern**: Skills use **progressive disclosure**:
1. `name` + `description` in YAML frontmatter (always in context ~100 words)
2. SKILL.md body loaded when skill triggers (<5k words, prefer <500 lines)
3. Bundled resources loaded/executed as needed (scripts can run without reading)

### Key Skills Categories

**Document Skills** (proprietary, reference implementations):
- [docx](skills/docx/) - Uses docx-js (create) and Python OOXML library (edit), supports tracked changes
- [pptx](skills/pptx/) - HTML to PowerPoint conversion, OOXML editing
- [pdf](skills/pdf/) - PDF manipulation, form filling
- [xlsx](skills/xlsx/) - Excel generation and editing

**Development Skills** (Apache 2.0):
- [mcp-builder](skills/mcp-builder/) - Build Model Context Protocol servers (TypeScript preferred)
- [webapp-testing](skills/webapp-testing/) - Playwright automation, uses `scripts/with_server.py`
- [skill-creator](skills/skill-creator/) - Meta-skill for creating new skills

**Creative/Design Skills**:
- [canvas-design](skills/canvas-design/) - Canvas design with 29 licensed fonts
- [frontend-design](skills/frontend-design/) - Modern web design patterns
- [algorithmic-art](skills/algorithmic-art/) - Generative art

## Critical Workflows

### Working with OOXML Documents

**Pattern used in docx/pptx/xlsx skills**:
1. **Unpack** Office file: `python ooxml/scripts/unpack.py <file> <dir>`
2. **Edit** XML directly or use Document library (Python)
3. **Validate** (for PPTX): `python ooxml/scripts/validate.py <dir> --original <file>`
4. **Pack** back: `python ooxml/scripts/pack.py <dir> <file>`

**Document library pattern** (docx/pptx):
```python
from scripts.document import Document
doc = Document.load('unpacked/word/document.xml')
node = doc.get_node('w:p', content_contains='target text')
# Manipulate DOM
doc.save('unpacked/word/document.xml')
```

### Redlining Workflow (DOCX tracked changes)

**Core principle**: Only mark text that changed, preserve original `<w:r>` elements and RSIDs for unchanged text.

Workflow:
1. Convert to markdown: `pandoc --track-changes=all file.docx -o current.md`
2. Group changes into batches (3-10 per batch)
3. Read [ooxml.md](skills/docx/ooxml.md) entirely (never set line ranges)
4. For each batch: grep XML → implement changes with Document library → test
5. Pack final document

### MCP Server Development

**Stack preference**: TypeScript + streamable HTTP (stateless, scales better than stdio)

Key references in [skills/mcp-builder/reference/](skills/mcp-builder/reference/):
- `mcp_best_practices.md` - Core guidelines
- `node_mcp_server.md` - TypeScript patterns
- `python_mcp_server.md` - Python patterns

**Design priorities**:
1. Comprehensive API coverage > specialized workflows
2. Clear, consistent tool naming with prefixes
3. Actionable error messages
4. Context management (pagination, filtering)

### Web Testing Pattern

Use [scripts/with_server.py](skills/webapp-testing/scripts/with_server.py) for server lifecycle:
```bash
python scripts/with_server.py --server "npm run dev" --port 5173 -- python test.py
```

**Critical**: Always `page.wait_for_load_state('networkidle')` before DOM inspection on dynamic apps.

## Project Conventions

### Content Guidelines

1. **Conciseness is paramount** - Context window is shared across all skills. Challenge every paragraph: "Does Claude need this?"
2. **Progressive disclosure** - Split large skills: core workflow in SKILL.md, details in references/
3. **Read full documentation files** - SKILL.md files often mandate "READ ENTIRE FILE" for critical docs (ooxml.md, docx-js.md)
4. **Scripts as black boxes** - Run with `--help` first, don't read source unless necessary

### Documentation Patterns

**SKILL.md structure**:
```markdown
---
name: skill-name
description: Complete description including what it does AND when to use it
license: License info or see LICENSE.txt
---

# Skill Name

## Overview
Brief intro

## Workflow Decision Tree
When to use which approach

## Core Workflows
Step-by-step procedures

## Reference Files
Links to bundled resources
```

**Avoid creating**:
- README.md files within skills (use SKILL.md only)
- Auxiliary documentation (INSTALLATION_GUIDE.md, CHANGELOG.md, etc.)
- User-facing docs (skills are for AI agents)

### Python Patterns

- Use `scripts/` directory for all Python code
- Common utilities in `scripts/__init__.py`, `scripts/utilities.py`, `scripts/document.py`
- Always include docstrings for script parameters
- Prefer black-box script usage over reading source

### File Organization

- `references/` - Documentation loaded as-needed (keep individual files <10k words)
- `scripts/` - Executable code, token-efficient
- `assets/` - Files used in output (templates, fonts, media)
- `ooxml/schemas/` - XML schemas for document validation

## Integration Points

### External Dependencies

**Document creation**:
- `docx-js` (npm) - TypeScript library for DOCX creation
- `pandoc` - Document conversion, especially for tracked changes visualization

**Python**:
- Standard libraries: `xml.etree.ElementTree`, `zipfile`, `json`
- External: `anthropic`, `mcp`, `playwright`, `pillow`, `imageio`

**Validation**:
- OOXML schemas in `ooxml/schemas/` for XML validation

### Testing

No formal test suite. Skills are tested through:
1. Claude.ai integration (paid plans)
2. Claude Code plugin system
3. API integration

## Special Notes

### License Awareness

- Most skills are Apache 2.0 (open source)
- Document skills (docx/pdf/pptx/xlsx) are proprietary/source-available
- Canvas fonts have individual OFL licenses in `skills/canvas-design/canvas-fonts/`

### Specification

Agent Skills specification moved to external site: https://agentskills.io/specification

### Partner Skills

Skills are extensible - partners can create skills for specific software (example: Notion Skills for Claude)

## Quick Reference

**Create new skill**: Use [template/SKILL.md](template/SKILL.md) or follow [skill-creator](skills/skill-creator/SKILL.md) guidance

**Common commands**:
```bash
# OOXML workflows
python ooxml/scripts/unpack.py file.docx unpacked/
python ooxml/scripts/pack.py unpacked/ output.docx
python ooxml/scripts/validate.py unpacked/ --original file.pptx

# Document conversion
pandoc --track-changes=all input.docx -o output.md

# Web testing
python scripts/with_server.py --server "npm run dev" --port 3000 -- python test.py

# Thumbnail generation (PPTX)
python scripts/thumbnail.py presentation.pptx --cols 4
```

**Key files to reference**:
- [spec/agent-skills-spec.md](spec/agent-skills-spec.md) - Points to agentskills.io
- [skills/docx/ooxml.md](skills/docx/ooxml.md) - Document library API (~600 lines, read in full)
- [skills/docx/docx-js.md](skills/docx/docx-js.md) - docx-js usage (~500 lines, read in full)
- [skills/skill-creator/SKILL.md](skills/skill-creator/SKILL.md) - Skill creation patterns
