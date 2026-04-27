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
                      - [docx](Q) - Uses docx-js (create) and Python OOXML library (edit), supports tracked changes
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
# Copilot Instructions for Skills Repository

- Purpose: teach AI agents how to extend Claude with modular skills. Each skill is a self-contained folder the agent loads dynamically.

## Fast orientation
- Core map: skills/* holds skills; spec/agent-skills-spec.md documents the standard; template/SKILL.md is the starter template.
- Read SKILL.md frontmatter first (name, description, license), then the body. Skills rely on progressive disclosure: keep instructions concise; move depth into references/ or scripts/.
- Avoid creating extra READMEs or aux docs inside skills; use SKILL.md only. Respect existing licenses (most Apache 2.0; docx/pdf/pptx/xlsx are source-available).

## Skill structure (consistent across folders)
- SKILL.md (required), LICENSE.txt, optional scripts/, references/, assets/. Keep individual reference files under ~10k words.
- scripts/ is for runnable helpers (Python/JS/Bash). Prefer running with --help before reading internals; document parameters with docstrings if you add scripts.
- references/ holds long-form docs; assets/ carries templates/fonts/media; ooxml/schemas/ store XML schemas.

## Critical workflows and examples
- DOCX/PPTX/XLSX OOXML editing (docx/pptx/xlsx skills): unpack → edit → validate (pptx) → pack.
```
python ooxml/scripts/unpack.py <file> <dir>
python ooxml/scripts/validate.py <dir> --original <file>  # pptx
python ooxml/scripts/pack.py <dir> <file>
```
- Document library pattern (docx/pptx): see [skills/docx/ooxml.md](skills/docx/ooxml.md). Use Document.load, query nodes, modify, save. Preserve unchanged runs/RSIDs when redlining.
- Tracked changes workflow (docx): convert to markdown with pandoc --track-changes=all, batch edits (3–10), edit XML via Document, then repack.
- MCP server skills (mcp-builder): prefer TypeScript + streamable HTTP; enforce clear tool prefixes, pagination/filtering support, actionable errors. References in [skills/mcp-builder/reference](skills/mcp-builder/reference).
- Web testing (webapp-testing): wrap app lifecycle with scripts/with_server.py, always wait for networkidle before DOM inspection.
- Creative/layout skills (canvas-design, frontend-design, algorithmic-art): keep outputs concise; use provided assets/fonts; avoid adding new font files.
# Copilot Instructions for Skills Repository

- Purpose: teach AI agents how to extend Claude with modular skills. Each skill is a self-contained folder the agent loads dynamically.

## Fast orientation
- Core map: skills/* holds skills; spec/agent-skills-spec.md documents the standard; template/SKILL.md is the starter template.
- Read SKILL.md frontmatter first (name, description, license), then the body. Skills rely on progressive disclosure: keep instructions concise; move depth into references/ or scripts/.
- Avoid creating extra READMEs or aux docs inside skills; use SKILL.md only. Respect existing licenses (most Apache 2.0; docx/pdf/pptx/xlsx are source-available).

## Skill structure (consistent across folders)
- SKILL.md (required), LICENSE.txt, optional scripts/, references/, assets/. Keep individual reference files under ~10k words.
- scripts/ is for runnable helpers (Python/JS/Bash). Prefer running with --help before reading internals; document parameters with docstrings if you add scripts.
- references/ holds long-form docs; assets/ carries templates/fonts/media; ooxml/schemas/ store XML schemas.

## Critical workflows and examples
- DOCX/PPTX/XLSX OOXML editing (docx/pptx/xlsx skills): unpack → edit → validate (pptx) → pack.
```
python ooxml/scripts/unpack.py <file> <dir>
python ooxml/scripts/validate.py <dir> --original <file>  # pptx
python ooxml/scripts/pack.py <dir> <file>
```
- Document library pattern (docx/pptx): see [skills/docx/ooxml.md](skills/docx/ooxml.md). Use Document.load, query nodes, modify, save. Preserve unchanged runs/RSIDs when redlining.
- Tracked changes workflow (docx): convert to markdown with pandoc --track-changes=all, batch edits (3–10), edit XML via Document, then repack.
- MCP server skills (mcp-builder): prefer TypeScript + streamable HTTP; enforce clear tool prefixes, pagination/filtering support, actionable errors. References in [skills/mcp-builder/reference](skills/mcp-builder/reference).
- Web testing (webapp-testing): wrap app lifecycle with scripts/with_server.py, always wait for networkidle before DOM inspection.
- Creative/layout skills (canvas-design, frontend-design, algorithmic-art): keep outputs concise; use provided assets/fonts; avoid adding new font files.

## Conventions to follow
- Conciseness first: challenge every paragraph; keep SKILL.md <5k words, ideally <500 lines.
- Keep instructions actionable and repo-specific; avoid aspirational guidance.
- When adding new skills, start from [template/SKILL.md](template/SKILL.md) or mirror patterns in [skills/skill-creator/SKILL.md](skills/skill-creator/SKILL.md).
- Do not move shared utilities; reuse scripts/utilities.py and scripts/document.py where possible.
- Cite key references rather than inlining long text; e.g., [skills/docx/docx-js.md](skills/docx/docx-js.md), [skills/pptx/ooxml.md](skills/pptx/ooxml.md), [skills/pdf/reference.md](skills/pdf/reference.md).

## Testing and validation
- No monorepo test runner. Validate document workflows by unpack/edit/pack; for pptx run validate.py.
- For web tests, run with_server wrapper plus your test script; ensure server port matches flag.
- If adding scripts, keep them executable and include minimal usage examples.

## Quick reference
- Specification: [spec/agent-skills-spec.md](spec/agent-skills-spec.md) points to agentskills.io.
- Marketplace metadata lives in .claude-plugin/marketplace.json.
- Common commands: pandoc --track-changes=all input.docx -o output.md, python scripts/thumbnail.py presentation.pptx --cols 4 (pptx thumbnails).

If any section feels unclear or missing for your task, point it out and I will tighten or expand it.
