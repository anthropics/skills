# Claude Academic Poster Skill

A [Claude Code](https://docs.anthropic.com/en/docs/claude-code) skill that turns a PDF research paper + PPTX template into a professional, conference-ready academic poster.

## What It Does

Given a research paper (PDF) and a poster template (PPTX), this skill guides Claude Code through a complete poster creation workflow: reading the paper, extracting figures, designing the layout, building the poster programmatically with `python-pptx`, and iterating through a render-inspect-fix loop until the result is polished.

The skill includes four bundled Python scripts that automate the most token-intensive parts of the process.

## Prerequisites

**Python packages:**
```bash
uv add python-pptx Pillow pymupdf
# or: pip install python-pptx Pillow pymupdf
```

**System dependencies:**
```bash
# Ubuntu/Debian
sudo apt-get install -y poppler-utils libreoffice-impress

# macOS
brew install poppler libreoffice
```

## Installation

1. Clone this repo into your project's `.claude/skills/` directory:
   ```bash
   cd your-project
   mkdir -p .claude/skills
   git clone https://github.com/sheryc/claude-academic-poster-skill.git .claude/skills/create-academic-poster
   ```

2. Or clone it into your global skills directory:
   ```bash
   git clone https://github.com/sheryc/claude-academic-poster-skill.git ~/.claude/skills/create-academic-poster
   ```

3. That's it. Claude Code will automatically discover the skill from `SKILL.md`.

## Usage

In Claude Code, just ask:

> "Make a poster for my paper using this template"

Provide both files (the PDF paper and PPTX template), and Claude will invoke the skill automatically.

## Workflow Overview

The skill follows six phases:

| Phase | What Happens |
|-------|-------------|
| **1. Understand** | Read the paper, analyze the template's shapes/colors/logos |
| **2. Extract** | Render PDF pages at high DPI, crop figures without captions or line numbers |
| **3. Design** | Plan the poster layout: header, content zones, figure placement |
| **4. Build** | Generate the poster programmatically with `python-pptx` |
| **5. Iterate** | Render PPTX to PNG, inspect regions, fix overlaps/spacing, repeat |
| **6. Deliver** | Output final `.pptx` (editable) and `.pdf` (print-ready) |

Phase 5 is the critical loop — poster text overflow is invisible in code and can only be caught by rendering and visually inspecting.

## Bundled Scripts

| Script | Purpose |
|--------|---------|
| `scripts/analyze_template.py` | Dump shape inventory, extract colors/logos from a template PPTX |
| `scripts/extract_figures.py` | Render PDF pages at high DPI and crop individual figures |
| `scripts/render_poster.py` | Convert PPTX to PDF/PNG with automatic region crops for QA |
| `scripts/measure_text.py` | Measure actual rendered text heights to prevent overflow |

These scripts eliminate the three biggest token sinks in poster creation: template analysis, render pipelines, and text height estimation.

## Reference Docs

- [`references/build_guide.md`](references/build_guide.md) — Detailed guide for building posters with `python-pptx`
- [`references/design_principles.md`](references/design_principles.md) — Visual hierarchy, color, layout, and common mistakes

## Key Design Principles

- **Lead with the result, not the method** — the key finding should be visible from 6 feet away
- **300-600 words maximum** — posters are conversation starters, not papers
- **60-70% visual content** — figures, diagrams, and tables dominate
- **Measure text empirically** — never trust math alone for text height estimation
- **Iterate visually** — every poster needs 3-6 render-inspect-fix rounds

## License

MIT
