---
name: gospelo-md2pdf
description: Convert Markdown files to PDF with Japanese font support and MermaidJS diagram rendering. Use when creating PDFs from markdown, documents with Japanese text, or technical docs with Mermaid diagrams.
---

# Markdown to PDF Converter

Convert Markdown to beautifully formatted PDFs with Japanese text and MermaidJS diagrams.

## Quick Start

```bash
# 1. Install or upgrade (requires v1.2.0+ for Kroki support)
pip install --upgrade gospelo-md2pdf

# 2. Convert markdown to PDF
gospelo-md2pdf input.md
```

## When to Use

Activate this skill when asked to:
- Convert markdown to PDF
- Generate/export a PDF document
- Create PDFs with Japanese text
- Create PDFs with Mermaid diagrams

## Installation

### For Claude Web Environment (Ubuntu)

```bash
# Install gospelo-md2pdf (v1.2.0+ required for Mermaid/Kroki support)
pip install --upgrade gospelo-md2pdf

# Japanese fonts (if Japanese text doesn't render)
apt-get update && apt-get install -y fonts-noto-cjk
```

### For macOS

```bash
brew install pango glib gdk-pixbuf font-noto-sans-cjk-jp
pip install --upgrade gospelo-md2pdf
```

## Mermaid Diagrams Setup

Mermaid diagrams are rendered using the [Kroki API](https://kroki.io) (no local installation required). Supported Mermaid version depends on Kroki (currently v11.x).

**For Claude Web Environment**: Add `kroki.io` to allowed domains:
1. Settings (gear icon) → Capabilities
2. Find "Additional allowed domains"
3. Add `kroki.io`

## Usage

```bash
# Basic (outputs PDF in same directory)
gospelo-md2pdf input.md

# Specify output directory
gospelo-md2pdf input.md -o ./output

# Specify output filename
gospelo-md2pdf input.md output.pdf
```

## Options

| Option | Description |
|--------|-------------|
| `-o, --output-dir` | Output directory |
| `-c, --css` | Custom CSS file |
| `--debug` | Keep intermediate files |
| `-q, --quiet` | Suppress messages |

## Features

- **Japanese Text**: Noto Sans CJK font support
- **MermaidJS**: Flowcharts, sequence diagrams, ER diagrams, etc. (via Kroki API)
- **Tables**: GitHub-flavored markdown tables
- **Code Blocks**: Syntax highlighting
- **Special Classes**: summary, warning, info boxes

## Special HTML Classes

```html
<div class="summary">Summary box (green)</div>
<div class="warning">Warning box (orange)</div>
<div class="info">Info box (blue)</div>
<div class="page-break"></div>
```

## Troubleshooting

| Problem | Solution |
|---------|----------|
| Command not found | `pip install gospelo-md2pdf` |
| Japanese not rendering | `apt-get install fonts-noto-cjk` |
| Mermaid not rendering | Add `kroki.io` to allowed domains (Settings → Capabilities) |
| Kroki connection error | Check network settings and allowed domains |
