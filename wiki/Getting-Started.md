# 🚀 Getting Started

This page explains how to install and use skills from this repository in every Claude interface.

---

## Prerequisites

No prerequisites are needed to use skills that are **pure instructions** (no scripts). For skills that include Python or shell scripts you will need:

| Dependency | Required by | Install |
|------------|-------------|---------|
| Python 3.8+ | docx, pdf, pptx, xlsx, skill-creator, webapp-testing, slack-gif-creator | System package manager |
| Node.js & npm | web-artifacts-builder, docx (JS library) | https://nodejs.org |
| LibreOffice | docx, pptx, xlsx (format conversion) | `sudo apt install libreoffice` |
| Poppler utils | pdf, pptx (PDF → image) | `sudo apt install poppler-utils` |
| Playwright | webapp-testing | `pip install playwright && playwright install chromium` |
| Tesseract OCR | pdf (OCR mode) | `sudo apt install tesseract-ocr` |

Most users only need Python 3.8+; install extra dependencies only for the skills you intend to run scripts from.

---

## Claude Code

Claude Code is the recommended environment for local development workflows that involve skill scripts.

### 1 — Register the marketplace

```
/plugin marketplace add anthropics/skills
```

### 2 — Browse and install a skill group

```
/plugin install document-skills@anthropic-agent-skills
/plugin install example-skills@anthropic-agent-skills
/plugin install claude-api@anthropic-agent-skills
```

| Plugin group | Skills included |
|---|---|
| `document-skills` | docx, pdf, pptx, xlsx |
| `example-skills` | algorithmic-art, brand-guidelines, canvas-design, doc-coauthoring, frontend-design, internal-comms, mcp-builder, skill-creator, slack-gif-creator, theme-factory, web-artifacts-builder, webapp-testing |
| `claude-api` | claude-api |

### 3 — Use a skill

Just mention the skill in your request:

```
Use the PDF skill to extract the form fields from /path/to/form.pdf
Use the DOCX skill to create a project proposal document
Use the algorithmic-art skill to create a flow field composition
```

Claude will automatically load the matching skill and follow its instructions.

### Installing an individual skill from source

Clone this repository and point Claude Code at the skill folder directly:

```bash
git clone https://github.com/d33disc/upstream_skills
```

Then in Claude Code:

```
/skill load ./upstream_skills/skills/mcp-builder
```

---

## Claude.ai

All skills in this repository are already **built into paid Claude.ai plans** — no installation required.

To upload your own custom skill or to activate a specific skill:

1. Open a conversation in Claude.ai.
2. Click **Skills** in the left sidebar.
3. Click **+ Add skill** and upload your `SKILL.md` (and optional supporting files).
4. Enable the skill for the current project.

See the official guide: [Using skills in Claude](https://support.claude.com/en/articles/12512180-using-skills-in-claude).

---

## Claude API

### Using pre-built Anthropic skills

Anthropic's document skills (docx, pdf, pptx, xlsx) are available as built-in API skills. Refer to the [Skills API Quickstart](https://docs.claude.com/en/api/skills-guide#creating-a-skill) for full documentation.

### Uploading a custom skill via the API

```python
import anthropic

client = anthropic.Anthropic()

# 1. Upload the skill file(s)
with open("skills/mcp-builder/SKILL.md", "rb") as f:
    skill_file = client.beta.files.upload(
        file=("SKILL.md", f, "text/markdown"),
    )

# 2. Reference the skill in a message
response = client.beta.messages.create(
    model="claude-opus-4-5",
    max_tokens=4096,
    messages=[{"role": "user", "content": "Build an MCP server for the GitHub API."}],
    system=[{"type": "tool_result", "tool_use_id": skill_file.id}],
    betas=["skills-2025-03-01"],
)
print(response.content[0].text)
```

> **Note:** API feature flags and endpoint paths may change. Always consult the [official API docs](https://docs.anthropic.com) for the latest.

---

## Running Skill Scripts Locally

Some skills include Python utility scripts that you can run directly outside Claude. Below are common entry points.

### Document skills (docx / pptx / xlsx)

```bash
# Unpack a Word document for XML editing
python skills/docx/scripts/office/unpack.py document.docx unpacked/

# Repack after editing
python skills/docx/scripts/office/pack.py unpacked/ output.docx --original document.docx

# Validate the result
python skills/docx/scripts/office/validate.py output.docx

# Recalculate Excel formulas with LibreOffice
python skills/xlsx/scripts/recalc.py workbook.xlsx
```

### PDF processing

```bash
# Extract fillable form field metadata
python skills/pdf/scripts/extract_form_field_info.py form.pdf

# Fill form fields
python skills/pdf/scripts/fill_fillable_fields.py form.pdf filled.pdf field_values.json

# Convert PDF pages to images (for OCR or review)
python skills/pdf/scripts/convert_pdf_to_images.py doc.pdf output_dir/
```

### Web artifact builder

```bash
# Scaffold a new React + Tailwind + shadcn/ui project
bash skills/web-artifacts-builder/scripts/init-artifact.sh my-app
cd my-app && npm run dev

# Bundle to a single self-contained HTML file
bash skills/web-artifacts-builder/scripts/bundle-artifact.sh
```

### Web app testing

```bash
# Run Playwright automation against a local dev server
python skills/webapp-testing/scripts/with_server.py \
  --server "npm run dev" --port 5173 \
  -- python my_automation.py
```

### Slack GIF creator (standalone)

```python
from skills.slack_gif_creator.core.gif_builder import GIFBuilder
from PIL import Image, ImageDraw

builder = GIFBuilder(width=128, height=128, fps=10)
for i in range(12):
    frame = Image.new("RGB", (128, 128), (240, 248, 255))
    draw = ImageDraw.Draw(frame)
    draw.ellipse([(i * 8, i * 8), (64 + i * 4, 64 + i * 4)], fill=(70, 130, 180))
    builder.add_frame(frame)

builder.save("output.gif", num_colors=48, optimize_for_emoji=True)
```

---

## Troubleshooting

| Symptom | Likely cause | Fix |
|---------|-------------|-----|
| `ModuleNotFoundError: No module named 'pypdf'` | Python dependency missing | `pip install pypdf` |
| `soffice: command not found` | LibreOffice not installed | `sudo apt install libreoffice` |
| `pdftoppm: command not found` | Poppler not installed | `sudo apt install poppler-utils` |
| Script exits with LibreOffice lock error | Previous LibreOffice instance still running | `pkill soffice` |
| Claude does not trigger the skill | Skill not installed / not enabled | Re-install or enable in the Skills panel |
| Generated file fails validation | XML structure error | Run `validate.py`, inspect the diff |

---

*See also: [Architecture](Architecture) · [Contributing](Contributing) · [Skills Overview](Skills-Overview)*
