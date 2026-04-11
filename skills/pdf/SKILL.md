---
name: pdf
description: Use this skill whenever the user wants to do anything with PDF files. This includes reading or extracting text/tables from PDFs, combining or merging multiple PDFs into one, splitting PDFs apart, rotating pages, adding watermarks, creating new PDFs, filling PDF forms, encrypting/decrypting PDFs, extracting images, and OCR on scanned PDFs to make them searchable. If the user mentions a .pdf file or asks to produce one, use this skill.
license: Proprietary. LICENSE.txt has complete terms
---

# PDF Processing Guide

## Overview

This guide covers essential PDF processing operations using Python libraries and command-line tools. For advanced features, JavaScript libraries, and detailed examples, see REFERENCE.md. If you need to fill out a PDF form, read FORMS.md and follow its instructions.

## Critical Portable Output Requirements

Apply these rules whenever the user asks for a generated PDF deliverable:

1. Save the final deliverable as `output.pdf` unless the user explicitly asks for a different filename.
2. Never rely on machine-local custom fonts (for example fonts available on one Mac only). Cross-platform readers on Windows/Android may substitute or break layout.
3. For non-ASCII text (Chinese, Japanese, Korean, symbols), use an embeddable TrueType-outline font and embed it in the PDF. Prefer `.ttf`; only use `.otf` when it is known to work with `reportlab`.
4. Do not put critical content only in viewer-dependent annotation layers when portability matters. Prefer writing text into page content.
5. Before returning the file, do a quick sanity check for portability risks (missing glyphs, obvious overflow, broken line wraps).

## Preferred PDF Authoring Path

Keep generation simple and deterministic:

1. Use `reportlab` for PDF writing and `pypdf` for merge/edit steps.
2. Do not switch to `fpdf2` just to work around font issues in this skill flow.
3. Do not rely on ad-hoc `fonttools` TTC-to-TTF conversion during task execution.
4. In the AstrBot sandbox (`astrbotdevs/shipyard-neo-ship:latest` running in a macOS Docker environment), do not treat local TTC collections as the default path. Many macOS TTC fonts use PostScript outlines that `reportlab` rejects.
5. Prefer one stable downloaded or bundled `.ttf` fallback font. If no embeddable font is available and the document only needs Chinese text, `UnicodeCIDFont("STSong-Light")` is an acceptable non-embedded fallback.

## Local CJK Font Discovery Policy

For Linux/sandbox environments, discovering local fonts via `fc-list` is optional. Treat it as a probe, not a guarantee.

```python
import subprocess

result = subprocess.run(
    ["fc-list", ":lang=zh", "-f", "%{file}\\n"],
    capture_output=True,
    text=True,
    timeout=4,
    check=False,
)
```

Rules:

1. Use `timeout` and `check=False` to avoid hanging or hard failure.
2. Treat `fc-list` results as candidates, not guaranteed usable fonts.
3. Prefer `.ttf` candidates first. Only try `.otf` if `reportlab` can actually load it.
4. Do not auto-assume `.ttc` is usable in the AstrBot sandbox. An `invalid character '—'` error is a string-quoting bug; `postscript outlines are not supported` is a font-compatibility bug.
5. If no compatible local font exists, download one fallback font into the working directory and reuse it. If download is impossible and the content is Chinese-only, fall back to `STSong-Light` and mention that it is not embedded.

## Final Response Requirements

When you create or modify a PDF file, your final response must include:

1. A direct downloadable file result (attachment/file output when the platform supports it).
2. The exact output path for fallback download, including the final `output.pdf` location.
3. A short note if custom fonts were embedded (or if fallback fonts were used).

## Quick Start

```python
from pypdf import PdfReader, PdfWriter

# Read a PDF
reader = PdfReader("document.pdf")
print(f"Pages: {len(reader.pages)}")

# Extract text
text = ""
for page in reader.pages:
    text += page.extract_text()
```

## Python Libraries

### pypdf - Basic Operations

#### Merge PDFs
```python
from pypdf import PdfWriter, PdfReader

writer = PdfWriter()
for pdf_file in ["doc1.pdf", "doc2.pdf", "doc3.pdf"]:
    reader = PdfReader(pdf_file)
    for page in reader.pages:
        writer.add_page(page)

with open("merged.pdf", "wb") as output:
    writer.write(output)
```

#### Split PDF
```python
reader = PdfReader("input.pdf")
for i, page in enumerate(reader.pages):
    writer = PdfWriter()
    writer.add_page(page)
    with open(f"page_{i+1}.pdf", "wb") as output:
        writer.write(output)
```

#### Extract Metadata
```python
reader = PdfReader("document.pdf")
meta = reader.metadata
print(f"Title: {meta.title}")
print(f"Author: {meta.author}")
print(f"Subject: {meta.subject}")
print(f"Creator: {meta.creator}")
```

#### Rotate Pages
```python
reader = PdfReader("input.pdf")
writer = PdfWriter()

page = reader.pages[0]
page.rotate(90)  # Rotate 90 degrees clockwise
writer.add_page(page)

with open("rotated.pdf", "wb") as output:
    writer.write(output)
```

### pdfplumber - Text and Table Extraction

#### Extract Text with Layout
```python
import pdfplumber

with pdfplumber.open("document.pdf") as pdf:
    for page in pdf.pages:
        text = page.extract_text()
        print(text)
```

#### Extract Tables
```python
with pdfplumber.open("document.pdf") as pdf:
    for i, page in enumerate(pdf.pages):
        tables = page.extract_tables()
        for j, table in enumerate(tables):
            print(f"Table {j+1} on page {i+1}:")
            for row in table:
                print(row)
```

#### Advanced Table Extraction
```python
import pandas as pd

with pdfplumber.open("document.pdf") as pdf:
    all_tables = []
    for page in pdf.pages:
        tables = page.extract_tables()
        for table in tables:
            if table:  # Check if table is not empty
                df = pd.DataFrame(table[1:], columns=table[0])
                all_tables.append(df)

# Combine all tables
if all_tables:
    combined_df = pd.concat(all_tables, ignore_index=True)
    combined_df.to_excel("extracted_tables.xlsx", index=False)
```

### reportlab - Create PDFs

#### Basic PDF Creation
```python
from reportlab.lib.pagesizes import letter
from reportlab.pdfgen import canvas

c = canvas.Canvas("hello.pdf", pagesize=letter)
width, height = letter

# Add text
c.drawString(100, height - 100, "Hello World!")
c.drawString(100, height - 120, "This is a PDF created with reportlab")

# Add a line
c.line(100, height - 140, 400, height - 140)

# Save
c.save()
```

#### Create PDF with Multiple Pages
```python
from reportlab.lib.pagesizes import letter
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, PageBreak
from reportlab.lib.styles import getSampleStyleSheet

doc = SimpleDocTemplate("report.pdf", pagesize=letter)
styles = getSampleStyleSheet()
story = []

# Add content
title = Paragraph("Report Title", styles['Title'])
story.append(title)
story.append(Spacer(1, 12))

body = Paragraph("This is the body of the report. " * 20, styles['Normal'])
story.append(body)
story.append(PageBreak())

# Page 2
story.append(Paragraph("Page 2", styles['Heading1']))
story.append(Paragraph("Content for page 2", styles['Normal']))

# Build PDF
doc.build(story)
```

#### Python String Safety (Avoid SyntaxError)

Unicode punctuation is usually not the real problem. Errors such as `invalid character '—' (U+2014)` often happen because the string was terminated early by an apostrophe or mismatched quote.

```python
import json
from pathlib import Path

# Preferred: load report text from UTF-8 data instead of hand-writing long literals.
report_data = json.loads(Path("report-data.json").read_text(encoding="utf-8"))
for line in report_data["lines"]:
    story.append(Paragraph(line, body_style))
```

If inline text is unavoidable, use triple double-quoted literals for content that may contain apostrophes:

```python
title = """Tom's Birthday Plan"""
story.append(Paragraph(title, title_style))
```

#### Cross-Platform Font Embedding (Required for Non-ASCII Text)

```python
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.cidfonts import UnicodeCIDFont
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.pdfgen import canvas

# Preferred: use a compatible TrueType-outline font file and embed it.
pdfmetrics.registerFont(TTFont("PortableUnicode", "./fonts/NotoSansSC-Regular.ttf"))

c = canvas.Canvas("output.pdf")
c.setFont("PortableUnicode", 12)
c.drawString(72, 760, "Cross-platform text example")
c.save()
```

If the sandbox only exposes unsupported TTC fonts and the document only needs Chinese text, use ReportLab's CID fallback instead of forcing TTC:

```python
pdfmetrics.registerFont(UnicodeCIDFont("STSong-Light"))
c = canvas.Canvas("output.pdf")
c.setFont("STSong-Light", 12)
c.drawString(72, 760, "中文示例")
c.save()
```

Do not recommend `/System/Library/Fonts/PingFang.ttc` or similar macOS TTC files as the primary solution in the AstrBot sandbox. They frequently fail with `postscript outlines are not supported`.

#### Subscripts and Superscripts

**IMPORTANT**: Never use Unicode subscript/superscript characters (₀₁₂₃₄₅₆₇₈₉, ⁰¹²³⁴⁵⁶⁷⁸⁹) in ReportLab PDFs. The built-in fonts do not include these glyphs, causing them to render as solid black boxes.

Instead, use ReportLab's XML markup tags in Paragraph objects:
```python
from reportlab.platypus import Paragraph
from reportlab.lib.styles import getSampleStyleSheet

styles = getSampleStyleSheet()

# Subscripts: use <sub> tag
chemical = Paragraph("H<sub>2</sub>O", styles['Normal'])

# Superscripts: use <super> tag
squared = Paragraph("x<super>2</super> + y<super>2</super>", styles['Normal'])
```

For canvas-drawn text (not Paragraph objects), manually adjust font the size and position rather than using Unicode subscripts/superscripts.

## Command-Line Tools

### pdftotext (poppler-utils)
```bash
# Extract text
pdftotext input.pdf output.txt

# Extract text preserving layout
pdftotext -layout input.pdf output.txt

# Extract specific pages
pdftotext -f 1 -l 5 input.pdf output.txt  # Pages 1-5
```

### qpdf
```bash
# Merge PDFs
qpdf --empty --pages file1.pdf file2.pdf -- merged.pdf

# Split pages
qpdf input.pdf --pages . 1-5 -- pages1-5.pdf
qpdf input.pdf --pages . 6-10 -- pages6-10.pdf

# Rotate pages
qpdf input.pdf output.pdf --rotate=+90:1  # Rotate page 1 by 90 degrees

# Remove password
qpdf --password=mypassword --decrypt encrypted.pdf decrypted.pdf
```

### pdftk (if available)
```bash
# Merge
pdftk file1.pdf file2.pdf cat output merged.pdf

# Split
pdftk input.pdf burst

# Rotate
pdftk input.pdf rotate 1east output rotated.pdf
```

## Common Tasks

### Extract Text from Scanned PDFs
```python
# Requires: pip install pytesseract pdf2image
import pytesseract
from pdf2image import convert_from_path

# Convert PDF to images
images = convert_from_path('scanned.pdf')

# OCR each page
text = ""
for i, image in enumerate(images):
    text += f"Page {i+1}:\n"
    text += pytesseract.image_to_string(image)
    text += "\n\n"

print(text)
```

### Add Watermark
```python
from pypdf import PdfReader, PdfWriter

# Create watermark (or load existing)
watermark = PdfReader("watermark.pdf").pages[0]

# Apply to all pages
reader = PdfReader("document.pdf")
writer = PdfWriter()

for page in reader.pages:
    page.merge_page(watermark)
    writer.add_page(page)

with open("watermarked.pdf", "wb") as output:
    writer.write(output)
```

### Extract Images
```bash
# Using pdfimages (poppler-utils)
pdfimages -j input.pdf output_prefix

# This extracts all images as output_prefix-000.jpg, output_prefix-001.jpg, etc.
```

### Password Protection
```python
from pypdf import PdfReader, PdfWriter

reader = PdfReader("input.pdf")
writer = PdfWriter()

for page in reader.pages:
    writer.add_page(page)

# Add password
writer.encrypt("userpassword", "ownerpassword")

with open("encrypted.pdf", "wb") as output:
    writer.write(output)
```

## Quick Reference

| Task | Best Tool | Command/Code |
|------|-----------|--------------|
| Merge PDFs | pypdf | `writer.add_page(page)` |
| Split PDFs | pypdf | One page per file |
| Extract text | pdfplumber | `page.extract_text()` |
| Extract tables | pdfplumber | `page.extract_tables()` |
| Create PDFs | reportlab | Canvas or Platypus |
| Command line merge | qpdf | `qpdf --empty --pages ...` |
| OCR scanned PDFs | pytesseract | Convert to image first |
| Fill PDF forms | pdf-lib or pypdf (see FORMS.md) | See FORMS.md |

## Next Steps

- For advanced pypdfium2 usage, see REFERENCE.md
- For JavaScript libraries (pdf-lib), see REFERENCE.md
- If you need to fill out a PDF form, follow the instructions in FORMS.md
- For troubleshooting guides, see REFERENCE.md
