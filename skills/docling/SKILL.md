---
name: docling
description: "Universal document conversion and parsing using Docling. Converts PDF, DOCX, PPTX, XLSX, HTML, images, and audio files to Markdown, HTML, or JSON with advanced table extraction, OCR support, and Vision Language Model capabilities. Use when Claude needs to: (1) Convert documents to Markdown/HTML/JSON, (2) Extract tables from PDFs or other documents, (3) Process scanned documents with OCR, (4) Prepare documents for RAG pipelines (LangChain, LlamaIndex, Haystack), (5) Use VLM-based document understanding with GraniteDocling, or (6) Batch convert multiple documents."
license: MIT
---

# Docling Document Processing Guide

## Overview

Docling is a universal document parser that converts various file formats into structured output. It excels at:

- **Layout-aware PDF parsing**: Reading order, table structure, figures, formulas
- **Multi-format support**: PDF, DOCX, PPTX, XLSX, HTML, images (PNG, JPEG, TIFF), audio (WAV, MP3)
- **Unified output**: DoclingDocument format exports to Markdown, HTML, JSON
- **OCR integration**: Tesseract, EasyOCR, RapidOCR for scanned documents
- **VLM pipeline**: GraniteDocling Vision Language Model for complex layouts
- **RAG-ready**: Built-in integrations with LangChain, LlamaIndex, Haystack

**When to use Docling vs other tools:**
- Use Docling for: Complex layouts, multi-format conversion, RAG pipelines, scanned docs
- Use pdfplumber for: Simple PDF text/table extraction when Docling overhead is unnecessary
- Use pypdf for: Basic PDF manipulation (merge, split, rotate)
- Use pandoc for: Simple format conversion without layout analysis

For advanced topics see:
- [OCR Configuration](references/ocr-configuration.md) - OCR engine setup
- [VLM Pipelines](references/vlm-pipelines.md) - Vision Language Model usage
- [RAG Integrations](references/rag-integrations.md) - Framework integration patterns
- [Advanced Options](references/advanced-options.md) - Export formats, chunking, document model

## Quick Start

### Installation

```bash
# Basic installation
pip install docling

# With OCR support
pip install "docling[tesserocr]"  # or easyocr, rapidocr

# With VLM support
pip install "docling[vlm]"

# With audio support (ASR)
pip install "docling[asr]"

# Full installation
pip install "docling[tesserocr,vlm,asr]"
```

### Basic Usage (Python)

```python
from docling.document_converter import DocumentConverter

# Convert a document
converter = DocumentConverter()
result = converter.convert("document.pdf")
doc = result.document

# Export to Markdown
markdown = doc.export_to_markdown()
print(markdown)

# Export to other formats
html = doc.export_to_html()
json_dict = doc.export_to_dict()
json_str = doc.model_dump_json(indent=2)
```

### Basic Usage (CLI)

```bash
# Convert to Markdown (default)
docling document.pdf

# Convert to specific format
docling document.pdf --output-format md
docling document.pdf --output-format json
docling document.pdf --output-format html

# Convert from URL
docling https://arxiv.org/pdf/2408.09869
```

## Common Workflows

### Convert Single Document

**Python:**
```python
from docling.document_converter import DocumentConverter
from pathlib import Path

converter = DocumentConverter()
result = converter.convert("report.pdf")

# Save as Markdown
Path("report.md").write_text(result.document.export_to_markdown())
```

**CLI:**
```bash
docling report.pdf -o output_dir/
```

**Script:** Use `scripts/convert_document.py` for a ready-to-run converter.

### Convert from URL

```python
from docling.document_converter import DocumentConverter

converter = DocumentConverter()
result = converter.convert("https://example.com/document.pdf")
print(result.document.export_to_markdown())
```

### Extract Tables

```python
from docling.document_converter import DocumentConverter
import pandas as pd

converter = DocumentConverter()
result = converter.convert("document.pdf")

# Access tables from the document
for i, table in enumerate(result.document.tables):
    # Export table to pandas DataFrame
    df = table.export_to_dataframe()
    df.to_csv(f"table_{i}.csv", index=False)
    print(f"Table {i}: {df.shape[0]} rows x {df.shape[1]} cols")
```

**Script:** Use `scripts/extract_tables.py` for batch table extraction.

### Batch Conversion

```python
from docling.document_converter import DocumentConverter
from pathlib import Path

converter = DocumentConverter()
input_dir = Path("documents/")
output_dir = Path("converted/")
output_dir.mkdir(exist_ok=True)

for doc_path in input_dir.glob("*.pdf"):
    result = converter.convert(str(doc_path))
    output_path = output_dir / f"{doc_path.stem}.md"
    output_path.write_text(result.document.export_to_markdown())
    print(f"Converted: {doc_path.name}")
```

**Script:** Use `scripts/batch_convert.py` for parallel batch processing.

### OCR for Scanned Documents

```python
from docling.document_converter import DocumentConverter
from docling.datamodel.pipeline_options import PipelineOptions
from docling.datamodel.document import InputFormat

# Configure OCR
pipeline_options = PipelineOptions()
pipeline_options.do_ocr = True

converter = DocumentConverter(
    format_options={
        InputFormat.PDF: {"pipeline_options": pipeline_options}
    }
)

result = converter.convert("scanned_document.pdf")
print(result.document.export_to_markdown())
```

**CLI with OCR:**
```bash
docling scanned_document.pdf --ocr
```

For detailed OCR configuration (engine selection, languages), see [ocr-configuration.md](references/ocr-configuration.md).

**Script:** Use `scripts/check_ocr_engines.py` to verify which OCR engines are available.

### VLM Pipeline (GraniteDocling)

For complex documents with intricate layouts, use the Vision Language Model pipeline:

**CLI:**
```bash
docling --pipeline vlm --vlm-model granite_docling document.pdf
```

**Python:**
```python
from docling.document_converter import DocumentConverter, PdfFormatOption
from docling.datamodel.pipeline_options import VlmPipelineOptions
from docling.datamodel.document import InputFormat

vlm_options = VlmPipelineOptions(
    model_name="granite_docling"
)

converter = DocumentConverter(
    format_options={
        InputFormat.PDF: PdfFormatOption(pipeline_options=vlm_options)
    }
)

result = converter.convert("complex_document.pdf")
```

For VLM configuration (GPU, MLX acceleration), see [vlm-pipelines.md](references/vlm-pipelines.md).

## Export Formats

### Markdown

```python
markdown = doc.export_to_markdown()
# Options: image_mode, table_mode, etc.
markdown = doc.export_to_markdown(image_mode="embedded")
```

### HTML

```python
html = doc.export_to_html()
```

### JSON

```python
# As Python dict
data = doc.export_to_dict()

# As JSON string
json_str = doc.model_dump_json(indent=2)

# Save to file
import json
with open("output.json", "w") as f:
    json.dump(doc.export_to_dict(), f, indent=2)
```

### DocTags (for LLM training)

```python
doctags = doc.export_to_document_tokens()
```

## RAG Integration Quick Reference

### LangChain

```python
from langchain_community.document_loaders import DoclingLoader

loader = DoclingLoader(file_path="document.pdf")
docs = loader.load()

# Use with any LangChain chain
from langchain.text_splitter import RecursiveCharacterTextSplitter
splitter = RecursiveCharacterTextSplitter(chunk_size=1000, chunk_overlap=200)
chunks = splitter.split_documents(docs)
```

### LlamaIndex

```python
from llama_index.readers.docling import DoclingReader

reader = DoclingReader()
documents = reader.load_data(file_path="document.pdf")

# Build index
from llama_index.core import VectorStoreIndex
index = VectorStoreIndex.from_documents(documents)
```

### Haystack

```python
from haystack_integrations.components.converters.docling import DoclingConverter

converter = DoclingConverter()
docs = converter.run(sources=["document.pdf"])
```

For complete RAG examples with vector stores, see [rag-integrations.md](references/rag-integrations.md).

**Script:** Use `scripts/prepare_rag_chunks.py` to prepare documents for RAG ingestion.

## CLI Reference

```bash
docling [OPTIONS] SOURCE

Arguments:
  SOURCE          File path or URL to convert

Options:
  -o, --output    Output directory (default: current directory)
  --output-format Format: md, json, html, doctags (default: md)
  --pipeline      Pipeline: standard, vlm (default: standard)
  --vlm-model     VLM model name (default: granite_docling)
  --ocr           Enable OCR for scanned documents
  --no-ocr        Disable OCR
  --ocr-lang      OCR languages (comma-separated, e.g., "eng,deu")
  --pages         Page range (e.g., "1-5" or "1,3,5")
  --help          Show help message
```

### Common CLI Examples

```bash
# Convert PDF to Markdown
docling report.pdf -o output/

# Convert with OCR enabled
docling scanned.pdf --ocr --ocr-lang eng,fra

# Convert specific pages
docling large_doc.pdf --pages 1-10

# Use VLM for complex layouts
docling complex.pdf --pipeline vlm --vlm-model granite_docling

# Convert URL
docling https://arxiv.org/pdf/2408.09869

# Output as JSON
docling document.pdf --output-format json
```

## Supported Formats

| Input Format | Extensions | Notes |
|--------------|------------|-------|
| PDF | .pdf | Native + scanned with OCR |
| Word | .docx | Office Open XML |
| PowerPoint | .pptx | Office Open XML |
| Excel | .xlsx | Office Open XML |
| HTML | .html, .htm | Web pages |
| Images | .png, .jpg, .jpeg, .tiff | OCR extraction |
| Audio | .wav, .mp3 | Requires ASR extra |

| Output Format | Method | Use Case |
|---------------|--------|----------|
| Markdown | `export_to_markdown()` | Documentation, RAG |
| HTML | `export_to_html()` | Web display |
| JSON | `export_to_dict()` | Structured data, APIs |
| DocTags | `export_to_document_tokens()` | LLM training |

## Installation Notes

### System Dependencies

**For Tesseract OCR:**
```bash
# macOS
brew install tesseract tesseract-lang

# Ubuntu/Debian
sudo apt-get install tesseract-ocr tesseract-ocr-eng

# Set TESSDATA_PREFIX if needed
export TESSDATA_PREFIX=/usr/share/tesseract-ocr/4.00/tessdata/
```

**For poppler (PDF rendering):**
```bash
# macOS
brew install poppler

# Ubuntu/Debian
sudo apt-get install poppler-utils
```

### Optional Extras

```bash
# OCR engines (choose one or more)
pip install "docling[tesserocr]"    # Tesseract (needs system install)
pip install "docling[easyocr]"      # EasyOCR (pure Python, easiest)
pip install "docling[rapidocr]"     # RapidOCR (CPU-optimized)

# Vision Language Model
pip install "docling[vlm]"

# Audio/Speech Recognition
pip install "docling[asr]"

# All extras
pip install "docling[tesserocr,easyocr,vlm,asr]"
```

### Apple Silicon (M1/M2/M3)

For MLX acceleration with VLM:
```bash
pip install "docling[vlm]"
# MLX backend is automatically used on Apple Silicon
```

## Scripts Reference

| Script | Purpose | Usage |
|--------|---------|-------|
| `convert_document.py` | Convert single document | `python scripts/convert_document.py input.pdf output.md` |
| `batch_convert.py` | Batch convert directory | `python scripts/batch_convert.py input_dir/ output_dir/` |
| `extract_tables.py` | Extract tables to CSV/Excel | `python scripts/extract_tables.py input.pdf tables/` |
| `check_ocr_engines.py` | Check OCR availability | `python scripts/check_ocr_engines.py` |
| `prepare_rag_chunks.py` | Prepare for RAG | `python scripts/prepare_rag_chunks.py input.pdf chunks.json` |

## Next Steps

- For OCR engine setup and configuration: [ocr-configuration.md](references/ocr-configuration.md)
- For VLM pipeline details: [vlm-pipelines.md](references/vlm-pipelines.md)
- For RAG framework integrations: [rag-integrations.md](references/rag-integrations.md)
- For advanced export options and document model: [advanced-options.md](references/advanced-options.md)
