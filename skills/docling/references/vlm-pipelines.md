# Vision Language Model (VLM) Pipelines Guide

This guide covers using Vision Language Models with Docling for advanced document understanding.

## Overview

VLM pipelines use vision-language models to understand document structure, making them ideal for:

- Complex layouts with mixed content
- Documents with unusual formatting
- Scientific papers with equations
- Forms and invoices
- Handwritten content mixed with printed text

## When to Use VLM vs Standard Pipeline

| Use Case | Recommended Pipeline |
|----------|---------------------|
| Clean PDF with text | Standard |
| Scanned document (mostly text) | Standard + OCR |
| Complex multi-column layout | VLM |
| Mixed tables/figures/text | VLM |
| Scientific papers | VLM |
| Forms and invoices | VLM |
| Low-quality scans | VLM |

## Installation

```bash
# Install VLM support
pip install "docling[vlm]"

# Full installation with VLM and OCR
pip install "docling[vlm,tesserocr]"
```

## Quick Start

### CLI

```bash
# Basic VLM conversion
docling --pipeline vlm document.pdf

# Specify model
docling --pipeline vlm --vlm-model granite_docling document.pdf
```

### Python

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
print(result.document.export_to_markdown())
```

## Available Models

### GraniteDocling (Recommended)

IBM's document-focused vision-language model.

```python
vlm_options = VlmPipelineOptions(model_name="granite_docling")
```

**Strengths:**
- Optimized for document understanding
- Good table structure recognition
- MLX support for Apple Silicon

## Hardware Requirements

### CPU Only

Works but slow. Expect 1-5 minutes per page depending on complexity.

```python
vlm_options = VlmPipelineOptions(
    model_name="granite_docling",
    device="cpu"
)
```

### GPU (CUDA)

Recommended for production. 5-30 seconds per page.

```python
vlm_options = VlmPipelineOptions(
    model_name="granite_docling",
    device="cuda"
)
```

### Apple Silicon (MLX)

Automatic MLX acceleration on M1/M2/M3 Macs. 10-60 seconds per page.

```python
# MLX is auto-detected on Apple Silicon
vlm_options = VlmPipelineOptions(model_name="granite_docling")
```

## Configuration Options

### Full Configuration Example

```python
from docling.document_converter import DocumentConverter, PdfFormatOption
from docling.datamodel.pipeline_options import VlmPipelineOptions
from docling.datamodel.document import InputFormat

vlm_options = VlmPipelineOptions(
    model_name="granite_docling",
    device="cuda",              # "cpu", "cuda", or "mps"
    batch_size=1,               # Pages to process in parallel
    max_new_tokens=4096,        # Max output tokens per page
)

converter = DocumentConverter(
    format_options={
        InputFormat.PDF: PdfFormatOption(pipeline_options=vlm_options)
    }
)
```

### Memory Management

For large documents or limited VRAM:

```python
vlm_options = VlmPipelineOptions(
    model_name="granite_docling",
    batch_size=1,           # Process one page at a time
    offload_to_cpu=True,    # Offload model weights to CPU when idle
)
```

## Batch Processing with VLM

VLM is compute-intensive. For batch processing:

```python
from docling.document_converter import DocumentConverter, PdfFormatOption
from docling.datamodel.pipeline_options import VlmPipelineOptions
from docling.datamodel.document import InputFormat
from pathlib import Path
from tqdm import tqdm

vlm_options = VlmPipelineOptions(model_name="granite_docling")

converter = DocumentConverter(
    format_options={
        InputFormat.PDF: PdfFormatOption(pipeline_options=vlm_options)
    }
)

files = list(Path("documents/").glob("*.pdf"))

for file in tqdm(files, desc="Converting with VLM"):
    try:
        result = converter.convert(str(file))
        output = Path("output") / f"{file.stem}.md"
        output.write_text(result.document.export_to_markdown())
    except Exception as e:
        print(f"Error processing {file}: {e}")
```

## Combining VLM with OCR

For documents with both complex layouts and scanned content:

```python
from docling.datamodel.pipeline_options import VlmPipelineOptions, OcrOptions

vlm_options = VlmPipelineOptions(
    model_name="granite_docling",
    do_ocr=True,
    ocr_options=OcrOptions(
        engine="tesseract",
        lang=["eng"]
    )
)
```

## Performance Optimization

### 1. Use Appropriate Hardware

| Hardware | Expected Speed | Memory |
|----------|---------------|--------|
| M1/M2/M3 Mac | 10-60s/page | 16GB+ RAM |
| CUDA GPU | 5-30s/page | 8GB+ VRAM |
| CPU only | 1-5min/page | 16GB+ RAM |

### 2. Reduce Page Count

Process only needed pages:

```bash
docling --pipeline vlm --pages 1-10 large_document.pdf
```

### 3. Pre-filter Documents

Use standard pipeline for simple documents, VLM only for complex ones:

```python
def needs_vlm(file_path: str) -> bool:
    """Heuristic to determine if VLM is needed."""
    # Check if document is likely complex
    # (e.g., multi-column, many images, etc.)
    return True  # Implement your logic

converter_standard = DocumentConverter()
converter_vlm = DocumentConverter(
    format_options={
        InputFormat.PDF: PdfFormatOption(
            pipeline_options=VlmPipelineOptions(model_name="granite_docling")
        )
    }
)

for file in files:
    converter = converter_vlm if needs_vlm(str(file)) else converter_standard
    result = converter.convert(str(file))
```

## Troubleshooting

### Out of Memory (OOM)

**Symptom:** Process killed or CUDA out of memory error

**Solutions:**
1. Reduce batch_size to 1
2. Enable CPU offloading
3. Use smaller model
4. Process fewer pages at once

```python
vlm_options = VlmPipelineOptions(
    model_name="granite_docling",
    batch_size=1,
    offload_to_cpu=True,
)
```

### Slow Processing

**Symptom:** Very slow conversion (>5 min/page)

**Solutions:**
1. Ensure GPU is being used: check `device` setting
2. Install CUDA/MLX properly
3. Use standard pipeline for simple documents

### Model Download Fails

**Symptom:** Model download hangs or fails

**Solutions:**
1. Check internet connection
2. Set HF_HOME for custom cache location:
   ```bash
   export HF_HOME=/path/to/cache
   ```
3. Pre-download model:
   ```python
   from huggingface_hub import snapshot_download
   snapshot_download("ibm-granite/granite-vision-docling")
   ```

### Poor Quality Output

**Symptom:** VLM output is worse than expected

**Solutions:**
1. Ensure document image quality is good (300+ DPI)
2. Try different model
3. Check if standard pipeline + OCR works better
4. Report issue with sample document

## Model Comparison

| Model | Size | Speed | Quality | Best For |
|-------|------|-------|---------|----------|
| granite_docling | ~7B | Medium | High | General documents |

## Environment Variables

```bash
# Hugging Face cache location
export HF_HOME=/path/to/cache

# CUDA device selection
export CUDA_VISIBLE_DEVICES=0

# Disable telemetry
export DOCLING_TELEMETRY=false
```

## Complete Example

```python
#!/usr/bin/env python3
"""Convert complex document with VLM pipeline."""

from docling.document_converter import DocumentConverter, PdfFormatOption
from docling.datamodel.pipeline_options import VlmPipelineOptions
from docling.datamodel.document import InputFormat
from pathlib import Path
import sys

def convert_with_vlm(input_path: str, output_path: str):
    """Convert document using VLM pipeline."""

    # Configure VLM
    vlm_options = VlmPipelineOptions(
        model_name="granite_docling",
        batch_size=1,
    )

    # Create converter
    converter = DocumentConverter(
        format_options={
            InputFormat.PDF: PdfFormatOption(pipeline_options=vlm_options)
        }
    )

    # Convert
    print(f"Processing: {input_path}")
    print("This may take several minutes for large documents...")

    result = converter.convert(input_path)

    # Save output
    Path(output_path).write_text(result.document.export_to_markdown())
    print(f"Output: {output_path}")

if __name__ == "__main__":
    if len(sys.argv) != 3:
        print("Usage: python script.py <input.pdf> <output.md>")
        sys.exit(1)

    convert_with_vlm(sys.argv[1], sys.argv[2])
```
