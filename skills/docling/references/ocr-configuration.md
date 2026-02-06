# OCR Configuration Guide

This guide covers OCR engine setup and configuration for processing scanned documents with Docling.

## Available OCR Engines

| Engine | Installation | Pros | Cons |
|--------|--------------|------|------|
| EasyOCR | Pure Python | Easiest setup, good accuracy | Slower, larger models |
| Tesseract | System + Python | Fast, widely supported | Requires system install |
| RapidOCR | Pure Python | CPU-optimized, fast | Less language support |
| OcrMac | macOS only | Native performance | macOS only |

## Quick Setup

### EasyOCR (Recommended for beginners)

```bash
pip install "docling[easyocr]"
```

No system dependencies required. Models download automatically on first use.

### Tesseract

**1. Install system binary:**

```bash
# macOS
brew install tesseract tesseract-lang

# Ubuntu/Debian
sudo apt-get install tesseract-ocr tesseract-ocr-eng tesseract-ocr-deu

# Fedora
sudo dnf install tesseract tesseract-langpack-eng

# Windows (via chocolatey)
choco install tesseract
```

**2. Install Python binding:**

```bash
pip install "docling[tesserocr]"
```

**3. Set TESSDATA_PREFIX (if needed):**

```bash
# Find tessdata location
tesseract --list-langs 2>&1 | head -1

# Export (add to .bashrc/.zshrc)
export TESSDATA_PREFIX=/usr/share/tesseract-ocr/4.00/tessdata/
```

### RapidOCR

```bash
pip install "docling[rapidocr]"
```

CPU-optimized, no GPU required. Good balance of speed and accuracy.

### OcrMac (macOS only)

```bash
pip install "docling[ocrmac]"
```

Uses macOS native Vision framework. Best performance on Apple Silicon.

## Configuration in Python

### Basic OCR

```python
from docling.document_converter import DocumentConverter, PdfFormatOption
from docling.datamodel.pipeline_options import PipelineOptions
from docling.datamodel.document import InputFormat

# Enable OCR
pipeline_options = PipelineOptions()
pipeline_options.do_ocr = True

converter = DocumentConverter(
    format_options={
        InputFormat.PDF: PdfFormatOption(pipeline_options=pipeline_options)
    }
)

result = converter.convert("scanned_document.pdf")
```

### Specify OCR Engine

```python
from docling.datamodel.pipeline_options import PipelineOptions, OcrOptions

# Use specific engine
pipeline_options = PipelineOptions()
pipeline_options.do_ocr = True
pipeline_options.ocr_options = OcrOptions(
    engine="tesseract"  # or "easyocr", "rapidocr", "ocrmac"
)
```

### Specify Languages

```python
pipeline_options.ocr_options = OcrOptions(
    engine="tesseract",
    lang=["eng", "deu", "fra"]  # English, German, French
)
```

### EasyOCR with GPU

```python
pipeline_options.ocr_options = OcrOptions(
    engine="easyocr",
    lang=["en", "de"],
    gpu=True  # Use GPU if available
)
```

## CLI Configuration

```bash
# Basic OCR
docling --ocr document.pdf

# Specify languages
docling --ocr --ocr-lang eng,deu document.pdf

# Specify engine (if supported by CLI version)
docling --ocr --ocr-engine tesseract document.pdf
```

## Language Codes

### Tesseract Language Codes

| Language | Code | Install |
|----------|------|---------|
| English | eng | Default |
| German | deu | tesseract-ocr-deu |
| French | fra | tesseract-ocr-fra |
| Spanish | spa | tesseract-ocr-spa |
| Italian | ita | tesseract-ocr-ita |
| Chinese (Simplified) | chi_sim | tesseract-ocr-chi-sim |
| Chinese (Traditional) | chi_tra | tesseract-ocr-chi-tra |
| Japanese | jpn | tesseract-ocr-jpn |
| Korean | kor | tesseract-ocr-kor |
| Arabic | ara | tesseract-ocr-ara |

List all installed: `tesseract --list-langs`

### EasyOCR Language Codes

| Language | Code |
|----------|------|
| English | en |
| German | de |
| French | fr |
| Spanish | es |
| Chinese (Simplified) | ch_sim |
| Chinese (Traditional) | ch_tra |
| Japanese | ja |
| Korean | ko |

Full list: https://www.jaided.ai/easyocr/

## Performance Comparison

| Engine | Speed | Accuracy | GPU Support | Languages |
|--------|-------|----------|-------------|-----------|
| Tesseract | Fast | Good | No | 100+ |
| EasyOCR | Medium | Very Good | Yes | 80+ |
| RapidOCR | Fast | Good | No | Limited |
| OcrMac | Fast | Good | N/A (Metal) | System |

## Troubleshooting

### Tesseract not found

```
Error: tesseract is not installed or not in PATH
```

**Solution:** Install tesseract binary and ensure it's in PATH:
```bash
which tesseract  # Should return path
tesseract --version  # Should show version
```

### TESSDATA_PREFIX not set

```
Error: Could not find tessdata
```

**Solution:** Set TESSDATA_PREFIX environment variable:
```bash
export TESSDATA_PREFIX=/usr/share/tesseract-ocr/4.00/tessdata/
```

### Language not available

```
Error: Failed to load language 'xxx'
```

**Solution:** Install the language pack:
```bash
# Ubuntu/Debian
sudo apt-get install tesseract-ocr-xxx

# macOS
brew install tesseract-lang  # Installs all languages
```

### EasyOCR model download fails

**Solution:** Download models manually to `~/.EasyOCR/model/`

### Low OCR accuracy

1. Try a different engine
2. Increase image DPI (300+ recommended)
3. Pre-process image (deskew, denoise)
4. Use VLM pipeline for complex layouts

## Combining with VLM

For complex documents with mixed content, consider using VLM instead of traditional OCR:

```bash
docling --pipeline vlm --vlm-model granite_docling document.pdf
```

VLM provides better understanding of document structure but requires more compute resources.
