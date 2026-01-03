# Advanced Options Guide

This guide covers advanced Docling features including the document model, export options, chunking strategies, and audio processing.

## DoclingDocument Model

The `DoclingDocument` is Docling's unified document representation.

### Structure

```python
from docling.document_converter import DocumentConverter

result = converter.convert("document.pdf")
doc = result.document

# Document properties
doc.name           # Source filename
doc.origin         # Original source path/URL
doc.num_pages      # Number of pages (if applicable)

# Content elements
doc.texts          # Text elements
doc.tables         # Table elements
doc.pictures       # Image/figure elements
doc.key_value_items # Key-value pairs (forms)
```

### Accessing Elements

```python
# Iterate through text elements
for text in doc.texts:
    print(f"Text: {text.text[:100]}...")
    print(f"  Page: {text.prov[0].page_no if text.prov else 'N/A'}")

# Iterate through tables
for i, table in enumerate(doc.tables):
    df = table.export_to_dataframe()
    print(f"Table {i}: {df.shape}")

# Iterate through figures
for picture in doc.pictures:
    print(f"Figure: {picture.caption}")
```

### Confidence Scores

Some elements include confidence scores from AI models:

```python
for text in doc.texts:
    if hasattr(text, 'confidence'):
        print(f"Confidence: {text.confidence}")
```

## Export Options

### Markdown Export

```python
# Basic export
markdown = doc.export_to_markdown()

# With options
markdown = doc.export_to_markdown(
    image_mode="embedded",  # "embedded", "referenced", or "placeholder"
    strict_text=False,      # Preserve original formatting
)
```

### HTML Export

```python
html = doc.export_to_html()

# Save with proper encoding
with open("output.html", "w", encoding="utf-8") as f:
    f.write(html)
```

### JSON Export

```python
# As Python dict
data = doc.export_to_dict()

# As JSON string (pretty printed)
json_str = doc.model_dump_json(indent=2)

# As JSON string (compact)
json_str = doc.model_dump_json()

# Save to file
import json
with open("output.json", "w") as f:
    json.dump(doc.export_to_dict(), f, indent=2, ensure_ascii=False)
```

### DocTags Export (for LLM training)

```python
# Document tokens format
doctags = doc.export_to_document_tokens()
```

## Chunking Strategies

### Basic Chunking

```python
def simple_chunk(text: str, chunk_size: int = 1000) -> list[str]:
    """Split text into fixed-size chunks."""
    return [text[i:i+chunk_size] for i in range(0, len(text), chunk_size)]

markdown = doc.export_to_markdown()
chunks = simple_chunk(markdown, 1000)
```

### Overlapping Chunks

```python
def overlap_chunk(text: str, chunk_size: int = 1000, overlap: int = 100) -> list[str]:
    """Split text into overlapping chunks."""
    chunks = []
    start = 0
    while start < len(text):
        end = start + chunk_size
        chunks.append(text[start:end])
        start = end - overlap
    return chunks
```

### Sentence-Aware Chunking

```python
import re

def sentence_chunk(text: str, max_chunk_size: int = 1000) -> list[str]:
    """Split text at sentence boundaries."""
    sentences = re.split(r'(?<=[.!?])\s+', text)

    chunks = []
    current_chunk = []
    current_size = 0

    for sentence in sentences:
        if current_size + len(sentence) > max_chunk_size and current_chunk:
            chunks.append(' '.join(current_chunk))
            current_chunk = []
            current_size = 0
        current_chunk.append(sentence)
        current_size += len(sentence) + 1

    if current_chunk:
        chunks.append(' '.join(current_chunk))

    return chunks
```

### Semantic Chunking (with embeddings)

```python
from sentence_transformers import SentenceTransformer
import numpy as np

def semantic_chunk(text: str, max_chunk_size: int = 1000, similarity_threshold: float = 0.5):
    """Split text based on semantic similarity."""
    model = SentenceTransformer('all-MiniLM-L6-v2')

    # Split into paragraphs
    paragraphs = text.split('\n\n')

    # Get embeddings
    embeddings = model.encode(paragraphs)

    chunks = []
    current_chunk = [paragraphs[0]]

    for i in range(1, len(paragraphs)):
        similarity = np.dot(embeddings[i], embeddings[i-1])

        if similarity < similarity_threshold or sum(len(p) for p in current_chunk) > max_chunk_size:
            chunks.append('\n\n'.join(current_chunk))
            current_chunk = []

        current_chunk.append(paragraphs[i])

    if current_chunk:
        chunks.append('\n\n'.join(current_chunk))

    return chunks
```

## Pipeline Customization

### Custom Pipeline Options

```python
from docling.document_converter import DocumentConverter, PdfFormatOption
from docling.datamodel.pipeline_options import PipelineOptions
from docling.datamodel.document import InputFormat

pipeline_options = PipelineOptions()

# OCR settings
pipeline_options.do_ocr = True
pipeline_options.ocr_options.engine = "tesseract"
pipeline_options.ocr_options.lang = ["eng"]

# Table detection settings
pipeline_options.do_table_structure = True

# Figure extraction
pipeline_options.generate_picture_images = True

converter = DocumentConverter(
    format_options={
        InputFormat.PDF: PdfFormatOption(pipeline_options=pipeline_options)
    }
)
```

### Processing Multiple Formats

```python
from docling.datamodel.document import InputFormat

converter = DocumentConverter(
    format_options={
        InputFormat.PDF: PdfFormatOption(pipeline_options=pdf_options),
        InputFormat.DOCX: DocxFormatOption(),
        InputFormat.PPTX: PptxFormatOption(),
    }
)
```

## Audio Processing (ASR)

Docling supports audio transcription via Automatic Speech Recognition.

### Installation

```bash
pip install "docling[asr]"
```

### Usage

```python
from docling.document_converter import DocumentConverter

converter = DocumentConverter()
result = converter.convert("recording.wav")
transcript = result.document.export_to_markdown()
```

### Supported Audio Formats

- WAV
- MP3
- VTT (subtitles)

### Configuration

```python
from docling.datamodel.pipeline_options import AsrPipelineOptions

asr_options = AsrPipelineOptions(
    model_name="whisper-base",  # or larger models
    language="en",
)
```

## Batch Processing Patterns

### Sequential with Progress

```python
from pathlib import Path
from tqdm import tqdm

converter = DocumentConverter()
files = list(Path("documents/").glob("*.pdf"))

for file in tqdm(files, desc="Converting"):
    result = converter.convert(str(file))
    output = Path("output") / f"{file.stem}.md"
    output.write_text(result.document.export_to_markdown())
```

### Parallel Processing

```python
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path

def convert_file(file_path: str) -> tuple[str, bool]:
    from docling.document_converter import DocumentConverter
    try:
        converter = DocumentConverter()
        result = converter.convert(file_path)
        output = Path("output") / f"{Path(file_path).stem}.md"
        output.write_text(result.document.export_to_markdown())
        return file_path, True
    except Exception as e:
        return file_path, False

files = [str(f) for f in Path("documents/").glob("*.pdf")]

with ProcessPoolExecutor(max_workers=4) as executor:
    results = list(executor.map(convert_file, files))

success = sum(1 for _, ok in results if ok)
print(f"Converted {success}/{len(files)} files")
```

### Error Handling

```python
from docling.document_converter import DocumentConverter, ConversionError

converter = DocumentConverter()

try:
    result = converter.convert("document.pdf")
except ConversionError as e:
    print(f"Conversion failed: {e}")
except FileNotFoundError:
    print("File not found")
except Exception as e:
    print(f"Unexpected error: {e}")
```

## Memory Management

For large documents or batch processing:

```python
import gc

converter = DocumentConverter()

for file in files:
    result = converter.convert(str(file))
    # Process result...

    # Clear memory
    del result
    gc.collect()
```

## Debugging

### Verbose Output

```python
import logging

logging.basicConfig(level=logging.DEBUG)
logger = logging.getLogger("docling")
logger.setLevel(logging.DEBUG)

converter = DocumentConverter()
result = converter.convert("document.pdf")
```

### Inspect Conversion Result

```python
result = converter.convert("document.pdf")

print(f"Status: {result.status}")
print(f"Errors: {result.errors}")
print(f"Document: {result.document}")
print(f"Pages: {result.document.num_pages}")
```
