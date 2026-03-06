# Parser Usage Guide

This guide explains how to use the `casely_parser.py` script provided with the Casely skill.

## Overview

The parser uses the `docling` library to convert various document formats into Markdown. This allows the LLM to easily analyze requirements and test case examples.

## Supported Formats

- Documents: PDF, DOCX, PPTX, XLSX, HTML, HTM, TXT, MD
- Images: PNG, JPG, JPEG, TIFF

## Command Line Interface (CLI)

You can run the parser directly from the terminal:

```bash
python scripts/casely_parser.py <input_dir> <output_dir>
```

- `input_dir`: Path to the folder containing your source documents.
- `output_dir`: Path where the converted Markdown files will be saved.

## Programmatic Usage

You can also import and use the `DocumentParser` class in your Python scripts:

```python
from casely_parser import DocumentParser

# Initialize the parser
parser = DocumentParser()

# Parse a specific folder
result = parser.parse_folder("projects/MyProject/input/requirements", "projects/MyProject/processed")

# Access results
print(f"Processed {result.processed} new files.")
```

## Naming Convention

Processed files are saved in the output directory with the prefix `_parsed_` and the `.md` extension.
Example: `Requirement.pdf` becomes `_parsed_Requirement.md`.
