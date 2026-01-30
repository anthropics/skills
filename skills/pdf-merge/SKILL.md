---
name: pdf-merge
description: Merges multiple PDF documents into a single file.
license: Proprietary. LICENSE.txt has complete terms
---

# PDF Merging Guide

## Overview

This skill merges two or more PDF files into a single PDF document. It uses the `pypdf` library to combine the pages from the input files in the order they are provided.

## Usage

To merge PDFs, you will need to provide a list of input PDF files and specify an output file name.

### Example

Here is an example of how to merge `doc1.pdf` and `doc2.pdf` into `merged.pdf`.

```python
from pypdf import PdfWriter, PdfReader

# List of input PDF files to merge
pdf_files = ["doc1.pdf", "doc2.pdf"]
output_pdf = "merged.pdf"

writer = PdfWriter()

for pdf_file in pdf_files:
    reader = PdfReader(pdf_file)
    for page in reader.pages:
        writer.add_page(page)

with open(output_pdf, "wb") as output:
    writer.write(output)

print(f"Successfully merged {len(pdf_files)} PDF files into {output_pdf}")
```

## Inputs

- A list of 2 or more PDF files to merge.

## Outputs

- A single merged PDF file.
