---
name: pdf-split
description: Splits a PDF document into multiple files, with each file containing a single page.
license: Proprietary. LICENSE.txt has complete terms
---

# PDF Splitting Guide

## Overview

This skill splits a PDF document into multiple files, where each file contains one page from the original document. It uses the `pypdf` library to perform the splitting operation.

## Usage

To split a PDF, you will need to provide the input PDF file. The skill will create new PDF files named `page_1.pdf`, `page_2.pdf`, and so on, in the current directory.

### Example

Here is an example of how to split `input.pdf`.

```python
from pypdf import PdfReader, PdfWriter

input_pdf = "input.pdf"

reader = PdfReader(input_pdf)
for i, page in enumerate(reader.pages):
    writer = PdfWriter()
    writer.add_page(page)
    output_filename = f"page_{i+1}.pdf"
    with open(output_filename, "wb") as output:
        writer.write(output)
    print(f"Created {output_filename}")

print(f"Successfully split {input_pdf} into {len(reader.pages)} pages.")
```

## Inputs

- A single PDF file to split.

## Outputs

- Multiple PDF files, each containing a single page from the input PDF.
