# Export Guide: Markdown to Excel

This guide describes how Casely converts generated Markdown test cases into formatted Excel files for TMS import.

## Overview

The `export_to_xlsx.py` script parses Markdown tables and recreates them in an Excel workbook using the `openpyxl` library.

## Features

- **Column Mapping:** Automatically maps Markdown headers to Excel columns.
- **Formatting:** Applies bold fonts and background fills to headers.
- **Auto-Width:** Calculates appropriate column widths based on content.
- **Multi-line Support:** Correctly handles line breaks (`<br>` or `\n`) within cells.
- **Styling:** Adds borders and alternating row colors for readability.

## Usage

Run the script from the command line:

```bash
python scripts/export_to_xlsx.py <results_dir> <output_dir>
```

- `results_dir`: Directory containing the `.md` files to export.
- `output_dir`: Directory where the `.xlsx` files will be created (one per Markdown file).

If you omit both arguments, the script will:

- Automatically detect the most recently modified project under `projects/`
- Use its `results/` folder as the source and `exports/` as the output directory

## Handling Special Characters

The script cleans worksheet names by removing illegal characters (like `\ / * ? [ ] :`) to ensure Excel compatibility.
