#!/usr/bin/env python3
"""Extract tables from a document using Docling."""

import argparse
import sys
from pathlib import Path


def extract_tables(
    input_path: str,
    output_dir: str,
    output_format: str = "csv",
    use_ocr: bool = False,
):
    """Extract tables from a document.

    Args:
        input_path: Path to input file or URL
        output_dir: Directory for output files
        output_format: Output format (csv, xlsx)
        use_ocr: Enable OCR for scanned documents
    """
    from docling.document_converter import DocumentConverter

    # Configure converter
    converter_kwargs = {}
    if use_ocr:
        from docling.datamodel.pipeline_options import PipelineOptions
        from docling.datamodel.document import InputFormat
        from docling.document_converter import PdfFormatOption

        pipeline_options = PipelineOptions()
        pipeline_options.do_ocr = True
        converter_kwargs["format_options"] = {
            InputFormat.PDF: PdfFormatOption(pipeline_options=pipeline_options)
        }

    # Convert document
    converter = DocumentConverter(**converter_kwargs)

    print(f"Processing: {input_path}")
    result = converter.convert(input_path)
    doc = result.document

    # Create output directory
    output_path = Path(output_dir)
    output_path.mkdir(parents=True, exist_ok=True)

    # Extract tables
    tables = list(doc.tables)
    if not tables:
        print("No tables found in document.")
        return []

    print(f"Found {len(tables)} table(s)")

    input_stem = Path(input_path).stem if not input_path.startswith("http") else "document"
    output_files = []

    if output_format == "xlsx":
        # All tables in one Excel file
        import pandas as pd

        xlsx_path = output_path / f"{input_stem}_tables.xlsx"
        with pd.ExcelWriter(xlsx_path, engine="openpyxl") as writer:
            for i, table in enumerate(tables):
                df = table.export_to_dataframe()
                sheet_name = f"Table_{i + 1}"
                df.to_excel(writer, sheet_name=sheet_name, index=False)
                print(f"  Table {i + 1}: {df.shape[0]} rows x {df.shape[1]} cols -> {sheet_name}")

        output_files.append(str(xlsx_path))
        print(f"\nSaved to: {xlsx_path}")

    else:  # csv
        for i, table in enumerate(tables):
            df = table.export_to_dataframe()
            csv_path = output_path / f"{input_stem}_table_{i + 1}.csv"
            df.to_csv(csv_path, index=False)
            output_files.append(str(csv_path))
            print(f"  Table {i + 1}: {df.shape[0]} rows x {df.shape[1]} cols -> {csv_path.name}")

        print(f"\nSaved {len(output_files)} CSV file(s) to: {output_dir}")

    return output_files


def main():
    parser = argparse.ArgumentParser(
        description="Extract tables from document using Docling",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s document.pdf tables/
  %(prog)s document.pdf tables/ --format xlsx
  %(prog)s scanned.pdf tables/ --ocr
        """,
    )
    parser.add_argument("input", help="Input file path or URL")
    parser.add_argument("output_dir", help="Output directory for tables")
    parser.add_argument(
        "--format",
        choices=["csv", "xlsx"],
        default="csv",
        help="Output format (default: csv)",
    )
    parser.add_argument(
        "--ocr",
        action="store_true",
        help="Enable OCR for scanned documents",
    )

    args = parser.parse_args()

    try:
        extract_tables(args.input, args.output_dir, args.format, args.ocr)
    except ImportError as e:
        if "openpyxl" in str(e):
            print("Error: xlsx format requires openpyxl. Install with: pip install openpyxl", file=sys.stderr)
        else:
            print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
