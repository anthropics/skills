#!/usr/bin/env python3
"""Convert a document to Markdown, HTML, or JSON using Docling."""

import argparse
import sys
from pathlib import Path


def convert_document(
    input_path: str,
    output_path: str,
    output_format: str = "md",
    use_ocr: bool = False,
    use_vlm: bool = False,
    vlm_model: str = "granite_docling",
):
    """Convert a document using Docling.

    Args:
        input_path: Path to input file or URL
        output_path: Path for output file
        output_format: Output format (md, html, json)
        use_ocr: Enable OCR for scanned documents
        use_vlm: Use VLM pipeline for complex layouts
        vlm_model: VLM model name (default: granite_docling)
    """
    from docling.document_converter import DocumentConverter

    # Configure converter based on options
    converter_kwargs = {}

    if use_vlm:
        from docling.datamodel.pipeline_options import VlmPipelineOptions
        from docling.datamodel.document import InputFormat
        from docling.document_converter import PdfFormatOption

        vlm_options = VlmPipelineOptions(model_name=vlm_model)
        converter_kwargs["format_options"] = {
            InputFormat.PDF: PdfFormatOption(pipeline_options=vlm_options)
        }
    elif use_ocr:
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

    print(f"Converting: {input_path}")
    result = converter.convert(input_path)
    doc = result.document

    # Export based on format
    if output_format == "md":
        content = doc.export_to_markdown()
    elif output_format == "html":
        content = doc.export_to_html()
    elif output_format == "json":
        content = doc.model_dump_json(indent=2)
    else:
        raise ValueError(f"Unknown format: {output_format}")

    # Write output
    Path(output_path).write_text(content)
    print(f"Output: {output_path}")

    return output_path


def main():
    parser = argparse.ArgumentParser(
        description="Convert document to Markdown/HTML/JSON using Docling",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s document.pdf output.md
  %(prog)s document.pdf output.html --format html
  %(prog)s scanned.pdf output.md --ocr
  %(prog)s complex.pdf output.md --vlm
  %(prog)s https://example.com/doc.pdf output.md
        """,
    )
    parser.add_argument("input", help="Input file path or URL")
    parser.add_argument("output", help="Output file path")
    parser.add_argument(
        "--format",
        choices=["md", "html", "json"],
        default="md",
        help="Output format (default: md)",
    )
    parser.add_argument(
        "--ocr",
        action="store_true",
        help="Enable OCR for scanned documents",
    )
    parser.add_argument(
        "--vlm",
        action="store_true",
        help="Use VLM pipeline for complex layouts",
    )
    parser.add_argument(
        "--vlm-model",
        default="granite_docling",
        help="VLM model name (default: granite_docling)",
    )

    args = parser.parse_args()

    if args.ocr and args.vlm:
        print("Error: Cannot use both --ocr and --vlm. Choose one.", file=sys.stderr)
        sys.exit(1)

    try:
        convert_document(
            args.input,
            args.output,
            args.format,
            args.ocr,
            args.vlm,
            args.vlm_model,
        )
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
