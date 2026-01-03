#!/usr/bin/env python3
"""Batch convert documents using Docling."""

import argparse
import sys
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path


def convert_single(args_tuple):
    """Convert a single document (for multiprocessing)."""
    input_path, output_path, output_format, use_ocr = args_tuple

    from docling.document_converter import DocumentConverter

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

    try:
        converter = DocumentConverter(**converter_kwargs)
        result = converter.convert(str(input_path))
        doc = result.document

        if output_format == "md":
            content = doc.export_to_markdown()
        elif output_format == "html":
            content = doc.export_to_html()
        elif output_format == "json":
            content = doc.model_dump_json(indent=2)
        else:
            raise ValueError(f"Unknown format: {output_format}")

        Path(output_path).write_text(content)
        return str(input_path), True, None
    except Exception as e:
        return str(input_path), False, str(e)


def batch_convert(
    input_dir: str,
    output_dir: str,
    pattern: str = "*",
    output_format: str = "md",
    use_ocr: bool = False,
    workers: int = 4,
):
    """Batch convert documents from a directory.

    Args:
        input_dir: Input directory containing documents
        output_dir: Output directory for converted files
        pattern: Glob pattern for input files (default: *)
        output_format: Output format (md, html, json)
        use_ocr: Enable OCR for scanned documents
        workers: Number of parallel workers
    """
    input_path = Path(input_dir)
    output_path = Path(output_dir)
    output_path.mkdir(parents=True, exist_ok=True)

    # Supported extensions
    supported_exts = {".pdf", ".docx", ".pptx", ".xlsx", ".html", ".htm", ".png", ".jpg", ".jpeg", ".tiff"}

    # Find files matching pattern
    if pattern == "*":
        files = [f for f in input_path.iterdir() if f.is_file() and f.suffix.lower() in supported_exts]
    else:
        files = [f for f in input_path.glob(pattern) if f.is_file() and f.suffix.lower() in supported_exts]

    if not files:
        print(f"No supported files found in {input_dir}")
        print(f"Supported formats: {', '.join(sorted(supported_exts))}")
        return

    print(f"Found {len(files)} file(s) to convert")
    print(f"Output format: {output_format}")
    print(f"Workers: {workers}")
    print("-" * 50)

    # Determine output extension
    ext_map = {"md": ".md", "html": ".html", "json": ".json"}
    out_ext = ext_map[output_format]

    # Prepare conversion tasks
    tasks = []
    for f in files:
        out_file = output_path / f"{f.stem}{out_ext}"
        tasks.append((f, out_file, output_format, use_ocr))

    # Process files
    success_count = 0
    error_count = 0

    if workers == 1:
        # Sequential processing
        for i, task in enumerate(tasks, 1):
            input_file, success, error = convert_single(task)
            if success:
                print(f"[{i}/{len(tasks)}] OK: {Path(input_file).name}")
                success_count += 1
            else:
                print(f"[{i}/{len(tasks)}] ERROR: {Path(input_file).name} - {error}")
                error_count += 1
    else:
        # Parallel processing
        with ProcessPoolExecutor(max_workers=workers) as executor:
            futures = {executor.submit(convert_single, task): task for task in tasks}
            for i, future in enumerate(as_completed(futures), 1):
                input_file, success, error = future.result()
                if success:
                    print(f"[{i}/{len(tasks)}] OK: {Path(input_file).name}")
                    success_count += 1
                else:
                    print(f"[{i}/{len(tasks)}] ERROR: {Path(input_file).name} - {error}")
                    error_count += 1

    print("-" * 50)
    print(f"Complete: {success_count} succeeded, {error_count} failed")
    print(f"Output directory: {output_dir}")


def main():
    parser = argparse.ArgumentParser(
        description="Batch convert documents using Docling",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s input_dir/ output_dir/
  %(prog)s input_dir/ output_dir/ --pattern "*.pdf"
  %(prog)s input_dir/ output_dir/ --format html
  %(prog)s input_dir/ output_dir/ --ocr --workers 2
        """,
    )
    parser.add_argument("input_dir", help="Input directory containing documents")
    parser.add_argument("output_dir", help="Output directory for converted files")
    parser.add_argument(
        "--pattern",
        default="*",
        help="Glob pattern for input files (default: *)",
    )
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
        "--workers",
        type=int,
        default=4,
        help="Number of parallel workers (default: 4, use 1 for sequential)",
    )

    args = parser.parse_args()

    if not Path(args.input_dir).is_dir():
        print(f"Error: {args.input_dir} is not a directory", file=sys.stderr)
        sys.exit(1)

    try:
        batch_convert(
            args.input_dir,
            args.output_dir,
            args.pattern,
            args.format,
            args.ocr,
            args.workers,
        )
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
