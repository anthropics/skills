#!/usr/bin/env python3
"""Prepare documents for RAG ingestion using Docling."""

import argparse
import json
import sys
from pathlib import Path


def chunk_text(text: str, chunk_size: int, overlap: int) -> list[dict]:
    """Split text into overlapping chunks.

    Args:
        text: Text to chunk
        chunk_size: Target chunk size in characters
        overlap: Overlap between chunks in characters

    Returns:
        List of chunk dictionaries with text and metadata
    """
    chunks = []
    start = 0
    chunk_id = 0

    while start < len(text):
        end = start + chunk_size

        # Try to break at sentence boundary
        if end < len(text):
            # Look for sentence end within last 20% of chunk
            search_start = start + int(chunk_size * 0.8)
            for i in range(end, search_start, -1):
                if text[i] in ".!?\n" and (i + 1 >= len(text) or text[i + 1].isspace()):
                    end = i + 1
                    break

        chunk_text = text[start:end].strip()
        if chunk_text:
            chunks.append({
                "chunk_id": chunk_id,
                "text": chunk_text,
                "start_char": start,
                "end_char": end,
            })
            chunk_id += 1

        start = end - overlap
        if chunks and start <= chunks[-1]["start_char"]:
            start = end  # Prevent infinite loop

    return chunks


def prepare_rag_chunks(
    input_path: str,
    output_path: str,
    chunk_size: int = 512,
    overlap: int = 50,
    use_ocr: bool = False,
    include_metadata: bool = True,
):
    """Prepare a document for RAG ingestion.

    Args:
        input_path: Path to input file or URL
        output_path: Path for output JSON file
        chunk_size: Target chunk size in characters
        overlap: Overlap between chunks in characters
        use_ocr: Enable OCR for scanned documents
        include_metadata: Include document metadata in output
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

    # Export to markdown for text extraction
    markdown = doc.export_to_markdown()

    # Chunk the text
    print(f"Chunking with size={chunk_size}, overlap={overlap}")
    chunks = chunk_text(markdown, chunk_size, overlap)

    # Build output structure
    output = {
        "source": input_path,
        "chunk_size": chunk_size,
        "overlap": overlap,
        "total_chunks": len(chunks),
        "chunks": [],
    }

    # Add metadata if requested
    if include_metadata:
        output["metadata"] = {
            "num_pages": getattr(doc, "num_pages", None),
            "num_tables": len(list(doc.tables)) if hasattr(doc, "tables") else 0,
        }

    # Add chunks with metadata
    for chunk in chunks:
        chunk_entry = {
            "id": f"{Path(input_path).stem}_chunk_{chunk['chunk_id']}",
            "text": chunk["text"],
            "metadata": {
                "source": input_path,
                "chunk_index": chunk["chunk_id"],
                "start_char": chunk["start_char"],
                "end_char": chunk["end_char"],
            },
        }
        output["chunks"].append(chunk_entry)

    # Write output
    Path(output_path).write_text(json.dumps(output, indent=2))
    print(f"Created {len(chunks)} chunks")
    print(f"Output: {output_path}")

    return output


def main():
    parser = argparse.ArgumentParser(
        description="Prepare document for RAG ingestion using Docling",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s document.pdf chunks.json
  %(prog)s document.pdf chunks.json --chunk-size 1000 --overlap 100
  %(prog)s scanned.pdf chunks.json --ocr
  %(prog)s document.pdf chunks.json --no-metadata

Output format:
  {
    "source": "document.pdf",
    "chunk_size": 512,
    "overlap": 50,
    "total_chunks": 10,
    "metadata": {...},
    "chunks": [
      {
        "id": "document_chunk_0",
        "text": "...",
        "metadata": {"source": "...", "chunk_index": 0, ...}
      },
      ...
    ]
  }
        """,
    )
    parser.add_argument("input", help="Input file path or URL")
    parser.add_argument("output", help="Output JSON file path")
    parser.add_argument(
        "--chunk-size",
        type=int,
        default=512,
        help="Target chunk size in characters (default: 512)",
    )
    parser.add_argument(
        "--overlap",
        type=int,
        default=50,
        help="Overlap between chunks in characters (default: 50)",
    )
    parser.add_argument(
        "--ocr",
        action="store_true",
        help="Enable OCR for scanned documents",
    )
    parser.add_argument(
        "--no-metadata",
        action="store_true",
        help="Exclude document metadata from output",
    )

    args = parser.parse_args()

    if args.chunk_size <= args.overlap:
        print("Error: chunk-size must be greater than overlap", file=sys.stderr)
        sys.exit(1)

    try:
        prepare_rag_chunks(
            args.input,
            args.output,
            args.chunk_size,
            args.overlap,
            args.ocr,
            not args.no_metadata,
        )
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
