#!/usr/bin/env python3
"""Extract searchable text from one PDF or a directory of PDFs (materials-paper-to-patent)."""

import argparse
from pathlib import Path

from pypdf import PdfReader


def extract(source: Path, destination: Path) -> tuple[int, int]:
    reader = PdfReader(source)
    pages = []
    for number, page in enumerate(reader.pages, start=1):
        text = page.extract_text() or ""
        pages.append(f"\n\n===== PAGE {number} =====\n\n{text}")

    content = "".join(pages)
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(content, encoding="utf-8")
    return len(reader.pages), len(content.strip())


def collect_pdfs(source: Path) -> list[Path]:
    if source.is_file():
        if source.suffix.lower() != ".pdf":
            raise ValueError(f"Input is not a PDF: {source}")
        return [source]
    if source.is_dir():
        return sorted(path for path in source.rglob("*.pdf") if path.is_file())
    raise FileNotFoundError(f"Input does not exist: {source}")


def output_path(pdf: Path, source: Path, output: Path) -> Path:
    if source.is_file():
        if output.suffix.lower() == ".txt":
            return output
        return output / f"{pdf.stem}.txt"
    relative = pdf.relative_to(source).with_suffix(".txt")
    return output / relative


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path, help="PDF file or directory")
    parser.add_argument(
        "--output",
        type=Path,
        required=True,
        help="Output text file or directory",
    )
    args = parser.parse_args()

    try:
        pdfs = collect_pdfs(args.source)
    except (FileNotFoundError, ValueError) as error:
        parser.error(str(error))

    if not pdfs:
        parser.error(f"No PDF files found under: {args.source}")

    low_text = []
    for pdf in pdfs:
        destination = output_path(pdf, args.source, args.output)
        pages, characters = extract(pdf, destination)
        print(f"{pdf}\t{pages} pages\t{characters} characters\t{destination}")
        if characters < max(200, pages * 50):
            low_text.append(pdf)

    if low_text:
        print("\nOCR may be required for:")
        for pdf in low_text:
            print(f"- {pdf}")
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
