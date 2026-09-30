#!/usr/bin/env python3
"""
build_index.py — Convert discovered URLs into a lightweight BM25-searchable index.

Usage:
  python build_index.py --in artifacts/discovered.json --out artifacts/index.json

Output:
  artifacts/index.json: normalized index for BM25 ranking
  {
    "domain": "docs.example.com",
    "pages": [
      {
        "id": 0,
        "url": "https://docs.example.com/guide/intro",
        "title": "Introduction",
        "text": "Getting Started Installation Learn the basics..."
      },
      ...
    ],
    "indexed_at": "2025-01-11T10:59:00Z"
  }
"""

import json
import argparse
from datetime import datetime


def build_index(discovered_file: str) -> dict:
    """
    Load discovered.json and normalize into searchable index.
    Combines title, headings, and snippet into a single text field for BM25.
    """
    with open(discovered_file, "r") as f:
        discovered = json.load(f)

    pages = []
    for idx, page in enumerate(discovered.get("urls", [])):
        # Combine all textual content for BM25 ranking
        text_parts = [
            page.get("title", ""),
            " ".join(page.get("headings", [])),
            page.get("snippet", "")
        ]
        combined_text = " ".join(filter(None, text_parts))

        pages.append({
            "id": idx,
            "url": page.get("url"),
            "title": page.get("title", "Untitled"),
            "text": combined_text
        })

    return {
        "domain": discovered.get("domain"),
        "pages": pages,
        "indexed_at": datetime.utcnow().isoformat() + "Z",
        "total_pages": len(pages)
    }


def main():
    parser = argparse.ArgumentParser(
        description="Build a lightweight index from discovered URLs."
    )
    parser.add_argument(
        "--in",
        dest="input_file",
        required=True,
        help="Input discovered.json file"
    )
    parser.add_argument(
        "--out",
        required=True,
        help="Output index.json file"
    )

    args = parser.parse_args()

    print(f"Reading: {args.input_file}")
    index = build_index(args.input_file)

    import os
    os.makedirs(os.path.dirname(args.out), exist_ok=True)

    with open(args.out, "w") as f:
        json.dump(index, f, indent=2)

    print(f"✓ Indexed {index['total_pages']} pages")
    print(f"✓ Saved to: {args.out}")


if __name__ == "__main__":
    main()
