#!/usr/bin/env python3
"""
extract_docx_blocks.py
Extracts paragraphs from a .docx into a stable block list JSON so an LLM can label headings vs body.

Usage:
  python extract_docx_blocks.py input.docx > blocks.json
"""
import sys, json
from docx import Document

def main(path):
    doc = Document(path)
    blocks = []
    i = 1
    for p in doc.paragraphs:
        txt = p.text or ""
        # Preserve empty paragraphs too (can be normalized later)
        blocks.append({
            "id": f"p{i:04d}",
            "text": txt,
            "style": p.style.name if p.style else None
        })
        i += 1
    print(json.dumps({"source": path, "blocks": blocks}, indent=2))

if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("Usage: python extract_docx_blocks.py input.docx")
    main(sys.argv[1])
