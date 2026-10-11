#!/bin/bash
# check_layout.sh - Render a .docx as page images for visual inspection
# Usage: ./check_layout.sh document.docx [output_dir]
#
# Part of the document-typography skill.
# Converts docx → PDF via LibreOffice, then renders each page as JPEG.
# Use Claude's view tool to inspect each page-NN.jpg for layout issues.

set -e

DOCX="$1"
OUTDIR="${2:-.}"
BASENAME=$(basename "$DOCX" .docx)

if [ -z "$DOCX" ]; then
    echo "Usage: $0 document.docx [output_dir]"
    exit 1
fi

echo "=== Converting $DOCX to PDF ==="
python /mnt/skills/public/docx/scripts/office/soffice.py --headless --convert-to pdf "$DOCX"

PDF="${DOCX%.docx}.pdf"

echo "=== Rendering pages as JPEG (150 DPI) ==="
rm -f "$OUTDIR/page-"*.jpg
pdftoppm -jpeg -r 150 "$PDF" "$OUTDIR/page"

PAGES=$(ls "$OUTDIR"/page-*.jpg 2>/dev/null | wc -l)
echo "=== Done: $PAGES pages rendered ==="
echo ""
echo "Inspect with: view $OUTDIR/page-01.jpg"
