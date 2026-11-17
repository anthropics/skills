#!/usr/bin/env python3
"""
validate_docx.py
Lightweight validator: checks page margins and base font size on Normal style.
"""
import sys, json
from docx import Document

def main(docx_path, expected_margins_in=None):
    doc = Document(docx_path)
    sec = doc.sections[0]
    report = {"file": docx_path, "checks": [], "warnings": [], "errors": []}

    if expected_margins_in:
        # python-docx stores inches as EMU; convert via .inches
        m = {
            "top": sec.top_margin.inches,
            "right": sec.right_margin.inches,
            "bottom": sec.bottom_margin.inches,
            "left": sec.left_margin.inches
        }
        report["checks"].append({"name": "margins", "actual": m, "expected": expected_margins_in,
                                 "pass": all(abs(m[k]-expected_margins_in[k]) < 0.01 for k in m)})

    normal = doc.styles["Normal"].font
    report["checks"].append({"name": "normal_font", "family": normal.name, "size_pt": normal.size.pt if normal.size else None})
    print(json.dumps(report, indent=2))

if __name__ == "__main__":
    if len(sys.argv) < 2:
        raise SystemExit("Usage: python validate_docx.py input.docx")
    main(sys.argv[1])
