#!/usr/bin/env python3
"""Unpack and format XML contents of Office files (.docx, .pptx, .xlsx)"""

import random
import sys
import defusedxml.minidom
import zipfile
from pathlib import Path

# Get command line arguments
assert len(sys.argv) == 3, "Usage: python unpack.py <office_file> <output_dir>"
input_file, output_dir = sys.argv[1], sys.argv[2]

# Extract and format
output_path = Path(output_dir)
output_path.mkdir(parents=True, exist_ok=True)
zipfile.ZipFile(input_file).extractall(output_path)

# Format all XML files - CRITICAL: Use toxml() to preserve Word compatibility
# Microsoft Word is extremely sensitive to XML whitespace. Using toprettyxml()
# adds newlines and indentation that break Word compatibility.
xml_files = list(output_path.rglob("*.xml")) + list(output_path.rglob("*.rels"))
for xml_file in xml_files:
    content = xml_file.read_text(encoding="utf-8")
    dom = defusedxml.minidom.parseString(content)
    # ✅ CORRECT: Use toxml() to preserve original formatting and Word compatibility
    # ❌ WRONG: Never use toprettyxml() - it adds whitespace that breaks Word
    xml_file.write_bytes(dom.toxml(encoding="ascii"))

# For .docx files, suggest an RSID for tracked changes
if input_file.endswith(".docx"):
    suggested_rsid = "".join(random.choices("0123456789ABCDEF", k=8))
    print(f"Suggested RSID for edit session: {suggested_rsid}")
