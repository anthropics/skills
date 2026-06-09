#!/usr/bin/env python3
"""
Inject Zotero-style Word field codes into an unpacked .docx document.

This transforms plain [N] or [N,N,N] inline citations into Word complex field
codes with ADDIN ZOTERO_ITEM CSL_CITATION JSON payloads. The bibliography
section is wrapped in ADDIN ZOTERO_BIBL. The result is that citations highlight
grey when clicked in Word, exactly like real Zotero/Mendeley output.

Usage:
  python3 inject_zotero_fields.py --unpacked unpacked/ --refs references.json

Prerequisites:
  - Document must already be unpacked with:
      python3 /mnt/skills/public/docx/scripts/office/unpack.py doc.docx unpacked/
  - After injection, repack with:
      python3 /mnt/skills/public/docx/scripts/office/pack.py unpacked/ out.docx --original doc.docx
"""

import argparse
import copy
import json
import os
import random
import re
import string
import xml.etree.ElementTree as ET

WML = "http://schemas.openxmlformats.org/wordprocessingml/2006/main"

# Register all common OOXML namespaces to prevent loss during parsing
NAMESPACES = {
    "w": WML,
    "r": "http://schemas.openxmlformats.org/officeDocument/2006/relationships",
    "wp": "http://schemas.openxmlformats.org/drawingml/2006/wordprocessingDrawing",
    "a": "http://schemas.openxmlformats.org/drawingml/2006/main",
    "mc": "http://schemas.openxmlformats.org/markup-compatibility/2006",
    "w14": "http://schemas.microsoft.com/office/word/2010/wordml",
    "w15": "http://schemas.microsoft.com/office/word/2012/wordml",
    "wp14": "http://schemas.microsoft.com/office/word/2010/wordprocessingDrawing",
    "wps": "http://schemas.microsoft.com/office/word/2010/wordprocessingShape",
}

for prefix, uri in NAMESPACES.items():
    ET.register_namespace(prefix, uri)


def random_id(length=8):
    return "".join(random.choices(string.ascii_letters + string.digits, k=length))


def make_csl_json(ref_ids, display_text, ref_lookup):
    """Build CSL_CITATION JSON payload matching Zotero's format."""
    items = []
    for rid in ref_ids:
        items.append({
            "id": rid,
            "uris": [f"http://zotero.org/users/local/gen/items/REF{rid:04d}"],
            "uri": [f"http://zotero.org/users/local/gen/items/REF{rid:04d}"],
            "itemData": {"id": rid, "type": "article-journal"},
        })
    return json.dumps({
        "citationID": random_id(),
        "properties": {
            "formattedCitation": display_text,
            "plainCitation": display_text,
            "noteIndex": 0,
        },
        "citationItems": items,
        "schema": "https://github.com/citation-style-language/schema/raw/master/csl-citation.json",
    }, ensure_ascii=True)


def make_el(tag, attrib=None, text=None):
    el = ET.Element(f"{{{WML}}}{tag}", attrib or {})
    if text:
        el.text = text
    return el


def make_fldchar(ftype):
    r = make_el("r")
    r.append(make_el("fldChar", {f"{{{WML}}}fldCharType": ftype}))
    return r


def make_instr_run(instr_text):
    r = make_el("r")
    it = make_el("instrText", {"{http://www.w3.org/XML/1998/namespace}space": "preserve"})
    it.text = f" {instr_text} "
    r.append(it)
    return r


def make_text_run(text, rpr_el=None):
    r = make_el("r")
    if rpr_el is not None:
        r.append(copy.deepcopy(rpr_el))
    t = make_el("t")
    if text.startswith(" ") or text.endswith(" "):
        t.set("{http://www.w3.org/XML/1998/namespace}space", "preserve")
    t.text = text
    r.append(t)
    return r


def build_citation_field(ref_ids, display_text, rpr_el, ref_lookup):
    """Return list of XML elements for a complete Zotero citation field."""
    csl = make_csl_json(ref_ids, display_text, ref_lookup)
    instr = f"ADDIN ZOTERO_ITEM CSL_CITATION {csl}"
    return [
        make_fldchar("begin"),
        make_instr_run(instr),
        make_fldchar("separate"),
        make_text_run(display_text, rpr_el),
        make_fldchar("end"),
    ]


def fix_missing_namespaces(doc_path):
    """Add any missing namespace declarations back to the root element."""
    content = open(doc_path, "r", encoding="utf-8").read()

    required = {
        "w14": 'xmlns:w14="http://schemas.microsoft.com/office/word/2010/wordml"',
        "w15": 'xmlns:w15="http://schemas.microsoft.com/office/word/2012/wordml"',
        "wp14": 'xmlns:wp14="http://schemas.microsoft.com/office/word/2010/wordprocessingDrawing"',
    }

    m = re.search(r"(<\w+:document\b)", content)
    if not m:
        return

    missing = [decl for ns, decl in required.items() if f"xmlns:{ns}=" not in content]
    if missing:
        insert = " " + " ".join(missing)
        pos = m.end()
        content = content[:pos] + insert + content[pos:]
        open(doc_path, "w", encoding="utf-8").write(content)
        print(f"  Fixed {len(missing)} missing namespace declarations")


def inject_inline_citations(body, ref_lookup):
    """Find [N] patterns in text runs and wrap them in Zotero field codes."""
    cite_pattern = re.compile(r"\[(\d+(?:,\s*\d+)*)\]")
    count = 0

    for para in body.iter(f"{{{WML}}}p"):
        runs = list(para.findall(f"{{{WML}}}r"))

        for run in runs:
            t_el = run.find(f"{{{WML}}}t")
            if t_el is None or t_el.text is None:
                continue

            text = t_el.text
            matches = list(cite_pattern.finditer(text))
            if not matches:
                continue

            rpr = run.find(f"{{{WML}}}rPr")
            run_idx = list(para).index(run)
            para.remove(run)

            insert_pos = run_idx
            last_end = 0

            for m in matches:
                before = text[last_end:m.start()]
                if before:
                    para.insert(insert_pos, make_text_run(before, rpr))
                    insert_pos += 1

                cite_text = m.group(0)
                ref_ids = [int(x.strip()) for x in m.group(1).split(",")]

                for el in build_citation_field(ref_ids, cite_text, rpr, ref_lookup):
                    para.insert(insert_pos, el)
                    insert_pos += 1

                count += 1
                last_end = m.end()

            after = text[last_end:]
            if after:
                para.insert(insert_pos, make_text_run(after, rpr))

    return count


def inject_bibliography_field(body):
    """Wrap bibliography paragraphs in a ZOTERO_BIBL field code."""
    ref_paras = []
    for para in body.findall(f"{{{WML}}}p"):
        for run in para.findall(f"{{{WML}}}r"):
            t = run.find(f"{{{WML}}}t")
            if t is not None and t.text and re.match(r"^\d+\.\s", t.text):
                ref_paras.append(para)
                break

    if not ref_paras:
        print("  No bibliography paragraphs found")
        return 0

    first_ref = ref_paras[0]
    last_ref = ref_paras[-1]
    first_idx = list(body).index(first_ref)

    # Insert field begin paragraph before first reference
    begin_para = make_el("p")
    begin_para.append(make_fldchar("begin"))
    bib_json = json.dumps({
        "uncited": [], "omitted": [], "custom": [],
        "schema": "https://github.com/citation-style-language/schema/raw/master/csl-citation.json",
    }, ensure_ascii=True)
    begin_para.append(make_instr_run(f"ADDIN ZOTERO_BIBL {bib_json} CSL_BIBLIOGRAPHY"))
    begin_para.append(make_fldchar("separate"))
    body.insert(first_idx, begin_para)

    # Insert field end paragraph after last reference (+1 because we just inserted)
    end_para = make_el("p")
    end_para.append(make_fldchar("end"))
    new_last_idx = list(body).index(last_ref)
    body.insert(new_last_idx + 1, end_para)

    return len(ref_paras)


def main():
    parser = argparse.ArgumentParser(description="Inject Zotero field codes into unpacked docx")
    parser.add_argument("--unpacked", required=True, help="Path to unpacked docx directory")
    parser.add_argument("--refs", required=True, help="Path to references.json")
    args = parser.parse_args()

    doc_path = os.path.join(args.unpacked, "word", "document.xml")

    # Load references
    refs = json.load(open(args.refs))
    ref_lookup = {r["id"]: r for r in refs}

    # Parse XML
    tree = ET.parse(doc_path)
    root = tree.getroot()
    body = root.find(f"{{{WML}}}body")

    if body is None:
        print("Error: No <w:body> found in document.xml")
        return 1

    # Inject inline citations
    cite_count = inject_inline_citations(body, ref_lookup)
    print(f"Injected {cite_count} inline Zotero citation field codes")

    # Inject bibliography field
    bib_count = inject_bibliography_field(body)
    print(f"Wrapped {bib_count} bibliography entries in ZOTERO_BIBL field")

    # Write back
    tree.write(doc_path, xml_declaration=True, encoding="UTF-8")

    # Fix namespace declarations that ElementTree may have dropped
    fix_missing_namespaces(doc_path)

    print("Done! Zotero field codes injected successfully.")
    return 0


if __name__ == "__main__":
    exit(main())
