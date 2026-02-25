#!/usr/bin/env python3
"""
render_docx_from_legalxml.py
Very small reference renderer: converts LEGALDOC.xml (semantic tags) into a .docx using python-docx.

This is a starter implementation for your app; extend as needed for TOC/TOA, footnotes, etc.
"""
import sys, json
import xml.etree.ElementTree as ET
from docx import Document
from docx.shared import Inches, Pt
from docx.oxml.ns import qn

def load_courts(courts_json_path):
    with open(courts_json_path, "r", encoding="utf-8") as f:
        return json.load(f)

def resolve_profile(courts, jurisdiction_id):
    # Simple inheritance resolver (one level deep for now)
    c = courts["courts"][jurisdiction_id]
    resolved = {}
    for base_id in c.get("inherits", []):
        resolved.update(courts["profiles"][base_id])
    # overlay court-specific keys
    for k, v in c.items():
        if k != "inherits":
            resolved[k] = v
    return resolved

def set_margins(doc, margins_in):
    section = doc.sections[0]
    section.top_margin = Inches(margins_in["top"])
    section.right_margin = Inches(margins_in["right"])
    section.bottom_margin = Inches(margins_in["bottom"])
    section.left_margin = Inches(margins_in["left"])

def ensure_style(doc, name, font_family, font_size_pt, bold=False, italic=False, all_caps=False, line_spacing=None):
    styles = doc.styles
    if name in [s.name for s in styles]:
        style = styles[name]
    else:
        style = styles.add_style(name, 1)  # 1 = paragraph
    font = style.font
    font.name = font_family
    font.size = Pt(font_size_pt)
    font.bold = bold
    font.italic = italic
    if all_caps:
        font.all_caps = True
    # ensure East Asia font set too
    style.element.rPr.rFonts.set(qn('w:eastAsia'), font_family)
    if line_spacing:
        style.paragraph_format.line_spacing = line_spacing
    return style

def main(xml_path, jurisdiction_id, out_docx, courts_json_path):
    courts = load_courts(courts_json_path)
    profile = resolve_profile(courts, jurisdiction_id)

    doc = Document()
    set_margins(doc, profile["page"]["margins_in"])

    body_font = profile.get("body_font", {"family":"Times New Roman","size_pt":12})
    heading_font = profile.get("heading_font", body_font)

    # basic styles
    ensure_style(doc, "LEGAL_CAPTION", body_font["family"], body_font["size_pt"], bold=False, line_spacing=1.0)
    ensure_style(doc, "LEGAL_TITLE", body_font["family"], body_font["size_pt"], bold=True, line_spacing=1.0)
    ensure_style(doc, "LEGAL_H1", heading_font["family"], heading_font.get("size_pt", body_font["size_pt"]), bold=True, all_caps=True, line_spacing=1.0)
    ensure_style(doc, "LEGAL_H2", heading_font["family"], heading_font.get("size_pt", body_font["size_pt"]), bold=True, line_spacing=1.0)
    ensure_style(doc, "LEGAL_H3", heading_font["family"], heading_font.get("size_pt", body_font["size_pt"]), bold=True, italic=True, line_spacing=1.0)
    ensure_style(doc, "LEGAL_BODY", body_font["family"], body_font["size_pt"], bold=False, line_spacing=2.0)

    tree = ET.parse(xml_path)
    root = tree.getroot()

    def add_para(text, style):
        p = doc.add_paragraph(text)
        p.style = style
        return p

    for node in root:
        tag = node.tag.upper()
        if tag == "CAPTION":
            for line in (node.text or "").splitlines():
                if line.strip() == "":
                    continue
                add_para(line, "LEGAL_CAPTION")
        elif tag == "TITLE":
            add_para((node.text or "").strip(), "LEGAL_TITLE")
        elif tag == "H1":
            add_para((node.text or "").strip(), "LEGAL_H1")
        elif tag == "H2":
            add_para((node.text or "").strip(), "LEGAL_H2")
        elif tag == "H3":
            add_para((node.text or "").strip(), "LEGAL_H3")
        elif tag == "P":
            add_para((node.text or "").strip(), "LEGAL_BODY")
        else:
            # fallback: dump text
            if (node.text or "").strip():
                add_para((node.text or "").strip(), "LEGAL_BODY")

    doc.save(out_docx)
    print(f"Wrote: {out_docx}")

if __name__ == "__main__":
    if len(sys.argv) != 4:
        raise SystemExit("Usage: python render_docx_from_legalxml.py LEGALDOC.xml JURISDICTION_ID output.docx")
    xml_path, jurisdiction_id, out_docx = sys.argv[1], sys.argv[2], sys.argv[3]
    courts_json_path = os.path.join(os.path.dirname(__file__), "..", "jurisdictions", "courts.json")
    main(xml_path, jurisdiction_id, out_docx, courts_json_path)
