"""Sanitize a python-pptx .pptx for Keynote / macOS compatibility.

Fixes three silent OOXML compliance issues that cause Keynote to reject .pptx
files that open correctly in PowerPoint, PowerPoint Online, and LibreOffice:

1. Contradictory <p:sldSz> element — python-pptx updates dimensions but
   leaves the type attribute from the 4:3 template, producing widescreen
   dimensions declared as screen4x3.
2. Missing <p:notesMasterIdLst> — python-pptx creates the notesMaster
   relationship but doesn't register it in presentation.xml.
3. Embedded Windows printer settings stub — declares a content type that
   has no macOS equivalent and causes Keynote to refuse the file.

All fixes are idempotent and safe on files not produced by python-pptx.

See: https://github.com/anthropics/skills/issues/1167
"""

import re
import zipfile


def _patch_sldSz(pres_xml: str) -> str:
    """Remove contradictory type attribute from <p:sldSz> element."""
    m = re.search(r"<p:sldSz\s+([^/]+?)/>", pres_xml)
    if not m:
        return pres_xml
    attrs = m.group(1)
    cx = int(re.search(r'cx="(\d+)"', attrs).group(1))
    cy = int(re.search(r'cy="(\d+)"', attrs).group(1))
    # 16:9 widescreen
    if abs(cx - 12192000) <= 60000 and abs(cy - 6858000) <= 60000:
        new_el = '<p:sldSz cx="12192000" cy="6858000"/>'
    # 4:3 standard
    elif abs(cx - 9144000) <= 60000 and abs(cy - 6858000) <= 60000:
        new_el = '<p:sldSz cx="9144000" cy="6858000" type="screen4x3"/>'
    else:
        new_attrs = re.sub(r'\s+type="[^"]+"', "", attrs).strip()
        new_el = f"<p:sldSz {new_attrs}/>"
    return pres_xml.replace(m.group(0), new_el)


def _add_notes_master_id(pres_xml: str, rels_xml: str) -> str:
    """Add <p:notesMasterIdLst> block to presentation.xml if missing."""
    if "<p:notesMasterIdLst" in pres_xml:
        return pres_xml
    m = re.search(
        r'<Relationship Id="(rId\d+)"[^>]*?notesMaster[^>]*?/>', rels_xml
    )
    if not m:
        return pres_xml
    rid = m.group(1)
    block = (
        f'<p:notesMasterIdLst>'
        f'<p:notesMasterId r:id="{rid}"/>'
        f'</p:notesMasterIdLst>'
    )
    return re.sub(r"</p:sldIdLst>", "</p:sldIdLst>" + block, pres_xml, count=1)


def _strip_printer_settings(entries: dict) -> dict:
    """Remove Windows printer settings stub and its content type declaration."""
    to_drop = [n for n in entries if n.startswith("ppt/printerSettings/")]
    for n in to_drop:
        del entries[n]
    if not to_drop:
        return entries

    rels_path = "ppt/_rels/presentation.xml.rels"
    if rels_path in entries:
        rels = entries[rels_path].decode("utf-8")
        entries[rels_path] = re.sub(
            r'<Relationship[^>]*printerSettings[^>]*/>', "", rels
        ).encode("utf-8")

    ct_path = "[Content_Types].xml"
    if ct_path in entries:
        ct = entries[ct_path].decode("utf-8")
        entries[ct_path] = re.sub(
            r'<Default Extension="bin"[^>]*/>', "", ct
        ).encode("utf-8")

    return entries


def sanitize(path: str) -> None:
    """Post-process a .pptx file for Keynote / macOS compatibility.

    Reads the .pptx as a zip, applies the three OOXML compliance fixes
    in memory, and writes the result back to the same path.

    Idempotent — safe to call even on files already sanitized.
    """
    with zipfile.ZipFile(path, "r") as zin:
        entries = {n: zin.read(n) for n in zin.namelist()}

    entries = _strip_printer_settings(entries)

    pres_p, rels_p = "ppt/presentation.xml", "ppt/_rels/presentation.xml.rels"
    if pres_p in entries and rels_p in entries:
        pres = entries[pres_p].decode("utf-8")
        rels = entries[rels_p].decode("utf-8")
        pres = _patch_sldSz(pres)
        pres = _add_notes_master_id(pres, rels)
        entries[pres_p] = pres.encode("utf-8")

    with zipfile.ZipFile(path, "w", zipfile.ZIP_DEFLATED) as zout:
        for name, data in entries.items():
            zout.writestr(name, data)
