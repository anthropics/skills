"""Namespace-aware OOXML publication checks without reserializing XML or caches."""

from io import BytesIO
from pathlib import Path
import re
import xml.etree.ElementTree as ET
from zipfile import ZipFile

ABS_PATH_NS = "http://schemas.microsoft.com/office/spreadsheetml/2010/11/ac"
CORE_NS = "http://schemas.openxmlformats.org/package/2006/metadata/core-properties"
DC_NS = "http://purl.org/dc/elements/1.1/"
GUID = re.compile(r"\{[0-9a-fA-F]{8}(?:-[0-9a-fA-F]{4}){3}-[0-9a-fA-F]{12}\}")
REVISION_NAMESPACES = {
    "http://schemas.microsoft.com/office/spreadsheetml/2014/revision",
    "http://schemas.microsoft.com/office/spreadsheetml/2015/revision2",
    "http://schemas.microsoft.com/office/spreadsheetml/2016/revision3",
}


def _namespaces(raw):
    return list(ET.iterparse(BytesIO(raw), events=("start-ns",)))


def structural_guid_spans(content, part):
    """Mask only Office revision uid attributes, never cell/customer identifiers.

    The part and the attribute's namespace are both checked. No global UUID
    allowlist, numerical-suffix exemption or modification of workbook IDs.
    """
    if not part.startswith("xl/") or not part.endswith(".xml"):
        return []
    raw = content.encode("utf-8")
    try:
        pending, stack, elements = {}, [{}], []
        for event, item in ET.iterparse(BytesIO(raw), events=("start-ns", "start", "end")):
            if event == "start-ns":
                pending[item[0]] = item[1]
            elif event == "start":
                scope = stack[-1] | pending
                pending = {}
                stack.append(scope)
                elements.append((item, scope))
            else:
                stack.pop()
    except ET.ParseError:
        return []
    # Ignore declarations/comments; keep original offsets for safe diagnostics.
    lexical = re.sub(r"<!--.*?-->|<\?.*?\?>|<!\[CDATA\[.*?\]\]>", lambda m: " " * len(m.group()), content, flags=re.S)
    tags = list(re.finditer(r"<(?![/!?])[^>]+>", lexical))
    if len(tags) != len(elements):
        return []  # Unsupported lexical structure: do not suppress detections.
    spans = []
    for token, (element, scope) in zip(tags, elements):
        pattern = re.compile(r'(?<![\w:])([\w:]+)\s*=\s*([\"\'])(' + GUID.pattern + r')\2')
        for match in pattern.finditer(token.group()):
            name = match.group(1)
            prefix, local = name.split(":", 1) if ":" in name else ("", name)
            uri = scope.get(prefix) if prefix else None  # Unqualified attributes have no default namespace.
            revision_uid = uri in REVISION_NAMESPACES and local == "uid"
            revision_save = (part == "xl/workbook.xml" and element.tag == "{http://schemas.microsoft.com/office/spreadsheetml/2014/revision}revisionPtr"
                             and uri == "http://schemas.microsoft.com/office/spreadsheetml/2016/revision10" and local == "uidLastSave")
            drawing_id = (part.startswith("xl/drawings/") and element.tag == "{http://schemas.microsoft.com/office/drawing/2014/main}creationId" and local == "id" and uri is None)
            if revision_uid or revision_save or drawing_id:
                spans.append((token.start() + match.start(3), token.start() + match.end(3)))
    return spans


def sanitize_publication(path):
    """Neutralize Excel machine/author metadata; parse every XML/rels part.

    Bounded lexical substitutions keep xmlns declarations, QName values,
    relationships, structural GUIDs and cached formula bytes unchanged.
    Call only on the recalculation candidate before its atomic publication.
    """
    path = Path(path)
    with ZipFile(path) as archive:
        entries = [(item, archive.read(item.filename)) for item in archive.infolist()]
    inspected = 0
    updated = []
    for item, raw in entries:
        if item.filename.endswith((".xml", ".rels")):
            inspected += 1
            root = ET.fromstring(raw)
            ns = _namespaces(raw)
            for _, (prefix, uri) in ns:
                tag_prefix = (re.escape(prefix).encode() + b":") if prefix else b""
                if uri == ABS_PATH_NS and any(e.tag == "{" + uri + "}absPath" for e in root.iter()):
                    tag = tag_prefix + b"absPath"
                    raw = re.sub(b"<" + tag + rb"\b[^>]*(?:/>|>.*?</" + tag + b">)", b"", raw, flags=re.S)
                names = ("creator",) if uri == DC_NS else (("lastModifiedBy",) if uri == CORE_NS else ())
                if item.filename == "docProps/core.xml":
                    for name in names:
                        tag = tag_prefix + name.encode()
                        raw = re.sub(b"(<" + tag + rb"\b[^>]*>).*?(</" + tag + b">)", rb"\1Public synthetic estimate\2", raw, flags=re.S)
            after = ET.fromstring(raw)
            if re.search(rb"(?i)(?:[a-z]:[\\/]Users[\\/]|/Users/|/home/)[a-z0-9_.-]+", raw):
                raise ValueError("Publication: private local-user path remains in an XML/relationship part")
            if any(e.tag == "{" + ABS_PATH_NS + "}absPath" for e in after.iter()):
                raise ValueError("Publication: absolute-path metadata was not neutralized")
            if item.filename == "docProps/core.xml":
                for element in after.iter():
                    if element.tag in ("{" + DC_NS + "}creator", "{" + CORE_NS + "}lastModifiedBy") and element.text not in (None, "Public synthetic estimate"):
                        raise ValueError("Publication: author metadata was not neutralized")
        updated.append((item, raw))
    with ZipFile(path, "w") as archive:
        for item, raw in updated:
            archive.writestr(item, raw)
    return inspected


def blank_formula_caches(path):
    """An explicit string cache <v/> is empty, not an absent numeric cache."""
    ns = "{http://schemas.openxmlformats.org/spreadsheetml/2006/main}"
    blanks = set()
    with ZipFile(path) as archive:
        relations = ET.fromstring(archive.read("xl/_rels/workbook.xml.rels"))
        targets = {e.attrib["Id"]: e.attrib["Target"] for e in relations}
        workbook = ET.fromstring(archive.read("xl/workbook.xml"))
        for sheet in workbook.find(ns + "sheets"):
            target = targets[sheet.attrib["{http://schemas.openxmlformats.org/officeDocument/2006/relationships}id"]]
            name = target.lstrip("/") if target.startswith("/") else "xl/" + target
            for cell in ET.fromstring(archive.read(name)).iter(ns + "c"):
                value = cell.find(ns + "v")
                if cell.attrib.get("t") == "str" and cell.find(ns + "f") is not None and value is not None and value.text in (None, ""):
                    blanks.add((sheet.attrib["name"], cell.attrib["r"]))
    return blanks
