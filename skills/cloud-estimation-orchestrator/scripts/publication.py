"""Namespace-aware OOXML publication checks without reserializing XML or caches."""

from io import BytesIO
from pathlib import Path
import re
import xml.etree.ElementTree as ET
from xml.parsers import expat
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


def _element_spans(raw):
    """Original byte spans keyed by Expat's namespace-resolved element names."""
    encoding = ("utf-16-le" if raw.startswith((b"\xff\xfe", b"<\x00")) else
                "utf-16-be" if raw.startswith((b"\xfe\xff", b"\x00<")) else "utf-8")
    unit = 2 if encoding.startswith("utf-16") else 1

    def tag_end(start):
        quote = None
        for index in range(start, len(raw), unit):
            char = chr(raw[index]) if unit == 1 else raw[index:index + unit].decode(encoding, errors="surrogatepass")
            if quote:
                if char == quote:
                    quote = None
            elif char in ("'", '"'):
                quote = char
            elif char == ">":
                return index + unit
        raise ValueError("Publication: incomplete XML tag")

    parser = expat.ParserCreate(namespace_separator="}")
    stack, spans = [], []

    def start(name, attributes):
        begin = parser.CurrentByteIndex
        content = tag_end(begin)
        empty = raw[content - 2 * unit:content] == "/>".encode(encoding)
        span = dict(name=name, start=begin, content_start=content, empty=empty)
        stack.append(span)
        spans.append(span)

    def end(name):
        span = stack.pop()
        span["content_end"] = span["content_start"] if span["empty"] else parser.CurrentByteIndex
        span["end"] = span["content_start"] if span["empty"] else tag_end(parser.CurrentByteIndex)

    parser.StartElementHandler, parser.EndElementHandler = start, end
    parser.Parse(raw, True)
    return spans, encoding


def structural_guid_spans(content, part):
    """Mask only Office structural GUID attributes, never cell/customer identifiers.

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
    tags = list(re.finditer(r'''<(?![/!?])(?:[^>"']|"[^"]*"|'[^']*')+>''', lexical))
    if len(tags) != len(elements):
        return []  # Unsupported lexical structure: do not suppress detections.
    spans = []
    attributes = re.compile(r'\s+([^\s=/>]+)\s*=\s*([\"\'])(.*?)\2', re.S)
    for token, (element, scope) in zip(tags, elements):
        for match in attributes.finditer(token.group()):
            name = match.group(1)
            prefix, local = name.split(":", 1) if ":" in name else ("", name)
            uri = scope.get(prefix) if prefix else None  # Unqualified attributes have no default namespace.
            if prefix and uri is None:
                continue
            parsed_name = "{" + uri + "}" + local if uri else local
            value = match.group(3)
            if element.get(parsed_name) != value:
                continue  # The lexical span must belong to this actual parsed attribute.
            offset = token.start() + match.start(3)
            revision_document = (part == "xl/workbook.xml" and element.tag == "{http://schemas.microsoft.com/office/spreadsheetml/2014/revision}revisionPtr"
                                 and name == "documentId")
            if revision_document:
                document_id = re.fullmatch(r'[0-9]+_ncr:[0-9]+_(' + GUID.pattern + r')', value)
                if document_id:
                    spans.append((offset + document_id.start(1), offset + document_id.end(1)))
                continue
            if not GUID.fullmatch(value):
                continue
            revision_uid = uri in REVISION_NAMESPACES and local == "uid"
            revision_save = (part == "xl/workbook.xml" and element.tag == "{http://schemas.microsoft.com/office/spreadsheetml/2014/revision}revisionPtr"
                             and uri == "http://schemas.microsoft.com/office/spreadsheetml/2016/revision10" and local == "uidLastSave")
            drawing_id = (part.startswith("xl/drawings/") and element.tag == "{http://schemas.microsoft.com/office/drawing/2014/main}creationId" and local == "id" and uri is None)
            if revision_uid or revision_save or drawing_id:
                spans.append((offset, offset + len(value)))
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
            spans, encoding = _element_spans(raw)
            edits = []
            for span in spans:
                if span["name"] == ABS_PATH_NS + "}absPath":
                    edits.append((span["start"], span["end"], b""))
                elif (item.filename == "docProps/core.xml" and not span["empty"]
                      and span["name"] in (DC_NS + "}creator", CORE_NS + "}lastModifiedBy")):
                    edits.append((span["content_start"], span["content_end"], "Public synthetic estimate".encode(encoding)))
            # Apply only outermost edits, preserving all other bytes exactly.
            selected = []
            for begin, end, replacement in sorted(edits, key=lambda edit: (edit[0], -edit[1])):
                if not selected or begin >= selected[-1][1]:
                    selected.append((begin, end, replacement))
            for begin, end, replacement in reversed(selected):
                raw = raw[:begin] + replacement + raw[end:]
            after = ET.fromstring(raw)
            private_path = re.compile(r"(?i)(?:[a-z]:[\\/]Users[\\/]|/Users/|/home/)[a-z0-9_.-]+")
            decoded = [value for element in after.iter() for value in
                       (element.text, element.tail, *element.attrib.values()) if value]
            # xmlns bindings, including unused/shadowed ones, are not attrib values.
            decoded.extend(uri for event, (prefix, uri) in
                           ET.iterparse(BytesIO(raw), events=("start-ns",)))
            if (any(private_path.search(value) for value in decoded)
                    or private_path.search(raw.decode(encoding))):
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
