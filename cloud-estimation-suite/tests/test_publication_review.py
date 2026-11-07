"""Adversarial reproductions from the second independent delivery review."""

from pathlib import Path
import sys
from types import ModuleType
import xml.etree.ElementTree as ET
from zipfile import ZipFile

import pytest

from tooling.diagram_renderer import render_diagram
from tooling.publication import sanitize_publication
from tooling.recalculate import _native_excel, _verify_native_final


@pytest.mark.parametrize("location", ["attribute", "text", "tail"])
def test_decoded_private_xml_path_refuses_publication_without_mutation(tmp_path, location):
    # Exact escaped relationship bypass; the other forms exercise all XML values.
    target = "file:///" + "C:/Us&#101;rs/" + "private-person/private.xlsx"
    if location == "attribute":
        xml = '<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships"><Relationship Id="rPrivate" Type="hyperlink" Target="' + target + '" TargetMode="External"/></Relationships>'
        part = "xl/_rels/workbook.xml.rels"
    elif location == "text":
        xml, part = "<root><value>" + target + "</value></root>", "docProps/custom.xml"
    else:
        xml, part = "<root><value/>" + target + "</root>", "docProps/custom.xml"
    path = tmp_path / "escaped.xlsx"
    with ZipFile(path, "w") as archive:
        archive.writestr(part, xml)
    original = path.read_bytes()
    with pytest.raises(ValueError, match="local-user path"):
        sanitize_publication(path)
    assert path.read_bytes() == original


def test_abs_path_removal_respects_effective_namespace_and_preserves_app_homonym(tmp_path):
    office = "http://schemas.microsoft.com/office/spreadsheetml/2010/11/ac"
    app = "urn:synthetic-application"
    path = tmp_path / "scoped.xlsx"
    xml = ('<root xmlns:p="' + office + '"><p:absPath url="neutral"/>'
           '<data xmlns:p="' + app + '"><p:absPath keep="yes"><value>Required application data</value></p:absPath></data>'
           '<p:absPath url="neutral-again"/></root>')
    app_bytes = ('<p:absPath keep="yes"><value>Required application data</value></p:absPath>').encode()
    with ZipFile(path, "w") as archive:
        archive.writestr("xl/workbook.xml", xml)
    assert sanitize_publication(path) == 1
    with ZipFile(path) as archive:
        after = archive.read("xl/workbook.xml")
    root = ET.fromstring(after)
    assert not list(root.iter("{" + office + "}absPath"))
    preserved = list(root.iter("{" + app + "}absPath"))
    assert len(preserved) == 1 and preserved[0].attrib == {"keep": "yes"}
    assert preserved[0].find("value").text == "Required application data"
    assert app_bytes in after
    assert ('xmlns:p="' + office + '"').encode() in after
    assert ('xmlns:p="' + app + '"').encode() in after


@pytest.mark.parametrize("encoding", ["utf-8", "utf-16"])
def test_publication_preserves_unicode_and_quoted_tag_delimiters(tmp_path, encoding):
    office = "http://schemas.microsoft.com/office/spreadsheetml/2010/11/ac"
    xml = '<root xmlns:p="' + office + '" label="Café > neutral"><p:absPath url="Neutral > metadata"/><data>Conservé</data></root>'
    expected = xml.replace('<p:absPath url="Neutral > metadata"/>', "").encode(encoding)
    path = tmp_path / "unicode.xlsx"
    with ZipFile(path, "w") as archive:
        archive.writestr("xl/workbook.xml", xml.encode(encoding))
    sanitize_publication(path)
    with ZipFile(path) as archive:
        assert archive.read("xl/workbook.xml") == expected


@pytest.mark.parametrize("operation", ["final", "recalculate"])
def test_pywin32_attempts_quit_after_workbook_close_failure(tmp_path, monkeypatch, operation):
    path = tmp_path / "readonly.xlsx"
    path.write_bytes(b"unchanged final bytes")
    events = []

    class Book:
        ReadOnly = True

        def Save(self):
            events.append(("Save",))

        def Close(self, *, SaveChanges):
            events.append(("Close", SaveChanges))
            raise OSError("forced Workbook.Close failure")

    class Books:
        def Open(self, name, *, UpdateLinks, ReadOnly):
            events.append(("Open", UpdateLinks, ReadOnly))
            return Book()

    class Excel:
        Workbooks = Books()

        def CalculateFullRebuild(self):
            events.append(("Calculate",))

        def Quit(self):
            events.append(("Quit",))
            raise OSError("forced Excel.Quit failure")

    client = ModuleType("win32com.client")
    client.DispatchEx = lambda name: Excel()
    package = ModuleType("win32com")
    package.client = client
    monkeypatch.setitem(sys.modules, "win32com", package)
    monkeypatch.setitem(sys.modules, "win32com.client", client)
    with pytest.raises(Exception) as caught:
        (_verify_native_final if operation == "final" else _native_excel)(path, "pywin32")
    expected = [("Open", 0, True)] if operation == "final" else [("Open", 0, False), ("Calculate",), ("Save",)]
    assert events == expected + [("Close", False), ("Quit",)]
    assert "forced Workbook.Close failure" in str(caught.value)
    assert "forced Excel.Quit failure" in str(caught.value)
    assert path.read_bytes() == b"unchanged final bytes"


def test_flow_label_line_breaks_render_as_one_bounded_complete_label(tmp_path):
    graph = {"nodes": [{"id": "APP"}, {"id": "DATA"}],
             "edges": [{"id": "F-01", "source": "APP", "target": "DATA",
                        "label": "HTTPS\nConnexion\r\nbase\tchiffree"}]}
    render_diagram(graph, tmp_path / "a.svg", tmp_path / "a.png")
    svg = ET.parse(tmp_path / "a.svg")
    ns = {"s": "http://www.w3.org/2000/svg"}
    label = svg.find('.//s:g[@data-flow-label="F-01"]/s:text', ns)
    assert label.text == "HTTPS Connexion base chiffree"
    assert "\n" not in label.text and "\r" not in label.text and "\t" not in label.text
    box = svg.find('.//s:rect[@data-edge-label-id="F-01"]', ns)
    x, y, w, h = [float(box.attrib[key]) for key in ("x", "y", "width", "height")]
    assert x <= float(label.attrib["x"]) < x + w
    assert y < float(label.attrib["y"]) < y + h


def test_fallback_flow_identifier_is_also_a_single_line_label(tmp_path):
    graph = {"nodes": [{"id": "APP"}, {"id": "DATA"}],
             "edges": [{"id": "Flow\nidentifier", "source": "APP", "target": "DATA", "label": ""}]}
    render_diagram(graph, tmp_path / "fallback.svg", tmp_path / "fallback.png")
    root = ET.parse(tmp_path / "fallback.svg")
    ns = {"s": "http://www.w3.org/2000/svg"}
    labels = root.findall('.//s:g[@data-flow-label]/s:text', ns)
    assert labels and all(label.text == "Flow identifier" for label in labels)


@pytest.mark.parametrize("encoding", ["utf-8", "utf-16", "utf-16-be"])
@pytest.mark.parametrize("scope", ["prefix", "default", "shadowed", "unused", "attribute"])
def test_decoded_private_namespace_refuses_publication_without_mutation(tmp_path, encoding, scope):
    # Namespace declarations are not ordinary ElementTree attributes.
    uri = "file:///" + "C:/Us&#101;rs/" + "private-person/work"
    if scope == "prefix":
        xml = '<root xmlns:private="' + uri + '"><private:value/></root>'
    elif scope == "default":
        xml = '<root xmlns="' + uri + '"><value/></root>'
    elif scope == "shadowed":
        xml = '<root xmlns:p="urn:public"><p:value/><branch xmlns:p="' + uri + '"><p:value/></branch><p:value/></root>'
    elif scope == "unused":
        xml = '<root xmlns:private="' + uri + '"><value/></root>'
    else:
        xml = '<root xmlns:private="' + uri + '" private:value="neutral"/>'
    path = tmp_path / "namespace.xlsx"
    with ZipFile(path, "w") as archive:
        archive.writestr("xl/workbook.xml", xml.encode(encoding))
    original = path.read_bytes()
    with pytest.raises(ValueError, match="local-user path"):
        sanitize_publication(path)
    assert path.read_bytes() == original


@pytest.mark.parametrize("encoding", ["utf-8", "utf-16", "utf-16-be"])
def test_legitimate_office_namespaces_and_shadowing_are_preserved(tmp_path, encoding):
    xml = ('<root xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main" '
           'xmlns:p="http://schemas.microsoft.com/office/spreadsheetml/2010/11/ac">'
           '<p:value/><branch xmlns:p="urn:public:application"><p:value keep="yes"/></branch>'
           '<p:value/></root>')
    raw = xml.encode(encoding)
    path = tmp_path / "public-namespaces.xlsx"
    with ZipFile(path, "w") as archive:
        archive.writestr("xl/workbook.xml", raw)
    assert sanitize_publication(path) == 1
    with ZipFile(path) as archive:
        assert archive.read("xl/workbook.xml") == raw


def test_whitespace_only_flow_label_uses_normalized_identifier_in_its_box(tmp_path):
    graph = {"nodes": [{"id": "APP"}, {"id": "DATA"}],
             "edges": [{"id": "Flow\nidentifier", "source": "APP", "target": "DATA", "label": " \t "}]}
    render_diagram(graph, tmp_path / "whitespace.svg", tmp_path / "whitespace.png")
    root = ET.parse(tmp_path / "whitespace.svg")
    ns = {"s": "http://www.w3.org/2000/svg"}
    group = root.find('.//s:g[@data-flow-label]', ns)
    label, box = group.find("s:text", ns), group.find("s:rect", ns)
    assert label.text == "Flow identifier"
    x, y, w, h = [float(box.attrib[key]) for key in ("x", "y", "width", "height")]
    assert x <= float(label.attrib["x"]) < x + w
    assert y < float(label.attrib["y"]) < y + h
    assert w >= len("Flow identifier") * 9 + 12
