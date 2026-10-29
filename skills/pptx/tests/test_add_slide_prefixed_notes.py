import importlib.util
import sys
from pathlib import Path
from xml.etree import ElementTree

import pytest


SCRIPTS = Path(__file__).resolve().parents[1] / "scripts"
sys.path.insert(0, str(SCRIPTS))
spec = importlib.util.spec_from_file_location("add_slide", SCRIPTS / "add_slide.py")
add_slide = importlib.util.module_from_spec(spec)
spec.loader.exec_module(add_slide)


@pytest.mark.parametrize("prefix", ["", "rel:"])
def test_duplicate_slide_removes_namespaced_notes_relationship(tmp_path, prefix):
    slides = tmp_path / "ppt" / "slides"
    rels = slides / "_rels"
    rels.mkdir(parents=True)
    (slides / "slide1.xml").write_text("<slide/>", encoding="utf-8")
    namespace = (
        'xmlns:rel="http://schemas.openxmlformats.org/package/2006/relationships"'
        if prefix
        else 'xmlns="http://schemas.openxmlformats.org/package/2006/relationships"'
    )
    (rels / "slide1.xml.rels").write_text(
        f"""<{prefix}Relationships {namespace}>
  <{prefix}Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/notesSlide" Target="../notesSlides/notesSlide1.xml"/>
  <{prefix}Relationship Id="rId2" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/image" Target="../media/image1.png"/>
</{prefix}Relationships>""",
        encoding="utf-8",
    )
    (tmp_path / "[Content_Types].xml").write_text(
        '<Types><Override PartName="/ppt/slides/slide1.xml"/></Types>',
        encoding="utf-8",
    )
    (tmp_path / "ppt" / "presentation.xml").write_text(
        '<p:presentation xmlns:p="http://schemas.openxmlformats.org/presentationml/2006/main" '
        'xmlns:r="http://schemas.openxmlformats.org/officeDocument/2006/relationships">'
        '<p:sldIdLst><p:sldId id="256" r:id="rId1"/></p:sldIdLst></p:presentation>',
        encoding="utf-8",
    )
    (tmp_path / "ppt" / "_rels").mkdir()
    (tmp_path / "ppt" / "_rels" / "presentation.xml.rels").write_text(
        '<Relationships><Relationship Id="rId1" '
        'Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/slide" '
        'Target="slides/slide1.xml"/></Relationships>',
        encoding="utf-8",
    )

    assert add_slide.duplicate_slide(tmp_path, "slide1.xml") == "slide2.xml"

    copied = ElementTree.parse(rels / "slide2.xml.rels")
    types = {element.attrib["Type"].rsplit("/", 1)[-1] for element in copied.getroot()}
    assert types == {"image"}
