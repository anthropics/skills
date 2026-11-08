"""Regression tests for presentation relationship registration in add_slide."""

import sys
import tempfile
import unittest
from pathlib import Path
from xml.dom import minidom


SCRIPTS = Path(__file__).resolve().parents[1] / "scripts"
sys.path.insert(0, str(SCRIPTS))
from add_slide import duplicate_slide  # noqa: E402


REL_NS = "http://schemas.openxmlformats.org/package/2006/relationships"
SLIDE_REL = "http://schemas.openxmlformats.org/officeDocument/2006/relationships/slide"


class PresentationRelationshipTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        slides = self.root / "ppt" / "slides"
        slides.mkdir(parents=True)
        (slides / "slide1.xml").write_text("<slide/>", encoding="utf-8")
        (self.root / "[Content_Types].xml").write_text("<Types></Types>", encoding="utf-8")
        (self.root / "ppt" / "presentation.xml").write_text(
            '<p:presentation xmlns:p="http://schemas.openxmlformats.org/presentationml/2006/main" '
            'xmlns:r="http://schemas.openxmlformats.org/officeDocument/2006/relationships">'
            '<p:sldIdLst><p:sldId id="256" r:id="rId1"/></p:sldIdLst></p:presentation>',
            encoding="utf-8",
        )
        rels_dir = self.root / "ppt" / "_rels"
        rels_dir.mkdir()
        self.rels_path = rels_dir / "presentation.xml.rels"
        self.rels_path.write_text(
            f'<pkg:Relationships xmlns:pkg="{REL_NS}">'
            f'<pkg:Relationship Id="rId1" Type="{SLIDE_REL}" Target="slides/slide1.xml"/>'
            '</pkg:Relationships>',
            encoding="utf-8",
        )

    def test_prefixed_rels_registers_new_slide(self):
        self.assertEqual(duplicate_slide(self.root, "slide1.xml"), "slide2.xml")
        dom = minidom.parse(str(self.rels_path))
        relationships = dom.getElementsByTagNameNS(REL_NS, "Relationship")
        self.assertEqual(
            [(node.getAttribute("Id"), node.getAttribute("Target")) for node in relationships],
            [("rId1", "slides/slide1.xml"), ("rId2", "slides/slide2.xml")],
        )
        self.assertIn('r:id="rId2"', (self.root / "ppt" / "presentation.xml").read_text())

    def test_prefixed_rels_resolves_after_slide(self):
        self.assertEqual(duplicate_slide(self.root, "slide1.xml", after="slide1.xml"), "slide2.xml")
        dom = minidom.parse(str(self.rels_path))
        self.assertEqual(len(dom.getElementsByTagNameNS(REL_NS, "Relationship")), 2)

    def test_default_namespace_rels_still_work(self):
        self.rels_path.write_text(
            f'<Relationships xmlns="{REL_NS}">'
            f'<Relationship Id="rId1" Type="{SLIDE_REL}" Target="slides/slide1.xml"/>'
            '</Relationships>',
            encoding="utf-8",
        )
        self.assertEqual(duplicate_slide(self.root, "slide1.xml", after="slide1.xml"), "slide2.xml")
        dom = minidom.parse(str(self.rels_path))
        self.assertEqual(len(dom.getElementsByTagNameNS(REL_NS, "Relationship")), 2)

    def test_existing_ids_with_single_quotes_are_reserved(self):
        self.rels_path.write_text(
            f'<pkg:Relationships xmlns:pkg="{REL_NS}">'
            f'<pkg:Relationship Id="rId1" Type="{SLIDE_REL}" Target="slides/slide1.xml"/>'
            '<pkg:Relationship Id=\'rId2\' Type="layout" Target="slideLayouts/layout1.xml"/>'
            '</pkg:Relationships>',
            encoding="utf-8",
        )
        self.assertEqual(duplicate_slide(self.root, "slide1.xml"), "slide2.xml")
        dom = minidom.parse(str(self.rels_path))
        ids = [node.getAttribute("Id") for node in dom.getElementsByTagNameNS(REL_NS, "Relationship")]
        self.assertEqual(ids, ["rId1", "rId2", "rId3"])


if __name__ == "__main__":
    unittest.main()
