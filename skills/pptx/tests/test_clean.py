"""Regression tests for the fail-closed slide cleanup in scripts/clean.py."""

import sys
import tempfile
import unittest
from pathlib import Path

SCRIPTS_DIR = Path(__file__).resolve().parents[1] / "scripts"
sys.path.insert(0, str(SCRIPTS_DIR))

import clean  # noqa: E402

PML_NS = "http://schemas.openxmlformats.org/presentationml/2006/main"
REL_NS = "http://schemas.openxmlformats.org/officeDocument/2006/relationships"
PKG_REL_NS = "http://schemas.openxmlformats.org/package/2006/relationships"
SLIDE_REL_TYPE = (
    "http://schemas.openxmlformats.org/officeDocument/2006/relationships/slide"
)


def _sld_id(rid: str, prefix: str = "p", quote: str = '"') -> str:
    return f'<{prefix}:sldId id="256" r:id={quote}{rid}{quote}/>'


def _presentation_xml(sld_ids: str, prefix: str = "p") -> str:
    return (
        '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>\n'
        f'<{prefix}:presentation xmlns:{prefix}="{PML_NS}" xmlns:r="{REL_NS}">'
        f"<{prefix}:sldIdLst>{sld_ids}</{prefix}:sldIdLst>"
        f"</{prefix}:presentation>"
    )


def _rels_xml(rels) -> str:
    entries = "".join(
        f'<Relationship Id="{rid}" Type="{SLIDE_REL_TYPE}" Target="{target}"/>'
        for rid, target in rels
    )
    return (
        '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>\n'
        f'<Relationships xmlns="{PKG_REL_NS}">{entries}</Relationships>'
    )


def _write_package(root: Path, presentation_xml: str, slides, rels) -> None:
    ppt = root / "ppt"
    (ppt / "slides" / "_rels").mkdir(parents=True)
    (ppt / "_rels").mkdir(parents=True)
    (ppt / "presentation.xml").write_text(presentation_xml, encoding="utf-8")
    (ppt / "_rels" / "presentation.xml.rels").write_text(
        _rels_xml(rels), encoding="utf-8"
    )
    for name in slides:
        (ppt / "slides" / name).write_text("<p:sld/>", encoding="utf-8")


class CleanSlidesTest(unittest.TestCase):
    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.root = Path(self._tmp.name)

    def tearDown(self):
        self._tmp.cleanup()

    def _slide_path(self, name: str) -> Path:
        return self.root / "ppt" / "slides" / name

    def test_valid_presentation_removes_unreferenced_slide(self):
        _write_package(
            self.root,
            _presentation_xml(_sld_id("rId1") + _sld_id("rId2")),
            slides=["slide1.xml", "slide2.xml", "slide3.xml"],
            rels=[("rId1", "slides/slide1.xml"), ("rId2", "slides/slide2.xml")],
        )

        removed = clean.clean_unused_files(self.root)

        self.assertIn("ppt/slides/slide3.xml", removed)
        self.assertTrue(self._slide_path("slide1.xml").exists())
        self.assertTrue(self._slide_path("slide2.xml").exists())
        self.assertFalse(self._slide_path("slide3.xml").exists())

    def test_get_slides_in_sldidlst_resolves_referenced_slides(self):
        _write_package(
            self.root,
            _presentation_xml(_sld_id("rId1") + _sld_id("rId2")),
            slides=["slide1.xml", "slide2.xml"],
            rels=[("rId1", "slides/slide1.xml"), ("rId2", "slides/slide2.xml")],
        )

        self.assertEqual(
            clean.get_slides_in_sldidlst(self.root), {"slide1.xml", "slide2.xml"}
        )

    def test_missing_presentation_refuses_and_keeps_slides(self):
        _write_package(
            self.root,
            _presentation_xml(_sld_id("rId1")),
            slides=["slide1.xml"],
            rels=[("rId1", "slides/slide1.xml")],
        )
        (self.root / "ppt" / "presentation.xml").unlink()

        with self.assertRaises(clean.RefusedToClean):
            clean.clean_unused_files(self.root)

        self.assertTrue(self._slide_path("slide1.xml").exists())

    def test_malformed_presentation_refuses_and_keeps_slides(self):
        _write_package(
            self.root,
            _presentation_xml(_sld_id("rId1")),
            slides=["slide1.xml"],
            rels=[("rId1", "slides/slide1.xml")],
        )
        (self.root / "ppt" / "presentation.xml").write_text(
            "<p:presentation><p:sldIdLst><p:sldId r:id=", encoding="utf-8"
        )

        with self.assertRaises(clean.RefusedToClean):
            clean.clean_unused_files(self.root)

        self.assertTrue(self._slide_path("slide1.xml").exists())

    def test_alternative_namespace_prefix_discovers_slides(self):
        _write_package(
            self.root,
            _presentation_xml(
                _sld_id("rId1", prefix="ppt") + _sld_id("rId2", prefix="ppt"),
                prefix="ppt",
            ),
            slides=["slide1.xml", "slide2.xml", "slide3.xml"],
            rels=[("rId1", "slides/slide1.xml"), ("rId2", "slides/slide2.xml")],
        )

        removed = clean.clean_unused_files(self.root)

        self.assertIn("ppt/slides/slide3.xml", removed)
        self.assertTrue(self._slide_path("slide1.xml").exists())
        self.assertTrue(self._slide_path("slide2.xml").exists())
        self.assertFalse(self._slide_path("slide3.xml").exists())

    def test_single_quoted_attributes_discover_slides(self):
        _write_package(
            self.root,
            _presentation_xml(_sld_id("rId1", quote="'") + _sld_id("rId2", quote="'")),
            slides=["slide1.xml", "slide2.xml", "slide3.xml"],
            rels=[("rId1", "slides/slide1.xml"), ("rId2", "slides/slide2.xml")],
        )

        removed = clean.clean_unused_files(self.root)

        self.assertIn("ppt/slides/slide3.xml", removed)
        self.assertTrue(self._slide_path("slide1.xml").exists())
        self.assertTrue(self._slide_path("slide2.xml").exists())
        self.assertFalse(self._slide_path("slide3.xml").exists())

    def test_unresolvable_slide_ids_refuse_and_keep_slides(self):
        _write_package(
            self.root,
            _presentation_xml(_sld_id("rId9")),
            slides=["slide1.xml"],
            rels=[("rId1", "slides/slide1.xml")],
        )

        with self.assertRaises(clean.RefusedToClean):
            clean.clean_unused_files(self.root)

        self.assertTrue(self._slide_path("slide1.xml").exists())

    def test_empty_sldidlst_refuses_while_slides_exist(self):
        _write_package(
            self.root,
            _presentation_xml(""),
            slides=["slide1.xml"],
            rels=[("rId1", "slides/slide1.xml")],
        )

        with self.assertRaises(clean.RefusedToClean):
            clean.clean_unused_files(self.root)

        self.assertTrue(self._slide_path("slide1.xml").exists())

    def test_missing_sldidlst_refuses_while_slides_exist(self):
        _write_package(
            self.root,
            '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>\n'
            f'<p:presentation xmlns:p="{PML_NS}" xmlns:r="{REL_NS}">'
            "</p:presentation>",
            slides=["slide1.xml"],
            rels=[("rId1", "slides/slide1.xml")],
        )

        with self.assertRaises(clean.RefusedToClean):
            clean.clean_unused_files(self.root)

        self.assertTrue(self._slide_path("slide1.xml").exists())

    def test_missing_presentation_rels_refuses_and_keeps_slides(self):
        _write_package(
            self.root,
            _presentation_xml(_sld_id("rId1")),
            slides=["slide1.xml"],
            rels=[("rId1", "slides/slide1.xml")],
        )
        (self.root / "ppt" / "_rels" / "presentation.xml.rels").unlink()

        with self.assertRaises(clean.RefusedToClean):
            clean.clean_unused_files(self.root)

        self.assertTrue(self._slide_path("slide1.xml").exists())


if __name__ == "__main__":
    unittest.main()
