import sys
import tempfile
import unittest
from pathlib import Path


sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from clean import RefusedToClean, clean_unused_files  # noqa: E402


class CleanMissingPresentationTests(unittest.TestCase):
    def test_missing_presentation_index_never_deletes_slides(self):
        for missing in ("presentation.xml", "presentation.xml.rels"):
            with self.subTest(missing=missing), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                slides = root / "ppt" / "slides"
                slide_rels = slides / "_rels"
                slide_rels.mkdir(parents=True)
                slide = slides / "slide1.xml"
                slide.write_text("<slide/>")
                (slide_rels / "slide1.xml.rels").write_text(
                    '<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">'
                    '<Relationship Id="rId1" Type="layout" '
                    'Target="../slideLayouts/slideLayout1.xml"/>'
                    '</Relationships>'
                )

                if missing != "presentation.xml":
                    presentation = root / "ppt" / "presentation.xml"
                    presentation.write_text("<presentation/>")
                if missing != "presentation.xml.rels":
                    pres_rels = root / "ppt" / "_rels" / "presentation.xml.rels"
                    pres_rels.parent.mkdir(parents=True)
                    pres_rels.write_text("<Relationships/>")

                with self.assertRaises(RefusedToClean):
                    clean_unused_files(root)
                self.assertTrue(slide.is_file())


if __name__ == "__main__":
    unittest.main()
