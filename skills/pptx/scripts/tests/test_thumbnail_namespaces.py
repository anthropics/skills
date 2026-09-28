import sys
import tempfile
import unittest
import zipfile
from pathlib import Path


sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from thumbnail import get_slide_info  # noqa: E402


PML = "http://schemas.openxmlformats.org/presentationml/2006/main"
REL = "http://schemas.openxmlformats.org/officeDocument/2006/relationships"
PKG = "http://schemas.openxmlformats.org/package/2006/relationships"


class ThumbnailNamespaceTests(unittest.TestCase):
    def test_slide_order_with_nonstandard_namespace_prefixes(self):
        with tempfile.TemporaryDirectory() as directory:
            presentation = Path(directory) / "prefixed.pptx"
            with zipfile.ZipFile(presentation, "w") as archive:
                archive.writestr(
                    "ppt/presentation.xml",
                    f'<deck:presentation xmlns:deck="{PML}" xmlns:link="{REL}">'
                    '<deck:sldIdLst><deck:sldId id="256" link:id="rId1"/>'
                    '</deck:sldIdLst></deck:presentation>',
                )
                archive.writestr(
                    "ppt/_rels/presentation.xml.rels",
                    f'<pkg:Relationships xmlns:pkg="{PKG}">'
                    f'<pkg:Relationship Id="rId1" Type="{REL}/slide" '
                    'Target="slides/slide1.xml"/></pkg:Relationships>',
                )
                archive.writestr(
                    "ppt/slides/slide1.xml",
                    f'<deck:sld xmlns:deck="{PML}"/>',
                )

            self.assertEqual(
                get_slide_info(presentation),
                [{"name": "slide1.xml", "hidden": False}],
            )


if __name__ == "__main__":
    unittest.main()
