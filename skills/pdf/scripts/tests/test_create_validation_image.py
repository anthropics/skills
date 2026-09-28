import json
import sys
import tempfile
import unittest
from pathlib import Path

from PIL import Image


sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from create_validation_image import create_validation_image  # noqa: E402


class ValidationImageTests(unittest.TestCase):
    def test_overlay_scales_boxes_to_rendered_image(self):
        for dimensions in (
            {"pdf_width": 100, "pdf_height": 50},
            {"image_width": 100, "image_height": 50},
        ):
            with self.subTest(dimensions=dimensions), tempfile.TemporaryDirectory() as directory:
                source = Path(directory) / "page.png"
                fields = Path(directory) / "fields.json"
                output = Path(directory) / "overlay.png"
                Image.new("RGB", (200, 100), "white").save(source)
                fields.write_text(
                    json.dumps(
                        {
                            "pages": [{"page_number": 1, **dimensions}],
                            "form_fields": [
                                {
                                    "page_number": 1,
                                    "entry_bounding_box": [10, 5, 20, 15],
                                    "label_bounding_box": [30, 5, 40, 15],
                                }
                            ],
                        }
                    )
                )

                create_validation_image(1, str(fields), str(source), str(output))
                with Image.open(output) as overlay:
                    self.assertEqual(overlay.getpixel((25, 10)), (255, 0, 0))
                    self.assertEqual(overlay.getpixel((65, 10)), (0, 0, 255))

    def test_missing_page_reports_requested_number(self):
        with tempfile.TemporaryDirectory() as directory:
            fields = Path(directory) / "fields.json"
            fields.write_text(json.dumps({"pages": [{"page_number": 1}], "form_fields": []}))
            with self.assertRaisesRegex(ValueError, "Page 2"):
                create_validation_image(2, str(fields), "unused.png", "unused-output.png")

    def test_partial_page_dimensions_report_missing_pair(self):
        for dimensions in ({"pdf_width": 100}, {"image_height": 50}):
            with self.subTest(dimensions=dimensions), tempfile.TemporaryDirectory() as directory:
                fields = Path(directory) / "fields.json"
                fields.write_text(
                    json.dumps(
                        {"pages": [{"page_number": 1, **dimensions}], "form_fields": []}
                    )
                )
                with self.assertRaisesRegex(ValueError, "must define both"):
                    create_validation_image(1, str(fields), "unused.png", "unused-output.png")


if __name__ == "__main__":
    unittest.main()
