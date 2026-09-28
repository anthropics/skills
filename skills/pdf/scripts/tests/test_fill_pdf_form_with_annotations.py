import json
import sys
import tempfile
import unittest
from pathlib import Path

from pypdf import PdfReader, PdfWriter


sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from fill_pdf_form_with_annotations import fill_pdf_form  # noqa: E402


class AnnotationGeometryTests(unittest.TestCase):
    def fill_one_field(self, rotation=0, crop=None, image_coords=False):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "source.pdf"
            fields = Path(directory) / "fields.json"
            output = Path(directory) / "output.pdf"

            writer = PdfWriter()
            page = writer.add_blank_page(width=100, height=200)
            if crop:
                page.cropbox.lower_left = crop[:2]
                page.cropbox.upper_right = crop[2:]
            if rotation:
                page.rotate(rotation)
            writer.write(source)

            box = [20, 10, 60, 30]
            display_width, display_height = (
                (200, 100) if rotation in (90, 270) else (100, 200)
            )
            page_info = {
                "page_number": 1,
                "pdf_width": display_width,
                "pdf_height": display_height,
            }
            if image_coords:
                box = [value * 2 for value in box]
                page_info = {"page_number": 1, "image_width": 400, "image_height": 200}
            if crop:
                if rotation == 0:
                    box = [10, 20, 30, 40]
                crop_width, crop_height = (
                    (160, 80) if rotation in (90, 270) else (80, 160)
                )
                page_info = {
                    "page_number": 1,
                    "pdf_width": crop_width,
                    "pdf_height": crop_height,
                }

            fields.write_text(
                json.dumps(
                    {
                        "pages": [page_info],
                        "form_fields": [
                            {
                                "page_number": 1,
                                "entry_bounding_box": box,
                                "entry_text": {"text": "Example"},
                            }
                        ],
                    }
                )
            )
            fill_pdf_form(str(source), str(fields), str(output))
            annotation = PdfReader(output).pages[0]["/Annots"][0].get_object()
            return [float(value) for value in annotation["/Rect"]]

    def test_rotated_pages_use_display_coordinates(self):
        expected = {
            0: [20, 170, 60, 190],
            90: [10, 20, 30, 60],
            180: [40, 10, 80, 30],
            270: [70, 140, 90, 180],
        }
        for rotation, rect in expected.items():
            with self.subTest(rotation=rotation):
                self.assertEqual(self.fill_one_field(rotation=rotation), rect)

    def test_image_coordinates_on_rotated_page(self):
        self.assertEqual(self.fill_one_field(rotation=90, image_coords=True), [10, 20, 30, 60])

    def test_cropped_page_uses_crop_box_origin(self):
        self.assertEqual(
            self.fill_one_field(crop=(10, 20, 90, 180)), [20, 140, 40, 160]
        )

    def test_rotated_and_cropped_page(self):
        self.assertEqual(
            self.fill_one_field(rotation=90, crop=(10, 20, 90, 180)),
            [20, 40, 40, 80],
        )

    def test_field_page_outside_pdf_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "source.pdf"
            fields = Path(directory) / "fields.json"
            output = Path(directory) / "output.pdf"
            writer = PdfWriter()
            writer.add_blank_page(width=100, height=200)
            writer.write(source)
            fields.write_text(
                json.dumps(
                    {
                        "pages": [{"page_number": 2, "pdf_width": 100, "pdf_height": 200}],
                        "form_fields": [
                            {
                                "page_number": 2,
                                "entry_bounding_box": [10, 10, 20, 20],
                                "entry_text": {"text": "Example"},
                            }
                        ],
                    }
                )
            )
            with self.assertRaisesRegex(ValueError, "Page 2 is outside"):
                fill_pdf_form(str(source), str(fields), str(output))
            self.assertFalse(output.exists())


if __name__ == "__main__":
    unittest.main()
