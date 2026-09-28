import io
import json
import sys
import unittest
from pathlib import Path


sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from check_bounding_boxes import get_bounding_box_messages  # noqa: E402


class BoundingBoxPageBoundsTests(unittest.TestCase):
    def messages_for(self, page, entry, label):
        fields = {
            "pages": [{"page_number": 1, **page}],
            "form_fields": [
                {
                    "page_number": 1,
                    "description": "Name",
                    "entry_bounding_box": entry,
                    "label_bounding_box": label,
                }
            ],
        }
        return get_bounding_box_messages(io.StringIO(json.dumps(fields)))

    def test_boxes_outside_page_are_rejected(self):
        for page in (
            {"pdf_width": 100, "pdf_height": 100},
            {"image_width": 100, "image_height": 100},
        ):
            with self.subTest(page=page):
                messages = self.messages_for(page, [90, 30, 110, 50], [5, 5, 25, 20])
                self.assertTrue(any("outside page" in message for message in messages))

    def test_inverted_boxes_are_rejected(self):
        messages = self.messages_for(
            {"pdf_width": 100, "pdf_height": 100},
            [40, 30, 20, 50],
            [5, 5, 25, 20],
        )
        self.assertTrue(any("x0 < x1" in message for message in messages))

    def test_valid_boxes_still_pass(self):
        messages = self.messages_for(
            {"pdf_width": 100, "pdf_height": 100},
            [30, 30, 80, 50],
            [5, 5, 25, 20],
        )
        self.assertIn("SUCCESS: All bounding boxes are valid", messages)


if __name__ == "__main__":
    unittest.main()
