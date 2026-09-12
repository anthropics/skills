import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import MagicMock, patch

import create_validation_image


class FakeImage:
    def __init__(self):
        self.closed = False
        self.saved_to = None

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc, tb):
        self.close()

    def close(self):
        self.closed = True

    def save(self, output_path):
        self.saved_to = output_path


class CreateValidationImageTests(unittest.TestCase):
    def test_create_validation_image_closes_input_image(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            tmp_path = Path(tmpdir)
            fields_json_path = tmp_path / "fields.json"
            output_path = tmp_path / "output.png"
            fields_json_path.write_text(
                json.dumps(
                    {
                        "form_fields": [
                            {
                                "page_number": 2,
                                "entry_bounding_box": [1, 2, 3, 4],
                                "label_bounding_box": [5, 6, 7, 8],
                            },
                            {
                                "page_number": 3,
                                "entry_bounding_box": [9, 10, 11, 12],
                                "label_bounding_box": [13, 14, 15, 16],
                            },
                        ]
                    }
                )
            )

            fake_image = FakeImage()
            fake_draw = MagicMock()

            with patch.object(create_validation_image.Image, "open", return_value=fake_image) as image_open:
                with patch.object(create_validation_image.ImageDraw, "Draw", return_value=fake_draw):
                    create_validation_image.create_validation_image(
                        2,
                        str(fields_json_path),
                        "input.png",
                        str(output_path),
                    )

            image_open.assert_called_once_with("input.png")
            self.assertTrue(fake_image.closed)
            self.assertEqual(fake_image.saved_to, str(output_path))
            self.assertEqual(fake_draw.rectangle.call_count, 2)


if __name__ == "__main__":
    unittest.main()
