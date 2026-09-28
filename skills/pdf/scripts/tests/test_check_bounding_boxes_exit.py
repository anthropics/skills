import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


SCRIPT = Path(__file__).resolve().parents[1] / "check_bounding_boxes.py"


class BoundingBoxExitTests(unittest.TestCase):
    def run_checker(self, entry_box):
        with tempfile.TemporaryDirectory() as directory:
            fields = Path(directory) / "fields.json"
            fields.write_text(
                json.dumps(
                    {
                        "form_fields": [
                            {
                                "page_number": 1,
                                "description": "Name",
                                "label_bounding_box": [10, 10, 30, 25],
                                "entry_bounding_box": entry_box,
                            }
                        ]
                    }
                )
            )
            return subprocess.run(
                [sys.executable, str(SCRIPT), str(fields)],
                capture_output=True,
                text=True,
            )

    def test_invalid_boxes_exit_nonzero(self):
        result = self.run_checker([20, 10, 40, 25])
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("FAILURE: intersection", result.stdout)

    def test_valid_boxes_exit_zero(self):
        result = self.run_checker([35, 10, 55, 25])
        self.assertEqual(result.returncode, 0)
        self.assertIn("SUCCESS: All bounding boxes are valid", result.stdout)


if __name__ == "__main__":
    unittest.main()
