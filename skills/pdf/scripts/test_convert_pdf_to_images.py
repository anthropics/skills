"""Tests for convert_pdf_to_images output handling."""

import os
import sys
import tempfile
import types
import unittest
from pathlib import Path

# Stub pdf2image before importing the script so the test needs neither
# pdf2image nor a poppler install — convert_from_path is replaced per-test.
if "pdf2image" not in sys.modules:
    _stub = types.ModuleType("pdf2image")
    _stub.convert_from_path = lambda *args, **kwargs: []
    sys.modules["pdf2image"] = _stub

sys.path.insert(0, str(Path(__file__).resolve().parent))

import convert_pdf_to_images  # noqa: E402


class _FakeImage:
    """Minimal stand-in for a PIL image.

    save() writes a real file, mirroring PIL's behaviour of raising
    FileNotFoundError when the destination directory does not exist.
    """

    size = (100, 100)

    def resize(self, size):
        return self

    def save(self, path):
        Path(path).write_bytes(b"\x89PNG\r\n")


class ConvertOutputDirTest(unittest.TestCase):
    def test_creates_output_directory_when_missing(self):
        with tempfile.TemporaryDirectory() as tmp:
            output_dir = os.path.join(tmp, "missing", "pages")
            self.assertFalse(os.path.exists(output_dir))

            original = convert_pdf_to_images.convert_from_path
            convert_pdf_to_images.convert_from_path = (
                lambda *args, **kwargs: [_FakeImage(), _FakeImage()]
            )
            try:
                convert_pdf_to_images.convert("input.pdf", output_dir)
            finally:
                convert_pdf_to_images.convert_from_path = original

            self.assertTrue(os.path.isdir(output_dir))
            self.assertTrue(os.path.isfile(os.path.join(output_dir, "page_1.png")))
            self.assertTrue(os.path.isfile(os.path.join(output_dir, "page_2.png")))


if __name__ == "__main__":
    unittest.main()
