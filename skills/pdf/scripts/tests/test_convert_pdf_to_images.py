import importlib.util
import sys
import tempfile
import types
import unittest
from pathlib import Path
from unittest.mock import patch

from PIL import Image


SCRIPT = Path(__file__).resolve().parents[1] / "convert_pdf_to_images.py"


class ConvertPdfToImagesTests(unittest.TestCase):
    def test_converts_all_pages_in_bounded_batches(self):
        calls = []

        def convert_from_path(_path, *, dpi, first_page=None, last_page=None):
            calls.append((first_page, last_page))
            first = first_page or 1
            last = last_page or 7
            return [Image.new("RGB", (20, 10), "red") for _ in range(first, last + 1)]

        pdf2image = types.ModuleType("pdf2image")
        pdf2image.convert_from_path = convert_from_path
        pdf2image.pdfinfo_from_path = lambda _path: {"Pages": 7}

        with patch.dict(sys.modules, {"pdf2image": pdf2image}):
            spec = importlib.util.spec_from_file_location("pdf_converter_under_test", SCRIPT)
            module = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(module)

            with tempfile.TemporaryDirectory() as directory:
                module.convert("input.pdf", directory)
                for page in range(1, 8):
                    self.assertTrue((Path(directory) / f"page_{page}.png").is_file())

        self.assertEqual(calls, [(1, 5), (6, 7)])


if __name__ == "__main__":
    unittest.main()
