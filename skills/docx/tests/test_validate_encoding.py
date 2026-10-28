import io
import sys
import tempfile
import unittest
from pathlib import Path

# Add validators to sys.path
OFFICE_PATH = Path(__file__).resolve().parent.parent / "scripts" / "office"
sys.path.insert(0, str(OFFICE_PATH))

from validators.docx import DOCXSchemaValidator


class TestValidateEncoding(unittest.TestCase):
    def test_xml_binary_read_avoids_charmap_codec_error(self):
        """Verify _validate_single_file_xsd reads XML in binary mode so multibyte UTF-8 doesn't crash cp1252."""
        with tempfile.TemporaryDirectory() as td:
            base_dir = Path(td)
            word_dir = base_dir / "word"
            word_dir.mkdir()
            font_table = word_dir / "fontTable.xml"
            # Write fontTable with multibyte East Asian font name (e.g. MS Mincho in Japanese)
            xml_content = (
                '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>\n'
                '<w:fonts xmlns:w="http://schemas.openxmlformats.org/wordprocessingml/2006/main">\n'
                '  <w:font w:name="ＭＳ 明朝">\n'
                '    <w:altName w:val="MS Mincho"/>\n'
                "  </w:font>\n"
                "</w:fonts>\n"
            )
            font_table.write_text(xml_content, encoding="utf-8")

            validator = DOCXSchemaValidator(base_dir)
            passed, errors = validator._validate_single_file_xsd(font_table, base_dir)
            if errors:
                for err in errors:
                    self.assertNotIn("charmap", err.lower())
                    self.assertNotIn("codec", err.lower())

    def test_paragraph_count_and_repair_messages_are_ascii_safe(self):
        """Verify paragraph count output and repair messages use ASCII '->' rather than Unicode arrow."""
        with tempfile.TemporaryDirectory() as td:
            base_dir = Path(td)
            word_dir = base_dir / "word"
            word_dir.mkdir()
            (word_dir / "document.xml").write_text(
                '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>\n'
                '<w:document xmlns:w="http://schemas.openxmlformats.org/wordprocessingml/2006/main">\n'
                "  <w:body><w:p/></w:body>\n"
                "</w:document>\n",
                encoding="utf-8",
            )
            validator = DOCXSchemaValidator(base_dir, original_file=base_dir)
            out = io.StringIO()
            old_stdout = sys.stdout
            try:
                sys.stdout = out
                validator.compare_paragraph_counts()
            finally:
                sys.stdout = old_stdout

            output = out.getvalue()
            self.assertIn("->", output)
            self.assertNotIn("→", output)
            # Must encode cleanly to Windows default cp1252 codepage without UnicodeEncodeError
            encoded = output.encode("cp1252")
            self.assertTrue(len(encoded) > 0)


if __name__ == "__main__":
    unittest.main()
