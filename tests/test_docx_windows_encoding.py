import io
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'skills' / 'docx' / 'scripts' / 'office'))

from validators.base import BaseSchemaValidator
from validators.docx import DOCXSchemaValidator


class DummySchemaValidator(BaseSchemaValidator):
    def validate(self):
        return True


class ValidateSingleFileXsdEncodingTests(unittest.TestCase):
    def test_validate_single_file_xsd_opens_xml_as_utf8_text(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            xml_file = tmp_path / 'word' / 'document.xml'
            xml_file.parent.mkdir(parents=True)
            xml_file.write_text('<?xml version="1.0" encoding="UTF-8"?><root/>', encoding='utf-8')
            schema_path = tmp_path / 'schema.xsd'
            schema_path.write_text(
                '<?xml version="1.0" encoding="UTF-8"?>\n'
                '<xs:schema xmlns:xs="http://www.w3.org/2001/XMLSchema">\n'
                '  <xs:element name="root" type="xs:string"/>\n'
                '</xs:schema>\n',
                encoding='utf-8',
            )

            validator = DummySchemaValidator(tmp_path)
            validator._get_schema_path = lambda _: schema_path
            validator._remove_template_tags_from_text_nodes = lambda xml_doc: (xml_doc, False)
            validator._preprocess_for_mc_ignorable = lambda xml_doc: xml_doc
            validator._clean_ignorable_namespaces = lambda xml_doc: xml_doc

            open_calls = []
            real_open = open

            def tracking_open(file, mode='r', *args, **kwargs):
                open_calls.append((Path(file), mode, kwargs.get('encoding')))
                return real_open(file, mode, *args, **kwargs)

            with mock.patch('builtins.open', side_effect=tracking_open):
                valid, errors = validator._validate_single_file_xsd(xml_file, tmp_path)

            self.assertTrue(valid)
            self.assertEqual(errors, set())
            self.assertIn((xml_file, 'r', 'utf-8'), open_calls)


class WindowsConsoleOutputTests(unittest.TestCase):
    def _cp1252_stdout(self):
        buffer = io.BytesIO()
        stream = io.TextIOWrapper(buffer, encoding='cp1252', errors='strict')
        return buffer, stream

    def test_compare_paragraph_counts_uses_ascii_safe_arrow(self):
        with tempfile.TemporaryDirectory() as tmp:
            validator = DOCXSchemaValidator(tmp)
            validator.count_paragraphs_in_original = lambda: 3
            validator.count_paragraphs_in_unpacked = lambda: 5

            buffer, stream = self._cp1252_stdout()
            with mock.patch('sys.stdout', stream):
                validator.compare_paragraph_counts()
                stream.flush()

            output = buffer.getvalue().decode('cp1252')
            self.assertIn('Paragraphs: 3 -> 5 (+2)', output)

    def test_repair_durable_id_uses_ascii_safe_arrow(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            xml_file = tmp_path / 'word' / 'document.xml'
            xml_file.parent.mkdir(parents=True)
            xml_file.write_text(
                '<?xml version="1.0" encoding="UTF-8"?>\n'
                '<w:document xmlns:w="http://schemas.openxmlformats.org/wordprocessingml/2006/main"\n'
                '            xmlns:w16cid="http://schemas.microsoft.com/office/word/2016/wordml/cid">\n'
                '  <w:body><w:p w16cid:durableId="FFFFFFFF"/></w:body>\n'
                '</w:document>\n',
                encoding='utf-8',
            )
            validator = DOCXSchemaValidator(tmp_path)

            buffer, stream = self._cp1252_stdout()
            with mock.patch('sys.stdout', stream), mock.patch('validators.docx.random.randint', return_value=42):
                repairs = validator.repair_durableId()
                stream.flush()

            output = buffer.getvalue().decode('cp1252')
            self.assertEqual(repairs, 1)
            self.assertIn('Repaired: document.xml: durableId FFFFFFFF -> 0000002A', output)


if __name__ == '__main__':
    unittest.main()
