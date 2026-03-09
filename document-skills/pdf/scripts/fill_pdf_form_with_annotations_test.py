import unittest
from unittest.mock import MagicMock, patch, mock_open
import json
from fill_pdf_form_with_annotations import transform_coordinates, fill_pdf_form

class TestFillPdfFormWithAnnotations(unittest.TestCase):

    def test_transform_coordinates(self):
        # 100x100 image, 200x200 pdf.
        # Scale factor is 2.
        # Y is flipped.

        # bbox: left=10, top=10, right=20, bottom=20
        # Image coordinates y increases downward.
        # PDF coordinates y increases upward.

        # input y=10 -> pdf y = 200 - 10*2 = 180
        # input y=20 -> pdf y = 200 - 20*2 = 160

        # expected: left=20, bottom=160, right=40, top=180

        bbox = [10, 10, 20, 20]
        result = transform_coordinates(bbox, 100, 100, 200, 200)
        self.assertEqual(result, (20.0, 160.0, 40.0, 180.0))

    @patch('fill_pdf_form_with_annotations.PdfReader')
    @patch('fill_pdf_form_with_annotations.PdfWriter')
    @patch('fill_pdf_form_with_annotations.FreeText')
    def test_fill_pdf_form(self, mock_free_text, mock_writer_cls, mock_reader_cls):
        mock_reader = MagicMock()
        mock_writer = MagicMock()
        mock_reader_cls.return_value = mock_reader
        mock_writer_cls.return_value = mock_writer

        # Mock page dimensions
        page1 = MagicMock()
        page1.mediabox.width = 100
        page1.mediabox.height = 100
        mock_reader.pages = [page1]

        fields_data = {
            "pages": [
                {"page_number": 1, "image_width": 100, "image_height": 100}
            ],
            "form_fields": [
                {
                    "page_number": 1,
                    "entry_bounding_box": [10, 10, 50, 50],
                    "entry_text": {"text": "Filled Value", "font_size": 12}
                },
                {
                    "page_number": 1,
                    "entry_bounding_box": [0,0,1,1]
                    # Missing entry_text, should be skipped
                }
            ]
        }

        with patch("builtins.open", mock_open(read_data=json.dumps(fields_data))):
            fill_pdf_form("input.pdf", "fields.json", "output.pdf")

        # Verify reader usage
        mock_reader_cls.assert_called_with("input.pdf")

        # Verify writer usage
        mock_writer.append.assert_called_with(mock_reader)

        # Verify annotation creation
        # One valid field
        self.assertEqual(mock_free_text.call_count, 1)
        args, kwargs = mock_free_text.call_args
        self.assertEqual(kwargs['text'], "Filled Value")

        # Verify annotation added to writer
        mock_writer.add_annotation.assert_called()
        self.assertEqual(mock_writer.add_annotation.call_count, 1)

        # Verify output written
        mock_writer.write.assert_called()

    @patch('fill_pdf_form_with_annotations.PdfReader')
    @patch('fill_pdf_form_with_annotations.PdfWriter')
    @patch('fill_pdf_form_with_annotations.FreeText')
    def test_fill_pdf_form_empty_text(self, mock_free_text, mock_writer_cls, mock_reader_cls):
        mock_reader = MagicMock()
        mock_writer = MagicMock()
        mock_reader_cls.return_value = mock_reader
        mock_writer_cls.return_value = mock_writer

        page1 = MagicMock()
        page1.mediabox.width = 100
        page1.mediabox.height = 100
        mock_reader.pages = [page1]

        fields_data = {
            "pages": [{"page_number": 1, "image_width": 100, "image_height": 100}],
            "form_fields": [
                {
                    "page_number": 1,
                    "entry_bounding_box": [10, 10, 50, 50],
                    "entry_text": {"text": ""} # Empty text
                }
            ]
        }

        with patch("builtins.open", mock_open(read_data=json.dumps(fields_data))):
            fill_pdf_form("input.pdf", "fields.json", "output.pdf")

        # Should create no annotations
        mock_free_text.assert_not_called()
        mock_writer.add_annotation.assert_not_called()

if __name__ == '__main__':
    unittest.main()
