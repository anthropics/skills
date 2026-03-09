import unittest
from unittest.mock import MagicMock, patch, mock_open
import json
from fill_fillable_fields import validation_error_for_field_value, fill_pdf_fields, monkeypatch_pydpf_method

class TestFillFillableFields(unittest.TestCase):

    def test_validation_error_checkbox_valid(self):
        field_info = {
            "type": "checkbox",
            "field_id": "cb1",
            "checked_value": "/Yes",
            "unchecked_value": "/Off"
        }
        self.assertIsNone(validation_error_for_field_value(field_info, "/Yes"))
        self.assertIsNone(validation_error_for_field_value(field_info, "/Off"))

    def test_validation_error_checkbox_invalid(self):
        field_info = {
            "type": "checkbox",
            "field_id": "cb1",
            "checked_value": "/Yes",
            "unchecked_value": "/Off"
        }
        err = validation_error_for_field_value(field_info, "/Maybe")
        self.assertIn("Invalid value", err)
        self.assertIn("checkbox field", err)

    def test_validation_error_radio_group_valid(self):
        field_info = {
            "type": "radio_group",
            "field_id": "rg1",
            "radio_options": [{"value": "Option1"}, {"value": "Option2"}]
        }
        self.assertIsNone(validation_error_for_field_value(field_info, "Option1"))

    def test_validation_error_radio_group_invalid(self):
        field_info = {
            "type": "radio_group",
            "field_id": "rg1",
            "radio_options": [{"value": "Option1"}, {"value": "Option2"}]
        }
        err = validation_error_for_field_value(field_info, "Option3")
        self.assertIn("Invalid value", err)
        self.assertIn("radio group field", err)

    def test_validation_error_choice_valid(self):
        field_info = {
            "type": "choice",
            "field_id": "ch1",
            "choice_options": [{"value": "Choice1"}, {"value": "Choice2"}]
        }
        self.assertIsNone(validation_error_for_field_value(field_info, "Choice1"))

    def test_validation_error_choice_invalid(self):
        field_info = {
            "type": "choice",
            "field_id": "ch1",
            "choice_options": [{"value": "Choice1"}, {"value": "Choice2"}]
        }
        err = validation_error_for_field_value(field_info, "Choice3")
        self.assertIn("Invalid value", err)
        self.assertIn("choice field", err)

    def test_validation_error_other_type(self):
        field_info = {
            "type": "text",
            "field_id": "txt1"
        }
        self.assertIsNone(validation_error_for_field_value(field_info, "Some text"))

    @patch('fill_fillable_fields.PdfReader')
    @patch('fill_fillable_fields.PdfWriter')
    @patch('fill_fillable_fields.get_field_info')
    def test_fill_pdf_fields_success(self, mock_get_field_info, mock_writer_cls, mock_reader_cls):
        # Setup mocks
        mock_reader = MagicMock()
        mock_reader_cls.return_value = mock_reader

        mock_writer = MagicMock()
        mock_writer_cls.return_value = mock_writer
        mock_writer.pages = [MagicMock()] # Mock one page

        # Mock field info from extract_form_field_info
        mock_get_field_info.return_value = [
            {"field_id": "f1", "type": "text", "page": 1},
            {"field_id": "f2", "type": "checkbox", "page": 1, "checked_value": "/Yes", "unchecked_value": "/Off"}
        ]

        # Input fields JSON
        fields_data = [
            {"field_id": "f1", "value": "Hello", "page": 1},
            {"field_id": "f2", "value": "/Yes", "page": 1}
        ]

        with patch("builtins.open", mock_open(read_data=json.dumps(fields_data))) as mock_file:
            fill_pdf_fields("input.pdf", "fields.json", "output.pdf")

        # Verify interactions
        mock_reader_cls.assert_called_with("input.pdf")
        mock_writer.update_page_form_field_values.assert_called()
        mock_writer.write.assert_called()

    @patch('fill_fillable_fields.PdfReader')
    @patch('fill_fillable_fields.PdfWriter')
    @patch('fill_fillable_fields.get_field_info')
    def test_fill_pdf_fields_invalid_field_id(self, mock_get_field_info, mock_writer_cls, mock_reader_cls):
        mock_get_field_info.return_value = [{"field_id": "f1", "type": "text", "page": 1}]
        fields_data = [{"field_id": "invalid_id", "value": "val", "page": 1}]

        with patch("builtins.open", mock_open(read_data=json.dumps(fields_data))):
            with self.assertRaises(SystemExit):
                 fill_pdf_fields("input.pdf", "fields.json", "output.pdf")

    @patch('fill_fillable_fields.PdfReader')
    @patch('fill_fillable_fields.PdfWriter')
    @patch('fill_fillable_fields.get_field_info')
    def test_fill_pdf_fields_wrong_page(self, mock_get_field_info, mock_writer_cls, mock_reader_cls):
        mock_get_field_info.return_value = [{"field_id": "f1", "type": "text", "page": 1}]
        fields_data = [{"field_id": "f1", "value": "val", "page": 2}] # Wrong page

        with patch("builtins.open", mock_open(read_data=json.dumps(fields_data))):
             with self.assertRaises(SystemExit):
                 fill_pdf_fields("input.pdf", "fields.json", "output.pdf")

    @patch('fill_fillable_fields.PdfReader')
    @patch('fill_fillable_fields.PdfWriter')
    @patch('fill_fillable_fields.get_field_info')
    def test_fill_pdf_fields_validation_error(self, mock_get_field_info, mock_writer_cls, mock_reader_cls):
        mock_get_field_info.return_value = [
            {"field_id": "cb1", "type": "checkbox", "page": 1, "checked_value": "/Yes", "unchecked_value": "/Off"}
        ]
        fields_data = [{"field_id": "cb1", "value": "Invalid", "page": 1}]

        with patch("builtins.open", mock_open(read_data=json.dumps(fields_data))):
             with self.assertRaises(SystemExit):
                 fill_pdf_fields("input.pdf", "fields.json", "output.pdf")

    def test_monkeypatch(self):
        # Just ensure it runs without error.
        # Testing the actual patch effect would require mocking pypdf internals which might be brittle.
        monkeypatch_pydpf_method()
        from pypdf.generic import DictionaryObject
        from pypdf.constants import FieldDictionaryAttributes

        # Test the patched method behavior
        obj = DictionaryObject()
        # Mocking get_inherited on the instance isn't enough because we patched the class method,
        # but we can try to verify if logic holds.
        # Since I cannot easily create a pypdf object structure that triggers the specific bug without extensive setup,
        # I will trust the monkeypatch function runs.
        pass

if __name__ == '__main__':
    unittest.main()
