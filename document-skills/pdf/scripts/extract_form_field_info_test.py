import unittest
from unittest.mock import MagicMock, patch
from extract_form_field_info import get_full_annotation_field_id, make_field_dict, get_field_info

class TestExtractFormFieldInfo(unittest.TestCase):

    def test_get_full_annotation_field_id(self):
        # Case 1: Simple field
        ann1 = {'/T': 'field1'}
        self.assertEqual(get_full_annotation_field_id(ann1), 'field1')

        # Case 2: Nested field
        parent = {'/T': 'parent'}
        child = {'/T': 'child', '/Parent': parent}
        self.assertEqual(get_full_annotation_field_id(child), 'parent.child')

        # Case 3: Deeply nested
        grandparent = {'/T': 'gp'}
        parent = {'/T': 'p', '/Parent': grandparent}
        child = {'/T': 'c', '/Parent': parent}
        self.assertEqual(get_full_annotation_field_id(child), 'gp.p.c')

        # Case 4: No name (should handle gracefully, though unlikely for valid field)
        ann_no_name = {}
        self.assertIsNone(get_full_annotation_field_id(ann_no_name))

    def test_make_field_dict_text(self):
        field = {'/FT': '/Tx'}
        field_id = "text_field"
        result = make_field_dict(field, field_id)
        self.assertEqual(result['field_id'], field_id)
        self.assertEqual(result['type'], 'text')

    def test_make_field_dict_checkbox(self):
        field = {'/FT': '/Btn', '/_States_': ['/Off', '/Yes']}
        field_id = "cb_field"
        result = make_field_dict(field, field_id)
        self.assertEqual(result['type'], 'checkbox')
        self.assertEqual(result['checked_value'], '/Yes')
        self.assertEqual(result['unchecked_value'], '/Off')

    def test_make_field_dict_checkbox_order(self):
        # Case where /Off is second
        field = {'/FT': '/Btn', '/_States_': ['/Yes', '/Off']}
        field_id = "cb_field"
        result = make_field_dict(field, field_id)
        self.assertEqual(result['type'], 'checkbox')
        self.assertEqual(result['checked_value'], '/Yes')
        self.assertEqual(result['unchecked_value'], '/Off')

    def test_make_field_dict_choice(self):
        field = {'/FT': '/Ch', '/_States_': [['val1', 'Text1'], ['val2', 'Text2']]}
        field_id = "choice_field"
        result = make_field_dict(field, field_id)
        self.assertEqual(result['type'], 'choice')
        expected_options = [
            {"value": "val1", "text": "Text1"},
            {"value": "val2", "text": "Text2"}
        ]
        self.assertEqual(result['choice_options'], expected_options)

    def test_make_field_dict_unknown(self):
        field = {'/FT': '/Unknown'}
        field_id = "unk"
        result = make_field_dict(field, field_id)
        self.assertEqual(result['type'], 'unknown (/Unknown)')

    def test_get_field_info(self):
        mock_reader = MagicMock()

        # Mock fields
        fields = {
            "f1": {"/FT": "/Tx"},
            "f2": {"/FT": "/Btn", "/_States_": ["/Off", "/Yes"]},
            "container": {"/Kids": [1, 2]} # Should be skipped
        }
        mock_reader.get_fields.return_value = fields

        # Mock pages and annotations
        mock_page1 = MagicMock()
        # Annotation for f1
        ann1 = {"/T": "f1", "/Rect": [10, 10, 50, 50]}
        # Annotation for f2
        ann2 = {"/T": "f2", "/Rect": [60, 60, 100, 100]}

        mock_page1.get.return_value = [ann1, ann2] # Return annotations
        mock_reader.pages = [mock_page1]

        # Patch get_full_annotation_field_id to behave correctly with our dict mocks
        # Since the real function expects objects with get(), and our dicts have get(), it should work.
        # But wait, the real function traverses /Parent.
        # For this test, I'll keep it simple and not use parents in annotations, so T is enough.

        # However, get_full_annotation_field_id is used inside get_field_info.
        # It relies on .get() method.

        results = get_field_info(mock_reader)

        self.assertEqual(len(results), 2)

        # Verify f1
        f1 = next(f for f in results if f['field_id'] == 'f1')
        self.assertEqual(f1['type'], 'text')
        self.assertEqual(f1['page'], 1)
        self.assertEqual(f1['rect'], [10, 10, 50, 50])

        # Verify f2
        f2 = next(f for f in results if f['field_id'] == 'f2')
        self.assertEqual(f2['type'], 'checkbox')
        self.assertEqual(f2['page'], 1)

    def test_get_field_info_radio_group(self):
        mock_reader = MagicMock()

        # Radio buttons are Btn fields with Kids usually, but here we simulate the logic
        # where we identify radio groups via Kids and Btn type.

        # Structure:
        # Parent field "radio_grp" (FT: Btn, Kids: [...])
        # Annotations on page refer to "radio_grp" and have /AP /N states.

        fields = {
            "radio_grp": {"/FT": "/Btn", "/Kids": [MagicMock(), MagicMock()]}
        }
        mock_reader.get_fields.return_value = fields

        mock_page = MagicMock()
        # Annotation for Option 1
        ann1 = {"/T": "radio_grp", "/Rect": [10, 10, 20, 20], "/AP": {"/N": ["/Off", "/Opt1"]}}
        # Annotation for Option 2
        ann2 = {"/T": "radio_grp", "/Rect": [30, 30, 40, 40], "/AP": {"/N": ["/Off", "/Opt2"]}}

        mock_page.get.return_value = [ann1, ann2]
        mock_reader.pages = [mock_page]

        results = get_field_info(mock_reader)

        self.assertEqual(len(results), 1)
        radio = results[0]
        self.assertEqual(radio['field_id'], 'radio_grp')
        self.assertEqual(radio['type'], 'radio_group')
        self.assertEqual(len(radio['radio_options']), 2)

        opt1 = next(o for o in radio['radio_options'] if o['value'] == '/Opt1')
        self.assertEqual(opt1['rect'], [10, 10, 20, 20])

        opt2 = next(o for o in radio['radio_options'] if o['value'] == '/Opt2')
        self.assertEqual(opt2['rect'], [30, 30, 40, 40])

if __name__ == '__main__':
    unittest.main()
