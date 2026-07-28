import unittest

from extract_form_field_info import make_field_dict


class ChoiceOptionTests(unittest.TestCase):
    def test_bare_string_options_preserve_value_and_label(self):
        field = {"/FT": "/Ch", "/_States_": ["Red", "B"]}

        self.assertEqual(
            make_field_dict(field, "colors")["choice_options"],
            [
                {"value": "Red", "text": "Red"},
                {"value": "B", "text": "B"},
            ],
        )

    def test_value_label_pairs_remain_supported(self):
        field = {"/FT": "/Ch", "/_States_": [["r", "Red"]]}

        self.assertEqual(
            make_field_dict(field, "colors")["choice_options"],
            [{"value": "r", "text": "Red"}],
        )


if __name__ == "__main__":
    unittest.main()
