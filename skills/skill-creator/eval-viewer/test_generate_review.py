"""Regression tests for the self-contained eval review page."""

import json
import unittest

from generate_review import generate_html, json_for_inline_script


class InlineScriptSerializationTests(unittest.TestCase):
    def test_script_closing_sequence_is_escaped_without_changing_data(self) -> None:
        value = {"content": "</script><script>alert('xss')</script>&"}

        serialized = json_for_inline_script(value)

        self.assertNotIn("<", serialized)
        self.assertNotIn(">", serialized)
        self.assertNotIn("&", serialized)
        self.assertEqual(json.loads(serialized), value)

    def test_generated_html_does_not_embed_untrusted_script_markup(self) -> None:
        payload = "</script><script>alert('xss')</script>"

        html = generate_html(
            runs=[{"id": "run-1", "prompt": payload, "outputs": []}],
            skill_name=payload,
        )

        self.assertNotIn(payload, html)
        self.assertIn("\\u003c/script\\u003e", html)


if __name__ == "__main__":
    unittest.main()
