import unittest
from types import SimpleNamespace

from pptx.enum.shapes import PP_PLACEHOLDER

from skills.pptx.scripts.slide_text import _shape


def text_shape(placeholder_type, index, text="Example"):
    return SimpleNamespace(
        _element=SimpleNamespace(
            tag="{http://schemas.openxmlformats.org/presentationml/2006/main}sp"
        ),
        has_table=False,
        has_chart=False,
        has_text_frame=True,
        is_placeholder=True,
        placeholder_format=SimpleNamespace(type=placeholder_type, idx=index),
        text_frame=SimpleNamespace(text=text),
    )


class SlideTextTests(unittest.TestCase):
    def test_nonzero_title_placeholder_is_a_heading(self):
        shape = text_shape(PP_PLACEHOLDER.TITLE, 100, "Quarterly Results")

        self.assertEqual(_shape(shape), ["# Quarterly Results"])

    def test_nonzero_center_title_placeholder_is_a_heading(self):
        shape = text_shape(PP_PLACEHOLDER.CENTER_TITLE, 100, "Quarterly Results")

        self.assertEqual(_shape(shape), ["# Quarterly Results"])

    def test_zero_index_body_placeholder_is_not_a_heading(self):
        shape = text_shape(PP_PLACEHOLDER.BODY, 0, "Revenue grew 25%")

        self.assertEqual(_shape(shape), ["Revenue grew 25%"])


if __name__ == "__main__":
    unittest.main()
