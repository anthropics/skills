import unittest

from PIL import Image, ImageChops, ImageDraw, ImageFont

from core.frame_composer import draw_text


class CenteredTextTests(unittest.TestCase):
    def assert_text_centered(self, text):
        position = (64, 64)
        background = Image.new("RGB", (128, 128), "white")
        frame = background.copy()
        draw_text(frame, text, position, centered=True)

        # Center the native text-bounds crop, preserving any whitespace inside
        # the font's layout box (the bitmap default differs from TrueType).
        native = background.copy()
        draw = ImageDraw.Draw(native)
        font = ImageFont.load_default()
        draw.text((0, 0), text, font=font, fill="black")
        caption = native.crop(draw.textbbox((0, 0), text, font=font))
        expected = background.copy()
        expected.paste(caption, (
            (expected.width - caption.width + 1) // 2,
            (expected.height - caption.height + 1) // 2,
        ))
        self.assertIsNone(ImageChops.difference(frame, expected).getbbox())

    def test_centers_text_with_descenders(self):
        self.assert_text_centered("gyp")

    def test_centers_multiline_caption(self):
        self.assert_text_centered("Hello\nSlack")


if __name__ == "__main__":
    unittest.main()
