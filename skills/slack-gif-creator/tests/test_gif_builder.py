import tempfile
import unittest
from pathlib import Path

from PIL import Image

from core.gif_builder import GIFBuilder


class GIFBuilderTimingTests(unittest.TestCase):
    def test_removing_duplicate_frames_preserves_animation_duration(self):
        builder = GIFBuilder(width=16, height=16, fps=10)
        for color in ("red", "red", "blue"):
            builder.add_frame(Image.new("RGB", (16, 16), color))

        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "animation.gif"
            info = builder.save(path, remove_duplicates=True)

            with Image.open(path) as animation:
                durations = []
                for index in range(animation.n_frames):
                    animation.seek(index)
                    durations.append(animation.info["duration"])

        self.assertEqual(durations, [200, 100])
        self.assertAlmostEqual(info["duration_seconds"], 0.3)


if __name__ == "__main__":
    unittest.main()
