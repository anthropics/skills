import importlib.util
from pathlib import Path

import numpy as np
from PIL import Image

spec = importlib.util.spec_from_file_location(
    "gif_builder", Path(__file__).resolve().parents[1] / "core/gif_builder.py"
)
gif_builder = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gif_builder)
GIFBuilder = gif_builder.GIFBuilder


def test_add_frame_snapshots_reused_array():
    builder = GIFBuilder(width=4, height=4)
    frame = np.zeros((4, 4, 3), dtype=np.uint8)

    builder.add_frame(frame)
    frame[:] = (255, 0, 0)
    builder.add_frame(frame)
    frame[:] = (0, 255, 0)

    np.testing.assert_array_equal(builder.frames[0], np.zeros((4, 4, 3), dtype=np.uint8))
    np.testing.assert_array_equal(builder.frames[1][0, 0], [255, 0, 0])
    assert not np.shares_memory(builder.frames[0], frame)
    assert not np.shares_memory(builder.frames[1], frame)


def test_add_frame_snapshots_array_view():
    builder = GIFBuilder(width=4, height=4)
    source = np.zeros((8, 8, 3), dtype=np.uint8)
    builder.add_frame(source[::2, ::2])
    source[:] = 255

    assert not builder.frames[0].any()


def test_pillow_and_resized_frames_remain_independent():
    builder = GIFBuilder(width=4, height=4)
    image = Image.new("RGB", (4, 4), "red")
    builder.add_frame(image)
    image.paste("blue", (0, 0, 4, 4))
    np.testing.assert_array_equal(builder.frames[0][0, 0], [255, 0, 0])

    resized_source = np.zeros((8, 8, 3), dtype=np.uint8)
    builder.add_frame(resized_source)
    resized_source[:] = 255
    assert not builder.frames[1].any()


def test_saved_gif_keeps_frames_from_reused_array(tmp_path):
    builder = GIFBuilder(width=4, height=4)
    frame = np.zeros((4, 4, 3), dtype=np.uint8)
    builder.add_frame(frame)
    frame[:] = (255, 0, 0)
    builder.add_frame(frame)
    frame[:] = (0, 255, 0)

    path = tmp_path / "snapshots.gif"
    builder.save(path)

    with Image.open(path) as image:
        assert image.n_frames == 2
        np.testing.assert_array_equal(np.array(image.convert("RGB"))[0, 0], [0, 0, 0])
        image.seek(1)
        np.testing.assert_array_equal(np.array(image.convert("RGB"))[0, 0], [255, 0, 0])
