"""Regression tests for issue #1886.

GIFBuilder.add_frame() promises its argument "will be converted to RGB"
but only the PIL.Image branch converted: a numpy RGBA or greyscale
array was stored as-is, and save() then crashed in optimize_colors()
(reshape to (-1, 3), palette quantize) or in deduplicate_frames()
(broadcasting (h, w, 3) against (h, w, 4)) — 45-130 lines below the
call the caller actually made.

Every stored frame must be an RGB ndarray with shape (height, width, 3).
Run from the repo root or from skills/slack-gif-creator:

    python -m pytest skills/slack-gif-creator/tests/test_gif_builder.py -v
"""

import sys
from pathlib import Path

import imageio.v3 as imageio
import numpy as np
import pytest
from PIL import Image

SKILL_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SKILL_ROOT))

from core.gif_builder import GIFBuilder  # noqa: E402


def make_rgb(h=120, w=120, color=(40, 120, 200)):
    return np.full((h, w, 3), color, dtype=np.uint8)


def make_rgba(h=120, w=120, color=(40, 120, 200), alpha=255):
    rgb = make_rgb(h, w, color)
    a = np.full((h, w, 1), alpha, dtype=np.uint8)
    return np.concatenate([rgb, a], axis=-1)


def varying_frames(kind, n=10, h=120, w=120):
    """Frames that actually differ from each other per index — a GIF
    of ten byte-identical frames reads back as fewer frames, so the
    save tests animate the colour instead (like the issue's repro)."""
    out = []
    for i in range(n):
        # Each frame must be spatially distinct, not just a different
        # solid colour: the GIF encoder merges consecutive frames that
        # are identical after palette quantization, so a plain colour
        # ramp reads back as fewer frames. A moving red block (like
        # the issue's sliding-disc repro) keeps every frame distinct.
        color = (i * 25, 120, 255 - i * 25)
        if kind == "rgb":
            frame = make_rgb(h, w, color)
        elif kind == "rgba":
            frame = make_rgba(h, w, color)
        elif kind == "grey":
            frame = np.full((h, w), 25 + i * 25, dtype=np.uint8)
        pos = i * 10
        if kind == "rgba":
            frame[pos:pos + 20, pos:pos + 20] = (220, 40, 40, 255)
        elif kind == "grey":
            frame[pos:pos + 20, pos:pos + 20] = 0
        else:
            frame[pos:pos + 20, pos:pos + 20] = (220, 40, 40)
        out.append(frame)
    return out


def make_grey(h=128, w=128, value=128):
    return np.full((h, w), value, dtype=np.uint8)


def pil_rgb_of(frame):
    """The conversion the PIL branch already performs."""
    return np.array(Image.fromarray(frame).convert("RGB"))


def save_and_decode(builder, tmp_path, name="out.gif", **kwargs):
    out = tmp_path / name
    info = builder.save(out, **kwargs)
    assert out.exists() and out.stat().st_size > 0
    frames = imageio.imread(out, index=None)
    return info, frames


# --- The invariant: every stored frame is (height, width, 3) ---


def test_rgb_ndarray_stored_unchanged():
    frame = make_rgb()
    builder = GIFBuilder(120, 120)
    builder.add_frame(frame)
    stored = builder.frames[-1]
    assert stored.shape == (120, 120, 3)
    assert stored.dtype == np.uint8
    np.testing.assert_array_equal(stored, frame)


def test_rgba_ndarray_normalised_to_rgb():
    frame = make_rgba()
    builder = GIFBuilder(120, 120)
    builder.add_frame(frame)
    stored = builder.frames[-1]
    assert stored.shape == (120, 120, 3)
    assert stored.dtype == np.uint8
    np.testing.assert_array_equal(stored, pil_rgb_of(frame))


def test_greyscale_ndarray_normalised_to_rgb():
    frame = make_grey()
    builder = GIFBuilder(128, 128)
    builder.add_frame(frame)
    stored = builder.frames[-1]
    assert stored.shape == (128, 128, 3)
    assert stored.dtype == np.uint8
    np.testing.assert_array_equal(stored, pil_rgb_of(frame))


def test_greyscale_width_three_not_mistaken_for_rgb():
    """A 2-D greyscale array of shape (height, 3) must not pass as RGB:
    the check must be on dimensionality, not just the last axis."""
    frame = np.full((128, 3), 200, dtype=np.uint8)
    builder = GIFBuilder(width=3, height=128)
    builder.add_frame(frame)
    stored = builder.frames[-1]
    assert stored.shape == (128, 3, 3)
    np.testing.assert_array_equal(stored, pil_rgb_of(frame))


def test_partial_alpha_matches_pil_path():
    rgba = make_rgba()
    rgba[:60, :, 3] = 0  # fully transparent top half
    rgba[60:, :, 3] = 128  # semi-transparent bottom half
    builder = GIFBuilder(120, 120)
    builder.add_frame(rgba)
    stored = builder.frames[-1]
    assert stored.shape == (120, 120, 3)
    # Alpha is discarded, exactly as the PIL branch does — no compositing.
    np.testing.assert_array_equal(stored, pil_rgb_of(rgba))
    # And the ndarray path agrees with the PIL path for the same pixels.
    pil_builder = GIFBuilder(120, 120)
    pil_builder.add_frame(Image.fromarray(rgba))
    np.testing.assert_array_equal(stored, pil_builder.frames[-1])


def test_rgba_resized_after_normalisation():
    frame = make_rgba(h=160, w=160)
    builder = GIFBuilder(120, 120)
    builder.add_frame(frame)
    stored = builder.frames[-1]
    assert stored.shape == (120, 120, 3)
    expected = np.array(
        Image.fromarray(frame).convert("RGB").resize((120, 120), Image.Resampling.LANCZOS)
    )
    np.testing.assert_array_equal(stored, expected)


def test_pil_rgba_and_l_still_convert():
    builder = GIFBuilder(120, 120)
    builder.add_frame(Image.fromarray(make_rgba()))
    assert builder.frames[-1].shape == (120, 120, 3)
    builder.add_frame(Image.fromarray(make_grey(h=120, w=120)))
    assert builder.frames[-1].shape == (120, 120, 3)


# --- Real GIFs: save() is where the failures actually happened ---


def test_save_rgba_128x128(tmp_path):
    builder = GIFBuilder(128, 128)
    builder.add_frames(varying_frames("rgba", h=128, w=128))
    info, frames = save_and_decode(builder, tmp_path, num_colors=48)
    assert info["frame_count"] == 10
    assert frames.shape[0] == 10


def test_save_rgba_120x120(tmp_path):
    builder = GIFBuilder(120, 120)
    builder.add_frames(varying_frames("rgba"))
    info, frames = save_and_decode(builder, tmp_path, num_colors=48)
    assert info["frame_count"] == 10
    assert frames.shape[0] == 10


def test_save_greyscale_128x128(tmp_path):
    builder = GIFBuilder(128, 128)
    builder.add_frames(varying_frames("grey", h=128, w=128))
    info, frames = save_and_decode(builder, tmp_path, num_colors=48)
    assert info["frame_count"] == 10
    assert frames.shape[0] == 10


def test_save_mixed_rgb_rgba_with_dedup(tmp_path):
    rgb = make_rgb(h=128, w=128)
    rgba = np.concatenate([rgb, np.full((128, 128, 1), 255, dtype=np.uint8)], axis=-1)
    different = make_rgb(h=128, w=128, color=(200, 40, 40))
    builder = GIFBuilder(128, 128)
    builder.add_frame(rgb)
    builder.add_frame(rgba)  # same pixels, different channel count
    builder.add_frame(different)
    info, frames = save_and_decode(
        builder, tmp_path, num_colors=48, remove_duplicates=True
    )
    # The RGB/RGBA pair is one duplicate; the different frame survives.
    assert info["frame_count"] == 2
    assert frames.shape[0] == 2


def test_save_rgba_emoji_480x480(tmp_path):
    builder = GIFBuilder(480, 480)
    builder.add_frames(varying_frames("rgba", n=3, h=480, w=480))
    info, frames = save_and_decode(
        builder, tmp_path, num_colors=48, optimize_for_emoji=True
    )
    assert info["frame_count"] == 3
    assert frames.shape[0] == 3


def test_save_single_frame_rgba(tmp_path):
    builder = GIFBuilder(128, 128)
    builder.add_frame(make_rgba(h=128, w=128))
    info, frames = save_and_decode(builder, tmp_path, num_colors=48)
    assert info["frame_count"] == 1
    assert frames.shape[0] == 1


def test_save_rgb_and_pil_controls(tmp_path):
    builder = GIFBuilder(120, 120)
    builder.add_frames(varying_frames("rgb"))
    info, frames = save_and_decode(builder, tmp_path, "rgb.gif", num_colors=48)
    assert info["frame_count"] == 10
    pil_builder = GIFBuilder(120, 120)
    for frame in varying_frames("rgba"):
        pil_builder.add_frame(Image.fromarray(frame))
    info, frames = save_and_decode(pil_builder, tmp_path, "pil.gif", num_colors=48)
    assert info["frame_count"] == 10
