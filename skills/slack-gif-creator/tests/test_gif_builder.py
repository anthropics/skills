"""Regression tests for GIFBuilder.save() (anthropics/skills #2176).

Saving must never change the builder's stored frames or dimensions, so a
builder can be saved more than once, with different settings each time,
and every save starts from the frames that were added.
"""

import sys
from pathlib import Path

import imageio.v3 as imageio
import numpy as np
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from core.gif_builder import GIFBuilder  # noqa: E402


def make_builder(width=160, height=160, count=16, seed=0):
    rng = np.random.default_rng(seed)
    builder = GIFBuilder(width=width, height=height, fps=15)
    for _ in range(count):
        builder.add_frame(rng.integers(0, 255, (height, width, 3), dtype=np.uint8))
    return builder


def read_gif(path):
    frames = imageio.imread(path)
    return frames.shape


def test_second_save_after_emoji_save_reproduces_original(tmp_path):
    builder = make_builder(count=24)
    emoji_info = builder.save(tmp_path / "emoji.gif", optimize_for_emoji=True)

    assert emoji_info["dimensions"] == "128x128"
    assert emoji_info["frame_count"] == 12
    assert (builder.width, builder.height) == (160, 160)
    assert len(builder.frames) == 24

    message_info = builder.save(tmp_path / "message.gif")
    assert message_info["dimensions"] == "160x160"
    assert message_info["frame_count"] == 24
    assert read_gif(tmp_path / "message.gif") == (24, 160, 160, 3)


def test_second_save_after_remove_duplicates_keeps_all_frames(tmp_path):
    builder = GIFBuilder(width=64, height=64, fps=15)
    # Near-identical frames: each differs from the last only in a small
    # block, so the dedupe pass (threshold 0.9995) removes all but the
    # first, while the block stays visible enough for the GIF to store
    # all of them on the second save.
    base = np.full((64, 64, 3), 128, dtype=np.uint8)
    for i in range(6):
        frame = base.copy()
        frame[10:15, 10:15] = 128 + i * 3
        builder.add_frame(frame)

    deduped_info = builder.save(tmp_path / "deduped.gif", remove_duplicates=True)
    assert deduped_info["frame_count"] == 1
    assert len(builder.frames) == 6

    full_info = builder.save(tmp_path / "full.gif")
    assert full_info["frame_count"] == 6


def test_save_with_different_settings_after_first_save(tmp_path):
    builder = make_builder()
    first = builder.save(tmp_path / "first.gif", optimize_for_emoji=True)
    assert first["dimensions"] == "128x128"

    second = builder.save(tmp_path / "second.gif", num_colors=64)
    assert second["dimensions"] == "160x160"
    assert second["frame_count"] == 16
    assert second["colors"] == 64
    assert read_gif(tmp_path / "second.gif") == (16, 160, 160, 3)

    third = builder.save(tmp_path / "third.gif", optimize_for_emoji=True)
    assert third["dimensions"] == "128x128"
    assert (builder.width, builder.height) == (160, 160)
    assert len(builder.frames) == 16


def test_deduplicate_frames_still_removes_duplicates_when_called_directly():
    builder = GIFBuilder(width=64, height=64, fps=15)
    frame = np.full((64, 64, 3), 200, dtype=np.uint8)
    for _ in range(4):
        builder.add_frame(frame.copy())

    assert builder.deduplicate_frames() == 3
    assert len(builder.frames) == 1
