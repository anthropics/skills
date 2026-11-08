"""Regression tests for validators.py (E722 narrowing + duration fallback).

Covers PR: bare ``except:`` -> ``except Exception:`` in the GIF duration
fallback. A bare except also swallows KeyboardInterrupt/SystemExit.
"""
import sys
from pathlib import Path
from unittest import mock

import pytest
from PIL import Image

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "core"))

from validators import validate_gif


def _make_gif(path: Path, size=(128, 128), frames=3) -> Path:
    imgs = [Image.new("RGB", size, (c * 80 % 256, 40, 120)) for c in range(frames)]
    imgs[0].save(path, save_all=True, append_images=imgs[1:],
                 duration=120, loop=0)
    return path


def test_keyboard_interrupt_propagates(tmp_path):
    """KeyboardInterrupt during duration read must propagate, not vanish."""
    gif = _make_gif(tmp_path / "t.gif")

    real_open = Image.open

    class BoomDict(dict):
        def get(self, *a, **k):
            raise KeyboardInterrupt()

    class BoomImage:
        def __init__(self, *a, **k):
            self._img = real_open(*a, **k)
            self.size = self._img.size
            self.info = BoomDict()

        def __enter__(self):
            return self

        def __exit__(self, *a):
            self._img.close()
            return False

        def seek(self, i):
            return self._img.seek(i)

    with mock.patch("PIL.Image.open", BoomImage):
        with pytest.raises(KeyboardInterrupt):
            validate_gif(gif, verbose=False)


def test_happy_path_frames_and_duration(tmp_path):
    """Normal GIFs validate with correct frame stats (no behavior change)."""
    gif = _make_gif(tmp_path / "ok.gif", frames=3)
    passes, results = validate_gif(gif, verbose=False)
    assert isinstance(passes, bool)
    assert results["frame_count"] == 3
    assert results["duration_seconds"] == pytest.approx(0.36, abs=0.05)


def test_missing_file():
    passes, results = validate_gif("/nonexistent/x.gif", verbose=False)
    assert passes is False
    assert "error" in results
