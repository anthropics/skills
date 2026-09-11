# Test Implementation Examples - Getting Started

This document provides concrete test examples that can be implemented immediately to begin improving test coverage.

## 1. Slack GIF Creator - Easing Functions Tests

**File:** `skills/slack-gif-creator/core/easing.py`

### Example Test File: `tests/test_easing.py`

```python
"""Tests for easing functions - animation timing."""

import math
import pytest
from skills.slack_gif_creator.core.easing import (
    linear, ease_in_quad, ease_out_quad, ease_in_out_quad,
    ease_in_cubic, ease_out_cubic, ease_in_out_cubic,
    ease_in_bounce, ease_out_bounce, ease_in_out_bounce,
    ease_in_elastic, ease_out_elastic, ease_in_out_elastic,
    ease_back_in, ease_back_out, ease_back_in_out,
    interpolate, get_easing, apply_squash_stretch,
    calculate_arc_motion, EASING_FUNCTIONS
)


class TestEasingBounds:
    """All easing functions should return values in [0, 1]."""
    
    @pytest.mark.parametrize("t_value", [0, 0.1, 0.25, 0.5, 0.75, 0.9, 1.0])
    @pytest.mark.parametrize("func_name", list(EASING_FUNCTIONS.keys()))
    def test_easing_bounds(self, func_name, t_value):
        """Easing function should return value in [0, 1] for t in [0, 1]."""
        easing_func = EASING_FUNCTIONS[func_name]
        result = easing_func(t_value)
        
        assert isinstance(result, (int, float)), \
            f"{func_name} returned {type(result)}"
        assert 0 <= result <= 1.01, \
            f"{func_name}({t_value}) = {result}, out of bounds"


class TestEasingMonotonicity:
    """Easing functions should generally increase monotonically."""
    
    def test_linear_is_monotonic(self):
        """Linear easing must be perfectly linear."""
        prev = -1
        for t in [0, 0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9, 1.0]:
            result = linear(t)
            assert result >= prev, f"Linear not monotonic at t={t}"
            assert abs(result - t) < 0.0001
            prev = result
    
    def test_ease_in_quad_is_monotonic(self):
        """Ease in quad should increase smoothly."""
        prev = -1
        for t in [i / 10 for i in range(11)]:
            result = ease_in_quad(t)
            assert result >= prev - 0.0001, f"ease_in_quad not monotonic at t={t}"
            prev = result
    
    def test_ease_out_quad_is_monotonic(self):
        """Ease out quad should increase smoothly."""
        prev = -1
        for t in [i / 10 for i in range(11)]:
            result = ease_out_quad(t)
            assert result >= prev - 0.0001, f"ease_out_quad not monotonic at t={t}"
            prev = result


class TestEasingEndpoints:
    """All easing functions should start at 0 and end at 1."""
    
    @pytest.mark.parametrize("func_name", list(EASING_FUNCTIONS.keys()))
    def test_easing_start_is_zero(self, func_name):
        """Easing function should return ~0 at t=0."""
        easing_func = EASING_FUNCTIONS[func_name]
        result = easing_func(0)
        assert abs(result - 0) < 0.0001, \
            f"{func_name}(0) = {result}, expected 0"
    
    @pytest.mark.parametrize("func_name", list(EASING_FUNCTIONS.keys()))
    def test_easing_end_is_one(self, func_name):
        """Easing function should return ~1 at t=1."""
        easing_func = EASING_FUNCTIONS[func_name]
        result = easing_func(1)
        assert abs(result - 1) < 0.0001, \
            f"{func_name}(1) = {result}, expected 1"


class TestSpecificEasing:
    """Test behavior of specific easing functions."""
    
    def test_ease_in_quad_acceleration(self):
        """Ease in quad should accelerate (second derivative > 0)."""
        # At t=0.5, ease_in_quad(0.5) should be 0.25 (not linear 0.5)
        result = ease_in_quad(0.5)
        assert result == pytest.approx(0.25)
    
    def test_ease_out_quad_deceleration(self):
        """Ease out quad should decelerate (second derivative < 0)."""
        # At t=0.5, ease_out_quad(0.5) should be 0.75 (not linear 0.5)
        result = ease_out_quad(0.5)
        assert result == pytest.approx(0.75)
    
    def test_ease_in_out_quad_symmetry(self):
        """Ease in out should be symmetric around t=0.5."""
        t1, t2 = 0.25, 0.75
        result1 = ease_in_out_quad(t1)
        result2 = ease_in_out_quad(t2)
        # result2 should be 1 - result1
        assert result2 == pytest.approx(1 - result1, abs=0.0001)
    
    def test_ease_in_bounce_returns_valid(self):
        """Bounce easing should still stay in bounds."""
        for t in [0, 0.1, 0.2, 0.5, 0.9, 1.0]:
            result = ease_in_bounce(t)
            assert -0.01 <= result <= 1.01


class TestInterpolation:
    """Test interpolation between values."""
    
    def test_interpolate_linear_at_zero(self):
        """At t=0, interpolate should return start value."""
        result = interpolate(10, 20, 0, "linear")
        assert result == pytest.approx(10)
    
    def test_interpolate_linear_at_one(self):
        """At t=1, interpolate should return end value."""
        result = interpolate(10, 20, 1, "linear")
        assert result == pytest.approx(20)
    
    def test_interpolate_linear_at_half(self):
        """At t=0.5, interpolate should return midpoint."""
        result = interpolate(10, 20, 0.5, "linear")
        assert result == pytest.approx(15)
    
    def test_interpolate_with_easing(self):
        """Interpolate with easing should differ from linear."""
        linear_result = interpolate(0, 100, 0.5, "linear")
        quad_result = interpolate(0, 100, 0.5, "ease_in")
        
        # ease_in at t=0.5 should give 25 (t*t=0.25)
        assert quad_result == pytest.approx(25)
        assert linear_result != quad_result


class TestSquashStretch:
    """Test squash and stretch transformations."""
    
    def test_squash_stretch_vertical(self):
        """Vertical squeeze should compress height, expand width."""
        base = (1.0, 1.0)
        width, height = apply_squash_stretch(base, 1.0, "vertical")
        
        assert height < 1.0, "Vertical squeeze should reduce height"
        assert width > 1.0, "Vertical squeeze should increase width"
    
    def test_squash_stretch_horizontal(self):
        """Horizontal squeeze should compress width, expand height."""
        base = (1.0, 1.0)
        width, height = apply_squash_stretch(base, 1.0, "horizontal")
        
        assert width < 1.0, "Horizontal squeeze should reduce width"
        assert height > 1.0, "Horizontal squeeze should increase height"
    
    def test_squash_stretch_zero_intensity(self):
        """Zero intensity should not change scales."""
        base = (1.5, 2.0)
        result = apply_squash_stretch(base, 0.0, "vertical")
        assert result == pytest.approx(base)
    
    def test_squash_stretch_preserves_volume_vertically(self):
        """Vertical squash should approximately preserve volume."""
        base = (1.0, 1.0)
        width, height = apply_squash_stretch(base, 0.5, "vertical")
        
        volume_change = (width * height) / (base[0] * base[1])
        # Should be close to 1.0 (volume preserved)
        assert 0.8 < volume_change < 1.2


class TestArcMotion:
    """Test parabolic motion calculation."""
    
    def test_arc_motion_start(self):
        """At t=0, should return start position."""
        start, end = (0, 0), (10, 0)
        x, y = calculate_arc_motion(start, end, 5, 0)
        assert x == pytest.approx(0)
        assert y == pytest.approx(0)
    
    def test_arc_motion_end(self):
        """At t=1, should return end position."""
        start, end = (0, 0), (10, 0)
        x, y = calculate_arc_motion(start, end, 5, 1)
        assert x == pytest.approx(10)
        assert y == pytest.approx(0)
    
    def test_arc_motion_middle(self):
        """At t=0.5, should be at midpoint with arc offset."""
        start, end = (0, 0), (10, 0)
        x, y = calculate_arc_motion(start, end, 5, 0.5)
        
        # x should be at midpoint
        assert x == pytest.approx(5)
        # y should be at peak (height = 5 * 4 * 0.5 * 0.5 = 5)
        assert y == pytest.approx(-5)  # Negative because we subtract arc_offset
    
    def test_arc_motion_height_effect(self):
        """Greater height should increase arc amplitude."""
        start, end = (0, 0), (10, 0)
        
        _, y1 = calculate_arc_motion(start, end, 3, 0.5)
        _, y2 = calculate_arc_motion(start, end, 6, 0.5)
        
        # Greater height should mean greater arc
        assert abs(y2) > abs(y1)


class TestGetEasing:
    """Test easing function lookup."""
    
    def test_get_easing_existing(self):
        """Should return correct easing function."""
        func = get_easing("linear")
        assert func(0.5) == 0.5
    
    def test_get_easing_invalid_default(self):
        """Should default to linear for invalid names."""
        func = get_easing("nonexistent_easing")
        assert func(0.5) == 0.5  # Linear
    
    def test_get_easing_all_names(self):
        """All registered easing names should return valid functions."""
        for name in EASING_FUNCTIONS:
            func = get_easing(name)
            result = func(0.5)
            assert 0 <= result <= 1


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
```

### Running These Tests

```bash
# Install pytest
pip install pytest pytest-cov

# Run tests
pytest tests/test_easing.py -v

# Run with coverage
pytest tests/test_easing.py --cov=skills.slack_gif_creator.core.easing --cov-report=html
```

### Expected Coverage

- **Lines:** ~95%+ (easing.py is 234 LOC)
- **Functions:** 100% of EASING_FUNCTIONS will be called
- **Branches:** ~90%+

---

## 2. Slack GIF Creator - Validators Tests

**File:** `skills/slack-gif-creator/core/validators.py`

### Example Test File: `tests/test_validators.py`

```python
"""Tests for GIF validation."""

import pytest
import tempfile
from pathlib import Path
from PIL import Image
import io

from skills.slack_gif_creator.core.validators import (
    validate_gif, is_slack_ready
)


class TestValidateGifBasic:
    """Test basic GIF validation."""
    
    def create_test_gif(self, width=128, height=128, frames=5, duration=100):
        """Create a test GIF with specified properties."""
        images = []
        for i in range(frames):
            img = Image.new("RGB", (width, height), color=(i*50 % 256, 100, 200))
            images.append(img)
        
        # Save to temporary file
        with tempfile.NamedTemporaryFile(suffix=".gif", delete=False) as f:
            images[0].save(
                f.name,
                save_all=True,
                append_images=images[1:],
                duration=duration,
                loop=0
            )
            return Path(f.name)
    
    def test_validate_gif_file_not_found(self):
        """Should return False for non-existent files."""
        passes, results = validate_gif("/nonexistent/file.gif", verbose=False)
        
        assert passes is False
        assert "error" in results
        assert "File not found" in results["error"]
    
    def test_validate_gif_emoji_optimal(self):
        """Should validate optimal emoji dimensions (128x128)."""
        gif_path = self.create_test_gif(128, 128)
        
        try:
            passes, results = validate_gif(gif_path, is_emoji=True, verbose=False)
            
            assert passes is True
            assert results["width"] == 128
            assert results["height"] == 128
            assert results["optimal"] is True
            assert results["is_emoji"] is True
        finally:
            gif_path.unlink()
    
    def test_validate_gif_emoji_acceptable(self):
        """Should validate acceptable emoji dimensions (64-128)."""
        gif_path = self.create_test_gif(96, 96)
        
        try:
            passes, results = validate_gif(gif_path, is_emoji=True, verbose=False)
            
            assert passes is True
            assert results["optimal"] is False  # Not 128x128
            assert results["width"] == 96
        finally:
            gif_path.unlink()
    
    def test_validate_gif_emoji_too_small(self):
        """Should reject emoji < 64x64."""
        gif_path = self.create_test_gif(48, 48)
        
        try:
            passes, results = validate_gif(gif_path, is_emoji=True, verbose=False)
            
            assert passes is False
            assert results["width"] == 48
        finally:
            gif_path.unlink()
    
    def test_validate_gif_emoji_too_large(self):
        """Should reject emoji > 128x128."""
        gif_path = self.create_test_gif(256, 256)
        
        try:
            passes, results = validate_gif(gif_path, is_emoji=True, verbose=False)
            
            assert passes is False
        finally:
            gif_path.unlink()
    
    def test_validate_gif_message_dimensions(self):
        """Should validate message GIF dimensions."""
        gif_path = self.create_test_gif(640, 480)
        
        try:
            passes, results = validate_gif(gif_path, is_emoji=False, verbose=False)
            
            assert passes is True
            assert results["is_emoji"] is False
        finally:
            gif_path.unlink()
    
    def test_validate_gif_frame_count(self):
        """Should correctly count frames."""
        gif_path = self.create_test_gif(128, 128, frames=10)
        
        try:
            passes, results = validate_gif(gif_path, verbose=False)
            
            assert results["frame_count"] == 10
        finally:
            gif_path.unlink()
    
    def test_validate_gif_fps_calculation(self):
        """Should calculate FPS from duration."""
        # Create GIF with 10 frames, 100ms each = 1 second total = 10 fps
        gif_path = self.create_test_gif(128, 128, frames=10, duration=100)
        
        try:
            passes, results = validate_gif(gif_path, verbose=False)
            
            assert results["frame_count"] == 10
            assert results["fps"] == pytest.approx(10, abs=0.1)
            assert results["duration_seconds"] == pytest.approx(1.0, abs=0.1)
        finally:
            gif_path.unlink()
    
    def test_validate_gif_file_size(self):
        """Should report file size in KB and MB."""
        gif_path = self.create_test_gif(128, 128)
        
        try:
            passes, results = validate_gif(gif_path, verbose=False)
            
            assert results["size_kb"] > 0
            file_size = gif_path.stat().st_size / 1024
            assert results["size_kb"] == pytest.approx(file_size, rel=0.01)
        finally:
            gif_path.unlink()


class TestIsSlackReady:
    """Test quick validation function."""
    
    def test_is_slack_ready_emoji(self, tmp_path):
        """Quick validation for emoji GIF."""
        gif_path = tmp_path / "emoji.gif"
        
        img = Image.new("RGB", (128, 128), color=(255, 0, 0))
        img.save(gif_path, "GIF")
        
        result = is_slack_ready(gif_path, is_emoji=True, verbose=False)
        assert result is True
    
    def test_is_slack_ready_fails_for_bad_dims(self, tmp_path):
        """Quick validation should fail for bad dimensions."""
        gif_path = tmp_path / "bad.gif"
        
        img = Image.new("RGB", (256, 256), color=(255, 0, 0))
        img.save(gif_path, "GIF")
        
        result = is_slack_ready(gif_path, is_emoji=True, verbose=False)
        assert result is False


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
```

---

## 3. Test Configuration Setup

### `pytest.ini`

```ini
[pytest]
minversion = 7.0
testpaths = skills/*/tests
python_files = test_*.py
python_classes = Test*
python_functions = test_*
addopts = 
    --strict-markers
    --tb=short
    --cov=skills
    --cov-report=term-missing
    --cov-report=html
    --cov-fail-under=70
markers =
    slow: marks tests as slow (deselect with '-m "not slow"')
    integration: marks tests as integration tests
    unit: marks tests as unit tests
```

### `requirements-dev.txt`

```
pytest>=7.0.0
pytest-cov>=4.0.0
pytest-mock>=3.10.0
coverage>=7.0.0
hypothesis>=6.0.0
faker>=15.0.0
```

---

## 4. Running Tests - Quick Reference

```bash
# Install test dependencies
pip install -r requirements-dev.txt

# Run all tests
pytest

# Run with verbose output
pytest -v

# Run specific test file
pytest skills/slack-gif-creator/tests/test_easing.py

# Run specific test class
pytest skills/slack-gif-creator/tests/test_easing.py::TestEasingBounds

# Run with coverage report
pytest --cov=skills --cov-report=html

# Open coverage report
open htmlcov/index.html

# Run only fast tests
pytest -m "not slow"

# Stop at first failure
pytest -x

# Show local variables on failure
pytest -l

# Parallel execution (if pytest-xdist installed)
pytest -n auto
```

---

## 5. CI/CD Integration Example

### `.github/workflows/tests.yml`

```yaml
name: Tests

on:
  push:
    branches: [ main, claude/* ]
  pull_request:
    branches: [ main ]

jobs:
  test:
    runs-on: ubuntu-latest
    strategy:
      matrix:
        python-version: ['3.9', '3.10', '3.11']
    
    steps:
    - uses: actions/checkout@v3
    
    - name: Set up Python
      uses: actions/setup-python@v4
      with:
        python-version: ${{ matrix.python-version }}
    
    - name: Install dependencies
      run: |
        python -m pip install --upgrade pip
        pip install -r requirements-dev.txt
    
    - name: Run tests
      run: pytest --cov=skills --cov-report=xml
    
    - name: Upload coverage
      uses: codecov/codecov-action@v3
      with:
        files: ./coverage.xml
        flags: unittests
```

---

## 6. Next Steps

1. **Create test structure:**
   ```bash
   mkdir -p skills/slack-gif-creator/tests
   touch skills/slack-gif-creator/tests/__init__.py
   ```

2. **Add test files:**
   - Copy examples above to `tests/test_easing.py` and `tests/test_validators.py`

3. **Install dependencies:**
   ```bash
   pip install -r requirements-dev.txt
   ```

4. **Run tests:**
   ```bash
   pytest skills/slack-gif-creator/tests/ -v
   ```

5. **Check coverage:**
   ```bash
   pytest skills/slack-gif-creator/tests/ --cov=skills.slack_gif_creator.core --cov-report=html
   ```

---

**Note:** These examples focus on the slack-gif-creator skill as it's the smallest and most self-contained. Scale this approach to other skills (DOCX, PPTX, XLSX, PDF) as the foundation solidifies.
