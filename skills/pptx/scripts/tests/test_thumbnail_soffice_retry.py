"""Regression tests for thumbnail.py LibreOffice retry and error handling.

Covers:
- Retry with lock file cleanup on transient soffice failures (#886)
- --norestore flag presence
- Timeout enforcement
- stderr surfacing in error messages
- Successful conversion on first/later attempt
- pdftoppm timeout and error handling
"""

import ast
import inspect
import re
import subprocess
import textwrap
import time
import types
import unittest
from pathlib import Path
from unittest.mock import MagicMock, patch

# ---------------------------------------------------------------------------
# Locate source without relying on the skill's runtime import machinery
# ---------------------------------------------------------------------------
SCRIPTS_DIR = Path(__file__).resolve().parent.parent
THUMBNAIL_SRC = (SCRIPTS_DIR / "thumbnail.py").read_text()


# ---------------------------------------------------------------------------
# Source-level audits (no imports needed)
# ---------------------------------------------------------------------------
class TestSourceAudit(unittest.TestCase):
    """Verify structural properties of the source that prevent regressions."""

    def test_norestore_flag_present(self):
        """--norestore must appear in the soffice command (parity with recalc.py)."""
        self.assertIn('"--norestore"', THUMBNAIL_SRC)

    def test_timeout_parameter_in_soffice_call(self):
        """subprocess.run for soffice must include a timeout kwarg."""
        # Find the soffice subprocess.run block
        tree = ast.parse(THUMBNAIL_SRC)
        found_timeout = False
        for node in ast.walk(tree):
            if isinstance(node, ast.Call):
                func = node.func
                # Match subprocess.run(...)
                if (isinstance(func, ast.Attribute) and func.attr == "run"
                        and isinstance(func.value, ast.Name) and func.value.id == "subprocess"):
                    # Check if any positional arg contains "soffice"
                    first_arg = node.args[0] if node.args else None
                    if first_arg is None:
                        continue
                    # List literal containing "soffice"
                    is_soffice_call = False
                    if isinstance(first_arg, ast.List):
                        for elt in first_arg.elts:
                            if isinstance(elt, ast.Constant) and isinstance(elt.value, str) and "soffice" in elt.value:
                                is_soffice_call = True
                                break
                    if is_soffice_call:
                        for kw in node.keywords:
                            if kw.arg == "timeout":
                                found_timeout = True
                                break
        self.assertTrue(found_timeout, "soffice subprocess.run call must include timeout=")

    def test_soffice_max_retries_constant(self):
        """SOFFICE_MAX_RETRIES must be defined and >= 2."""
        match = re.search(r"SOFFICE_MAX_RETRIES\s*=\s*(\d+)", THUMBNAIL_SRC)
        self.assertIsNotNone(match, "SOFFICE_MAX_RETRIES constant must be defined")
        self.assertGreaterEqual(int(match.group(1)), 2)

    def test_soffice_timeout_constant(self):
        """SOFFICE_TIMEOUT must be defined and > 0."""
        match = re.search(r"SOFFICE_TIMEOUT\s*=\s*(\d+)", THUMBNAIL_SRC)
        self.assertIsNotNone(match, "SOFFICE_TIMEOUT constant must be defined")
        self.assertGreater(int(match.group(1)), 0)

    def test_cleanup_lock_function_exists(self):
        """A lock-file cleanup helper must exist."""
        self.assertIn("_cleanup_soffice_lock", THUMBNAIL_SRC)

    def test_stderr_captured_in_error_message(self):
        """Error messages must include stderr details, not just 'PDF conversion failed'."""
        # The old code had a bare "PDF conversion failed" with no stderr.
        # Ensure we now reference stderr/detail in the RuntimeError.
        # Count bare "PDF conversion failed" without any detail variable nearby
        bare_errors = re.findall(
            r'raise\s+RuntimeError\(\s*"PDF conversion failed"\s*\)',
            THUMBNAIL_SRC,
        )
        self.assertEqual(
            len(bare_errors), 0,
            "No bare 'PDF conversion failed' without stderr detail should remain",
        )

    def test_pdftoppm_has_timeout(self):
        """pdftoppm subprocess.run must include a timeout kwarg."""
        tree = ast.parse(THUMBNAIL_SRC)
        found = False
        for node in ast.walk(tree):
            if isinstance(node, ast.Call):
                func = node.func
                if (isinstance(func, ast.Attribute) and func.attr == "run"
                        and isinstance(func.value, ast.Name) and func.value.id == "subprocess"):
                    first_arg = node.args[0] if node.args else None
                    if first_arg is None:
                        continue
                    is_pdftoppm = False
                    if isinstance(first_arg, ast.List):
                        for elt in first_arg.elts:
                            if isinstance(elt, ast.Constant) and isinstance(elt.value, str) and "pdftoppm" in elt.value:
                                is_pdftoppm = True
                                break
                    if is_pdftoppm:
                        for kw in node.keywords:
                            if kw.arg == "timeout":
                                found = True
        self.assertTrue(found, "pdftoppm subprocess.run must include timeout=")


# ---------------------------------------------------------------------------
# Functional tests via module-level extraction
# ---------------------------------------------------------------------------

def _load_module():
    """Load thumbnail.py as a module, stubbing heavy dependencies."""
    import importlib
    import types

    mod = types.ModuleType("thumbnail")
    mod.__file__ = str(SCRIPTS_DIR / "thumbnail.py")

    # Stub imports that may not be available
    stub_defusedxml = types.ModuleType("defusedxml")
    stub_minidom = types.ModuleType("defusedxml.minidom")
    stub_defusedxml.minidom = stub_minidom
    stub_minidom.parseString = MagicMock()

    stub_soffice = types.ModuleType("office.soffice")
    stub_soffice.get_soffice_env = MagicMock(return_value={})

    stub_pil = types.ModuleType("PIL")
    stub_image = types.ModuleType("PIL.Image")
    stub_draw = types.ModuleType("PIL.ImageDraw")
    stub_font = types.ModuleType("PIL.ImageFont")

    # PIL.Image.Image is a class used in type annotations (-> Image.Image)
    class _FakeImage:
        class Resampling:
            LANCZOS = 1
    stub_image.Image = _FakeImage
    stub_image.Resampling = _FakeImage.Resampling
    stub_image.new = MagicMock()
    stub_image.open = MagicMock()
    stub_draw.Draw = MagicMock()
    stub_draw.ImageDraw = MagicMock()
    stub_font.load_default = MagicMock()
    stub_font.ImageFont = MagicMock()
    stub_pil.Image = stub_image
    stub_pil.ImageDraw = stub_draw
    stub_pil.ImageFont = stub_font

    import sys as _sys
    saved = {}
    stubs = {
        "defusedxml": stub_defusedxml,
        "defusedxml.minidom": stub_minidom,
        "office": types.ModuleType("office"),
        "office.soffice": stub_soffice,
        "PIL": stub_pil,
        "PIL.Image": stub_image,
        "PIL.ImageDraw": stub_draw,
        "PIL.ImageFont": stub_font,
    }
    for name, stub in stubs.items():
        saved[name] = _sys.modules.get(name)
        _sys.modules[name] = stub

    try:
        exec(compile(THUMBNAIL_SRC, str(SCRIPTS_DIR / "thumbnail.py"), "exec"), mod.__dict__)
    finally:
        for name, orig in saved.items():
            if orig is None:
                _sys.modules.pop(name, None)
            else:
                _sys.modules[name] = orig

    return mod


class TestConvertToImagesRetry(unittest.TestCase):
    """Functional tests for convert_to_images retry logic."""

    @classmethod
    def setUpClass(cls):
        cls.mod = _load_module()

    @patch("subprocess.run")
    def test_success_on_first_attempt(self, mock_run):
        """Conversion succeeds on the first try - no retries needed."""
        import tempfile
        with tempfile.TemporaryDirectory() as td:
            td_path = Path(td)
            pptx_path = td_path / "test.pptx"
            pptx_path.touch()
            pdf_path = td_path / "test.pdf"

            call_count = 0

            def side_effect(cmd, **kwargs):
                nonlocal call_count
                call_count += 1
                result = MagicMock()
                result.returncode = 0
                result.stderr = ""
                if "soffice" in cmd:
                    pdf_path.write_text("fake pdf")
                if "pdftoppm" in cmd:
                    (td_path / "slide-1.jpg").touch()
                return result

            mock_run.side_effect = side_effect
            images = self.mod.convert_to_images(pptx_path, td_path)
            # soffice called exactly once (no retry needed)
            soffice_calls = [c for c in mock_run.call_args_list
                             if "soffice" in c.args[0]]
            self.assertEqual(len(soffice_calls), 1)
            self.assertEqual(len(images), 1)

    @patch("subprocess.run")
    def test_success_on_second_attempt(self, mock_run):
        """Conversion fails first, succeeds on retry."""
        import tempfile
        with tempfile.TemporaryDirectory() as td:
            td_path = Path(td)
            pptx_path = td_path / "test.pptx"
            pptx_path.touch()
            pdf_path = td_path / "test.pdf"

            attempt = 0

            def side_effect(cmd, **kwargs):
                nonlocal attempt
                if "soffice" in cmd:
                    attempt += 1
                    result = MagicMock()
                    if attempt == 1:
                        result.returncode = 1
                        result.stderr = "lock file error"
                    else:
                        result.returncode = 0
                        result.stderr = ""
                        pdf_path.write_text("fake pdf")
                    return result
                # pdftoppm
                result = MagicMock()
                result.returncode = 0
                result.stderr = ""
                (td_path / "slide-1.jpg").touch()
                return result

            mock_run.side_effect = side_effect
            images = self.mod.convert_to_images(pptx_path, td_path)
            self.assertEqual(attempt, 2)
            self.assertEqual(len(images), 1)

    @patch("subprocess.run")
    def test_all_retries_exhausted(self, mock_run):
        """All retries fail - raises RuntimeError with stderr detail."""
        import tempfile
        with tempfile.TemporaryDirectory() as td:
            td_path = Path(td)
            pptx_path = td_path / "test.pptx"
            pptx_path.touch()

            def side_effect(cmd, **kwargs):
                result = MagicMock()
                result.returncode = 1
                result.stderr = "profile lock: resource busy"
                return result

            mock_run.side_effect = side_effect
            with self.assertRaises(RuntimeError) as ctx:
                self.mod.convert_to_images(pptx_path, td_path)
            # Error message must include stderr detail
            self.assertIn("profile lock: resource busy", str(ctx.exception))
            self.assertIn("attempts", str(ctx.exception))

    @patch("subprocess.run")
    def test_timeout_triggers_retry(self, mock_run):
        """TimeoutExpired from soffice triggers retry, not immediate crash."""
        import tempfile
        with tempfile.TemporaryDirectory() as td:
            td_path = Path(td)
            pptx_path = td_path / "test.pptx"
            pptx_path.touch()
            pdf_path = td_path / "test.pdf"

            attempt = 0

            def side_effect(cmd, **kwargs):
                nonlocal attempt
                if "soffice" in cmd:
                    attempt += 1
                    if attempt == 1:
                        raise subprocess.TimeoutExpired(cmd="soffice", timeout=120)
                    result = MagicMock()
                    result.returncode = 0
                    result.stderr = ""
                    pdf_path.write_text("fake pdf")
                    return result
                result = MagicMock()
                result.returncode = 0
                result.stderr = ""
                (td_path / "slide-1.jpg").touch()
                return result

            mock_run.side_effect = side_effect
            images = self.mod.convert_to_images(pptx_path, td_path)
            self.assertEqual(attempt, 2)

    @patch("subprocess.run")
    def test_all_timeouts_exhausted(self, mock_run):
        """All attempts timeout - error message includes timeout info."""
        import tempfile
        with tempfile.TemporaryDirectory() as td:
            td_path = Path(td)
            pptx_path = td_path / "test.pptx"
            pptx_path.touch()

            def side_effect(cmd, **kwargs):
                raise subprocess.TimeoutExpired(cmd="soffice", timeout=120)

            mock_run.side_effect = side_effect
            with self.assertRaises(RuntimeError) as ctx:
                self.mod.convert_to_images(pptx_path, td_path)
            self.assertIn("timed out", str(ctx.exception))

    @patch("subprocess.run")
    def test_pdftoppm_timeout(self, mock_run):
        """pdftoppm timeout raises RuntimeError with timeout info."""
        import tempfile
        with tempfile.TemporaryDirectory() as td:
            td_path = Path(td)
            pptx_path = td_path / "test.pptx"
            pptx_path.touch()
            pdf_path = td_path / "test.pdf"

            def side_effect(cmd, **kwargs):
                if "soffice" in cmd:
                    pdf_path.write_text("fake pdf")
                    result = MagicMock()
                    result.returncode = 0
                    result.stderr = ""
                    return result
                # pdftoppm
                raise subprocess.TimeoutExpired(cmd="pdftoppm", timeout=120)

            mock_run.side_effect = side_effect
            with self.assertRaises(RuntimeError) as ctx:
                self.mod.convert_to_images(pptx_path, td_path)
            self.assertIn("pdftoppm", str(ctx.exception))
            self.assertIn("timed out", str(ctx.exception))

    @patch("subprocess.run")
    def test_pdftoppm_error_includes_stderr(self, mock_run):
        """pdftoppm failure includes stderr in error message."""
        import tempfile
        with tempfile.TemporaryDirectory() as td:
            td_path = Path(td)
            pptx_path = td_path / "test.pptx"
            pptx_path.touch()
            pdf_path = td_path / "test.pdf"

            def side_effect(cmd, **kwargs):
                if "soffice" in cmd:
                    pdf_path.write_text("fake pdf")
                    result = MagicMock()
                    result.returncode = 0
                    result.stderr = ""
                    return result
                result = MagicMock()
                result.returncode = 1
                result.stderr = "Syntax Error: Couldn't open file"
                return result

            mock_run.side_effect = side_effect
            with self.assertRaises(RuntimeError) as ctx:
                self.mod.convert_to_images(pptx_path, td_path)
            self.assertIn("Couldn't open file", str(ctx.exception))

    @patch("subprocess.run")
    def test_norestore_flag_in_command(self, mock_run):
        """The actual soffice command list must include --norestore."""
        import tempfile
        with tempfile.TemporaryDirectory() as td:
            td_path = Path(td)
            pptx_path = td_path / "test.pptx"
            pptx_path.touch()
            pdf_path = td_path / "test.pdf"

            def side_effect(cmd, **kwargs):
                if "soffice" in cmd:
                    pdf_path.write_text("fake pdf")
                result = MagicMock()
                result.returncode = 0
                result.stderr = ""
                if "pdftoppm" in cmd:
                    (td_path / "slide-1.jpg").touch()
                return result

            mock_run.side_effect = side_effect
            self.mod.convert_to_images(pptx_path, td_path)

            soffice_calls = [c for c in mock_run.call_args_list
                             if "soffice" in c.args[0]]
            self.assertTrue(len(soffice_calls) > 0)
            self.assertIn("--norestore", soffice_calls[0].args[0])


class TestCleanupLockFunction(unittest.TestCase):
    """Test the lock file cleanup helper."""

    @classmethod
    def setUpClass(cls):
        cls.mod = _load_module()

    def test_removes_lock_files(self):
        """Lock files matching LibreOffice patterns are removed."""
        import tempfile
        with tempfile.TemporaryDirectory() as td:
            td_path = Path(td)
            lock1 = td_path / ".~lock.test.pptx#"
            lock2 = td_path / ".~lock.other.pdf"
            lock1.touch()
            lock2.touch()
            self.mod._cleanup_soffice_lock(td_path)
            self.assertFalse(lock1.exists())
            self.assertFalse(lock2.exists())

    def test_no_error_on_empty_dir(self):
        """Cleanup on a directory with no locks doesn't raise."""
        import tempfile
        with tempfile.TemporaryDirectory() as td:
            self.mod._cleanup_soffice_lock(Path(td))  # Should not raise

    def test_preserves_non_lock_files(self):
        """Regular files are not deleted."""
        import tempfile
        with tempfile.TemporaryDirectory() as td:
            td_path = Path(td)
            normal = td_path / "slide.pdf"
            normal.touch()
            self.mod._cleanup_soffice_lock(td_path)
            self.assertTrue(normal.exists())


if __name__ == "__main__":
    unittest.main()
