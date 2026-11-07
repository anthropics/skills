import subprocess
import sys
from pathlib import Path

from pypdf import PdfWriter

SCRIPTS = Path(__file__).parent


def run(script, *args):
    return subprocess.run(
        [sys.executable, str(SCRIPTS / script), *args],
        capture_output=True, text=True,
    )


def blank_pdf(tmp_path):
    path = tmp_path / "blank.pdf"
    writer = PdfWriter()
    writer.add_blank_page(width=200, height=200)
    with open(path, "wb") as f:
        writer.write(f)
    return path


def test_extract_no_form_fields_exits_cleanly(tmp_path):
    result = run("extract_form_field_info.py", str(blank_pdf(tmp_path)), str(tmp_path / "out.json"))
    assert "Traceback" not in result.stderr
    assert result.returncode != 0
    assert "no fillable form fields" in (result.stdout + result.stderr).lower()


def test_check_fillable_fields_usage_without_args():
    result = run("check_fillable_fields.py")
    assert "Traceback" not in result.stderr
    assert result.returncode == 1
    assert "usage" in (result.stdout + result.stderr).lower()
