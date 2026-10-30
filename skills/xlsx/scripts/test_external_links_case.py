"""
Regression test for anthropics/skills#1464.

external_links_at_risk() must match defined-name references case-insensitively,
since Excel treats defined names as case-insensitive.
"""
import shutil
import sys
import zipfile
from pathlib import Path

SCRIPTS_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS_DIR))

from openpyxl import Workbook
from openpyxl.workbook.defined_name import DefinedName

from recalc import external_links_at_risk


def build_workbook(path):
    wb = Workbook()
    ws = wb.active
    ws.title = "Sheet1"

    # Defined name that "points at" an external workbook, matching the
    # EXTERNAL_REF_RE shape used to seed `external_names`.
    wb.defined_names["MixedCase"] = DefinedName(
        name="MixedCase", attr_text="[1]Sheet1!$A$1"
    )

    # Formula referencing the name in different case, with no cached value
    # (mirrors a value openpyxl would strip on save).
    ws["A1"] = "=mixedcase+1"

    wb.save(path)

    # openpyxl can't author a real xl/externalLinks/ part, but
    # external_links_at_risk() only checks for the path's presence, so
    # inject a placeholder entry into the zip.
    with zipfile.ZipFile(path, "a") as z:
        z.writestr("xl/externalLinks/externalLink1.xml", "<externalLink/>")


def main():
    tmp_dir = Path("/tmp/xlsx-case-test")
    tmp_dir.mkdir(exist_ok=True)
    path = tmp_dir / "case_variant.xlsx"
    if path.exists():
        path.unlink()

    build_workbook(path)

    at_risk = external_links_at_risk(str(path))
    assert at_risk == ["Sheet1!A1"], (
        f"expected 'Sheet1!A1' to be reported as at-risk (case-insensitive "
        f"defined-name match), got: {at_risk}"
    )
    print("PASS: case-variant reference to a defined name is detected as at-risk")

    shutil.rmtree(tmp_dir)


if __name__ == "__main__":
    main()
