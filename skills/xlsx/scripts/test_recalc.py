"""
Regression tests for external_links_at_risk() in recalc.py.

Covers issue #1464: the defined-name regex used to flag cells that reach
an external-linked defined name was compiled without re.IGNORECASE, so a
formula referencing the name with different casing than its definition
was silently missed.
"""

import sys
import zipfile
from pathlib import Path

import pytest
from openpyxl import Workbook
from openpyxl.workbook.defined_name import DefinedName

sys.path.insert(0, str(Path(__file__).resolve().parent))

from recalc import external_links_at_risk  # noqa: E402


def _make_workbook_with_external_link(path, defined_name, formula_ref):
    """
    Build a minimal .xlsx that:
      - has a defined name pointing at an external workbook reference
        (so EXTERNAL_REF_RE matches its value and it's treated as an
        external-linked name)
      - has a cell formula referencing that name using `formula_ref`
        casing, with no cached value (simulating openpyxl having
        stripped the cached external value on save)
      - contains a stub xl/externalLinks/ member so the "has external
        links at all" precheck passes
    """
    wb = Workbook()
    ws = wb.active
    ws.title = "Sheet1"

    wb.defined_names[defined_name] = DefinedName(
        defined_name, attr_text="[1]Sheet1!$A$1"
    )

    ws["A1"] = f"={formula_ref}"

    wb.save(path)

    # Inject a stub external link part so external_links_at_risk() doesn't
    # bail out on the "no xl/externalLinks/ members" fast path.
    with zipfile.ZipFile(path, "a") as archive:
        archive.writestr(
            "xl/externalLinks/externalLink1.xml",
            '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
            '<externalLink xmlns="http://schemas.openxmlformats.org/'
            'spreadsheetml/2006/main"/>',
        )


def test_case_variant_reference_is_flagged_as_at_risk(tmp_path):
    """A formula referencing a linked name in a different case must still
    be detected as reaching out to the external link."""
    path = tmp_path / "case_variant.xlsx"
    _make_workbook_with_external_link(
        path, defined_name="MixedCase", formula_ref="mixedcase"
    )

    at_risk = external_links_at_risk(str(path))

    assert at_risk == ["Sheet1!A1"]


def test_exact_case_reference_is_still_flagged_as_at_risk(tmp_path):
    """Sanity check: the exact-case path (already covered pre-fix) keeps
    working after adding re.IGNORECASE."""
    path = tmp_path / "exact_case.xlsx"
    _make_workbook_with_external_link(
        path, defined_name="MixedCase", formula_ref="MixedCase"
    )

    at_risk = external_links_at_risk(str(path))

    assert at_risk == ["Sheet1!A1"]


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))
