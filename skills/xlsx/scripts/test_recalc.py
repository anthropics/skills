import sys
import tempfile
import unittest
import zipfile
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))

import recalc


class _Sheet:
    def __init__(self, cell):
        self._cell = cell

    def iter_rows(self):
        return [[self._cell]]

    def __getitem__(self, coordinate):
        return self._cell


class _Workbook:
    sheetnames = ["Sheet1"]

    def __init__(self, cell, defined_name):
        self.defined_names = {"MixedCase": SimpleNamespace(value=defined_name)}
        self._sheet = _Sheet(cell)

    def __getitem__(self, sheet):
        return self._sheet

    def close(self):
        pass


class ExternalDefinedNameTests(unittest.TestCase):
    def test_case_variant_defined_name_is_at_risk(self):
        formula_cell = SimpleNamespace(value="=mIxEdCaSe", coordinate="A1")
        cached_cell = SimpleNamespace(value=None)
        formulas = _Workbook(formula_cell, "'[1]Data'!$A$1")
        values = _Workbook(SimpleNamespace(value=cached_cell.value, coordinate="A1"), "")

        with tempfile.TemporaryDirectory() as directory:
            filename = Path(directory) / "book.xlsx"
            with zipfile.ZipFile(filename, "w") as archive:
                archive.writestr("xl/externalLinks/externalLink1.xml", "")

            with patch.object(recalc, "load_workbook", side_effect=[formulas, values]):
                self.assertEqual(recalc.external_links_at_risk(filename), ["Sheet1!A1"])


if __name__ == "__main__":
    unittest.main()
