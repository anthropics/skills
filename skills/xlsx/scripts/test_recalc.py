"""Tests for the data-table guard in recalc.py.

Run from skills/xlsx/scripts: python -m unittest test_recalc -v
No LibreOffice needed: the guard runs before any recalculation.
"""

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

from openpyxl import Workbook
from openpyxl.worksheet.formula import DataTableFormula

import recalc


def make_workbook(path, table=None):
    """Build the issue's repro workbook; table is a DataTableFormula or None."""
    wb = Workbook()
    ws = wb.active
    ws.title = "Sheet1"
    ws["B2"] = 10
    ws["B3"] = 2
    ws["B4"] = "=B2*B3"
    ws["D5"] = "=B4"
    if table is not None:
        ws["C6"] = 8
        ws["C7"] = 9
        ws["C8"] = 10
        ws["D6"] = table
    wb.save(path)


ONE_INPUT = DataTableFormula(ref="D6:D8", r1="B2", dt2D=True, dtr=False)
TWO_INPUT = DataTableFormula(ref="D11:F13", r1="B2", r2="B3", dt2D=True, dtr=True)


class TestDataTablesAtRisk(unittest.TestCase):
    def test_one_input_table_found(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "one.xlsx"
            make_workbook(p, table=ONE_INPUT)
            self.assertEqual(recalc.data_tables_at_risk(p), ["Sheet1!D6:D8"])

    def test_two_input_table_found(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "two.xlsx"
            make_workbook(p, table=TWO_INPUT)
            self.assertEqual(recalc.data_tables_at_risk(p), ["Sheet1!D11:F13"])

    def test_no_table(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "plain.xlsx"
            make_workbook(p, table=None)
            self.assertEqual(recalc.data_tables_at_risk(p), [])

    def test_not_a_workbook(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "junk.xlsx"
            p.write_text("not a zip")
            self.assertEqual(recalc.data_tables_at_risk(p), [])


class TestRecalcRefusal(unittest.TestCase):
    def test_refuses_data_table(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "t.xlsx"
            make_workbook(p, table=ONE_INPUT)
            result = recalc.recalc(str(p))
            self.assertIn("error", result)
            self.assertIn("data table", result["error"].lower())
            self.assertEqual(result["data_table_ranges"], ["Sheet1!D6:D8"])

    def test_cli_refuses_and_exits_nonzero(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "t.xlsx"
            make_workbook(p, table=ONE_INPUT)
            proc = subprocess.run(
                [sys.executable, str(Path(recalc.__file__).parent / "recalc.py"), str(p)],
                capture_output=True, text=True, timeout=120,
            )
            self.assertNotEqual(proc.returncode, 0)
            self.assertIn("data table", json.loads(proc.stdout)["error"].lower())


if __name__ == "__main__":
    unittest.main()
