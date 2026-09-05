"""Regression tests for external_links_at_risk() in recalc.py."""

import os
import tempfile
import unittest
import zipfile

from openpyxl import Workbook
from openpyxl.workbook.defined_name import DefinedName

from recalc import external_links_at_risk


def _workbook_with_case_variant_name_reference(path: str) -> None:
    wb = Workbook()
    ws = wb.active
    ws["A1"] = "=mixedcase+1"
    wb.defined_names.add(
        DefinedName("MixedCase", attr_text="[1]external.xlsx!$A$1")
    )
    wb.save(path)

    with zipfile.ZipFile(path, "a") as archive:
        archive.writestr(
            "xl/externalLinks/externalLink1.xml",
            '<?xml version="1.0"?>'
            '<externalLink xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main"/>',
        )


class ExternalLinksAtRiskTests(unittest.TestCase):
    def test_matches_defined_names_case_insensitively(self):
        fd, path = tempfile.mkstemp(suffix=".xlsx")
        os.close(fd)
        try:
            _workbook_with_case_variant_name_reference(path)
            self.assertEqual(external_links_at_risk(path), ["Sheet!A1"])
        finally:
            os.unlink(path)


if __name__ == "__main__":
    unittest.main()
