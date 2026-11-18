import importlib.util
from pathlib import Path
import sys
import zipfile


def _load_recalc():
    scripts_dir = Path(__file__).resolve().parents[1] / "skills" / "xlsx" / "scripts"
    if str(scripts_dir) not in sys.path:
        sys.path.insert(0, str(scripts_dir))
    spec = importlib.util.spec_from_file_location("recalc", scripts_dir / "recalc.py")
    module = importlib.util.module_from_spec(spec)
    assert spec is not None and spec.loader is not None
    spec.loader.exec_module(module)
    return module


recalc = _load_recalc()


ROOT_RELS = """<?xml version="1.0" encoding="UTF-8" standalone="yes"?>
<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">
  <Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/officeDocument" Target="xl/workbook.xml"/>
</Relationships>"""

WORKBOOK_XML = """<?xml version="1.0" encoding="UTF-8" standalone="yes"?>
<workbook xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main"
          xmlns:r="http://schemas.openxmlformats.org/officeDocument/2006/relationships">
  <sheets>
    <sheet name="Sheet1" sheetId="1" r:id="rId1"/>
  </sheets>
</workbook>"""

WORKBOOK_RELS = """<?xml version="1.0" encoding="UTF-8" standalone="yes"?>
<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">
  <Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/worksheet" Target="worksheets/sheet1.xml"/>
</Relationships>"""

CONTENT_TYPES = """<?xml version="1.0" encoding="UTF-8" standalone="yes"?>
<Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types">
  <Default Extension="rels" ContentType="application/vnd.openxmlformats-package.relationships+xml"/>
  <Default Extension="xml" ContentType="application/xml"/>
  <Override PartName="/xl/workbook.xml" ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet.main+xml"/>
  <Override PartName="/xl/worksheets/sheet1.xml" ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.worksheet+xml"/>
</Types>"""


def _write_xlsx(path: Path, sheet_data_body: str) -> Path:
    sheet_xml = (
        '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
        '<worksheet xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main">'
        f"<sheetData>{sheet_data_body}</sheetData>"
        "</worksheet>"
    )
    with zipfile.ZipFile(path, "w", zipfile.ZIP_DEFLATED) as zf:
        zf.writestr("[Content_Types].xml", CONTENT_TYPES)
        zf.writestr("_rels/.rels", ROOT_RELS)
        zf.writestr("xl/workbook.xml", WORKBOOK_XML)
        zf.writestr("xl/_rels/workbook.xml.rels", WORKBOOK_RELS)
        zf.writestr("xl/worksheets/sheet1.xml", sheet_xml)
    return path


def test_shared_formula_lacking_in_libreoffice_marks_all_followers_not_computed(tmp_path: Path):
    workbook = _write_xlsx(
        tmp_path / "workbook.xlsx",
        (
            '<row r="2"><c r="B2"><f t="shared" ref="B2:B4" si="0">'
            "_xlfn.XLOOKUP(A2,$D$2:$D$4,$E$2:$E$4)</f></c></row>"
            '<row r="3"><c r="B3"><f t="shared" si="0"/></c></row>'
            '<row r="4"><c r="B4"><f t="shared" si="0"/></c></row>'
        ),
    )
    lo_copy = _write_xlsx(
        tmp_path / "copy.xlsx",
        (
            '<row r="2"><c r="B2" t="e"><f t="shared" ref="B2:B4" si="0">'
            "_xlfn.xlookup(A2,$D$2:$D$4,$E$2:$E$4)</f><v>#NAME?</v></c></row>"
            '<row r="3"><c r="B3" t="e"><f t="shared" si="0"/><v>#NAME?</v></c></row>'
            '<row r="4"><c r="B4" t="e"><f t="shared" si="0"/><v>#NAME?</v></c></row>'
        ),
    )

    found = recalc._write_values(str(workbook), str(lo_copy))
    report = recalc._report(str(workbook), found)

    assert report["status"] == "success"
    assert report["total_errors"] == 0
    assert report["error_summary"] == {}
    assert report["total_formulas"] == 3
    assert report["not_computed"] == {
        "count": 3,
        "locations": ["Sheet1!B2", "Sheet1!B3", "Sheet1!B4"],
    }


def test_shared_formula_supported_by_libreoffice_writes_all_follower_values(tmp_path: Path):
    workbook = _write_xlsx(
        tmp_path / "workbook.xlsx",
        (
            '<row r="2"><c r="B2"><f t="shared" ref="B2:B4" si="0">'
            "_xlfn.XLOOKUP(A2,$D$2:$D$4,$E$2:$E$4)</f></c></row>"
            '<row r="3"><c r="B3"><f t="shared" si="0"/></c></row>'
            '<row r="4"><c r="B4"><f t="shared" si="0"/></c></row>'
        ),
    )
    lo_copy = _write_xlsx(
        tmp_path / "copy.xlsx",
        (
            '<row r="2"><c r="B2"><f t="shared" ref="B2:B4" si="0">'
            "_xlfn.XLOOKUP(A2,$D$2:$D$4,$E$2:$E$4)</f><v>10</v></c></row>"
            '<row r="3"><c r="B3"><f t="shared" si="0"/><v>20</v></c></row>'
            '<row r="4"><c r="B4"><f t="shared" si="0"/><v>30</v></c></row>'
        ),
    )

    found = recalc._write_values(str(workbook), str(lo_copy))
    report = recalc._report(str(workbook), found)

    assert report["status"] == "success"
    assert report["total_errors"] == 0
    assert "not_computed" not in report
    with zipfile.ZipFile(workbook) as zf:
        sheet = zf.read("xl/worksheets/sheet1.xml")
    assert b"<v>10</v>" in sheet
    assert b"<v>20</v>" in sheet
    assert b"<v>30</v>" in sheet


def test_shared_formula_calling_libreoffice_only_function_flags_all_followers_name_error(
    tmp_path: Path,
):
    workbook = _write_xlsx(
        tmp_path / "workbook.xlsx",
        (
            '<row r="2"><c r="B2"><f t="shared" ref="B2:B4" si="0">DaysInMonth(A2)</f></c></row>'
            '<row r="3"><c r="B3"><f t="shared" si="0"/></c></row>'
            '<row r="4"><c r="B4"><f t="shared" si="0"/></c></row>'
        ),
    )
    before = workbook.read_bytes()
    lo_copy = _write_xlsx(
        tmp_path / "copy.xlsx",
        (
            '<row r="2"><c r="B2"><f t="shared" ref="B2:B4" si="0">'
            "DaysInMonth(A2)</f><v>31</v></c></row>"
            '<row r="3"><c r="B3"><f t="shared" si="0"/><v>28</v></c></row>'
            '<row r="4"><c r="B4"><f t="shared" si="0"/><v>31</v></c></row>'
        ),
    )

    found = recalc._write_values(str(workbook), str(lo_copy))
    report = recalc._report(str(workbook), found)

    assert report["status"] == "errors_found"
    assert report["total_errors"] == 3
    assert report["error_summary"] == {
        "#NAME?": {"count": 3, "locations": ["Sheet1!B2", "Sheet1!B3", "Sheet1!B4"]}
    }
    assert workbook.read_bytes() == before
