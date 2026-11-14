"""
Excel Formula Recalculation Script
Recalculates all formulas in an Excel file using LibreOffice

LibreOffice recalculates a copy of the workbook. Only the values it computed are then written
into the workbook itself, so nothing else in the file is rewritten.
"""

import contextlib
import copy
import html
import io
import json
import math
import os
import platform
import posixpath
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import zipfile
from pathlib import Path
from xml.parsers import expat

from office.soffice import get_soffice_env, run_soffice

MACRO_FILENAME = "Module1.xba"
SOFFICE_MISSING = "soffice not found on PATH; LibreOffice is required to recalculate"

MAX_LOCATIONS = 100

RECALCULATE_MACRO = """<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE script:module PUBLIC "-//OpenOffice.org//DTD OfficeDocument 1.0//EN" "module.dtd">
<script:module xmlns:script="http://openoffice.org/2000/script" script:name="Module1" script:language="StarBasic">
    Sub RecalculateAndSave()
      ThisComponent.calculateAll()
      ThisComponent.store()
      ThisComponent.close(True)
    End Sub
</script:module>"""


def has_gtimeout():
    try:
        subprocess.run(
            ["gtimeout", "--version"], capture_output=True, timeout=1, check=False
        )
        return True
    except (FileNotFoundError, subprocess.TimeoutExpired):
        return False


def _stamp(path):
    st = os.stat(path)
    return st.st_mtime_ns, st.st_size


def setup_libreoffice_macro(profile_dir: Path, timeout=30):
    url = profile_dir.as_uri()
    try:
        run_soffice(
            ["--headless", "--terminate_after_init", f"-env:UserInstallation={url}"],
            capture_output=True,
            timeout=timeout,
        )
    except FileNotFoundError:
        return None, SOFFICE_MISSING
    except subprocess.TimeoutExpired:
        return None, "LibreOffice timed out creating its profile; formulas were NOT recalculated"

    macro_dir = profile_dir / "user" / "basic" / "Standard"
    if not macro_dir.exists():
        return None, "LibreOffice did not create a usable profile; formulas were NOT recalculated"

    try:
        (macro_dir / MACRO_FILENAME).write_text(RECALCULATE_MACRO)
    except OSError as e:
        return None, f"Could not install the recalculation macro: {e}"

    return url, None


def _existing_cells(ws):
    if not hasattr(ws, "iter_rows"):  
        return []
    return [ws._cells[key] for key in sorted(ws._cells)]


def _is_workbook(path):
    try:
        with zipfile.ZipFile(path) as archive:
            return _workbook_part(archive) is not None
    except Exception:  
        return False


def _part_that_is_not_xml(path):
    with zipfile.ZipFile(path) as archive:
        for item in archive.infolist():
            if not item.filename.endswith((".xml", ".rels")) or item.file_size > 50_000_000:
                continue
            data = archive.read(item)
            plain = data.replace(b"\x00", b"") if b"\x00" in data[:64] else data
            if b"<!" in plain:
                continue
            try:
                expat.ParserCreate().Parse(data, True)
            except expat.ExpatError as e:
                return f"{item.filename} is not well-formed XML: {e}"
    return None


def _has_formulas(path):
    try:
        with zipfile.ZipFile(path) as archive:
            for _, part_name in _worksheets(archive, any_namespace=True):
                raw = archive.read(part_name)
                plain = raw.replace(b"\x00", b"") if b"\x00" in raw[:64] else raw
                if re.search(rb"<(?:\w+:)?f[\s/>]", plain):
                    return True
                if b"<!" not in plain:  
                    expat.ParserCreate().Parse(raw, True)  
        return False
    except Exception:  
        return True


def recalc(filename, timeout=30, force=False):
    if not Path(filename).exists():
        return {"error": f"File {filename} does not exist"}

    abs_path = os.path.realpath(filename)

    if not _is_workbook(abs_path):
        return {"error": f"{filename} is not an .xlsx or .xlsm workbook; recalc.py cannot read it"}

    if not _has_formulas(abs_path):
        report = _report(filename)
        if "error" not in report:
            return report
        broken = _part_that_is_not_xml(abs_path)
        if broken:
            return {"error": f"{broken}; {filename} is unchanged"}
        return {"status": "success", "total_errors": 0, "error_summary": {}, "total_formulas": 0}

    if not (os.access(abs_path, os.W_OK) and os.access(os.path.dirname(abs_path), os.W_OK)):
        return {
            "error": f"{filename} or its folder is not writable; recalc.py needs to write to both"
        }

    try:
        get_soffice_env()
    except Exception as e:  
        return {"error": f"Could not prepare the LibreOffice environment: {e}"}

    with tempfile.TemporaryDirectory(prefix="recalc-lo-", ignore_cleanup_errors=True) as work:
        copy = os.path.join(work, "copy", os.path.basename(abs_path))
        profile_dir = Path(work) / "profile"
        try:
            os.mkdir(os.path.dirname(copy))
            shutil.copyfile(abs_path, copy)
            profile_dir.mkdir()
        except OSError as e:
            return {"error": f"Could not copy {filename} for LibreOffice to work on: {e}"}
        return _recalc_with_profile(filename, abs_path, copy, timeout, profile_dir)


def _recalc_with_profile(filename, abs_path, copy, timeout, profile_dir: Path):
    started = time.monotonic()
    profile_url, err = setup_libreoffice_macro(profile_dir, timeout=timeout)
    if err:
        return {"error": err}

    timeout = max(5, int(timeout - (time.monotonic() - started)))

    before = _stamp(copy)

    cmd = [
        "soffice",
        "--headless",
        "--norestore",
        f"-env:UserInstallation={profile_url}",
        "vnd.sun.star.script:Standard.Module1.RecalculateAndSave?language=Basic&location=application",
        copy,
    ]

    if platform.system() == "Linux" and shutil.which("timeout"):
        cmd = ["timeout", str(timeout)] + cmd
    elif platform.system() == "Darwin" and has_gtimeout():
        cmd = ["gtimeout", str(timeout)] + cmd

    timed_out = f"LibreOffice timed out after {timeout}s; formulas were NOT recalculated. Re-run with a longer timeout."

    try:
        result = subprocess.run(
            cmd, capture_output=True, text=True, env=get_soffice_env(), timeout=timeout + 15
        )
    except subprocess.TimeoutExpired:
        return {"error": timed_out}
    except FileNotFoundError:
        return {"error": SOFFICE_MISSING}

    if result.returncode == 124:
        return {"error": timed_out}

    if result.returncode != 0:
        detail = (result.stderr or "").strip() or f"soffice exited {result.returncode}"
        return {"error": f"LibreOffice failed to recalculate: {detail}"}

    try:
        rewritten = _stamp(copy) != before
    except OSError:  
        rewritten = False
    if not rewritten:
        return {
            "error": (
                "LibreOffice exited cleanly but never rewrote its copy of the file, so nothing was "
                "recalculated. Run it again; if the same happens, LibreOffice is not running the "
                "recalculation macro on this machine."
            )
        }

    try:
        found = _write_values(abs_path, copy)
    except Exception as e:  
        why = f"which is unchanged: {str(e) or type(e).__name__}"
        return {"error": f"Could not write the new values into {filename}, {why}"}

    return _report(filename, found)


EXCEL_ERRORS = ["#VALUE!", "#DIV/0!", "#REF!", "#NAME?", "#NULL!", "#NUM!", "#N/A"]

_MAIN_NS = "{http://schemas.openxmlformats.org/spreadsheetml/2006/main}"
_REL_NS = "{http://schemas.openxmlformats.org/officeDocument/2006/relationships}"
_CELL_REF_RE = re.compile(r"([A-Z]{1,3})([0-9]+)")  
MAX_MERGE_CHECKS = 1_000_000
_MERGE_RE = re.compile(rb'<(?:\w+:)?mergeCell\b[^>]*\bref="([^"]*)"')


def _error_in(text):
    if "#" in text:
        for err in EXCEL_ERRORS:
            if err in text:
                return err
    return None


def _rich_text(node):
    runs = node.findall(f"{_MAIN_NS}t") + node.findall(f"{_MAIN_NS}r/{_MAIN_NS}t")
    return "".join(t.text or "" for t in runs)


def _row_major(coordinate):
    address = _CELL_REF_RE.fullmatch(coordinate)
    if address is None:
        raise ValueError(f"{coordinate[:20]!r} is not the address of a cell")
    column, row = address.groups()
    number = 0
    for letter in column:
        number = number * 26 + ord(letter) - ord("A") + 1
    return int(row), number


def _merged_ranges(sheet_xml):
    ranges = []
    for ref in _MERGE_RE.findall(sheet_xml):
        first, _, last = ref.decode().partition(":")
        ranges.append((*_row_major(first), *_row_major(last)))
    return ranges


def _hidden_by_a_merge(merged, row, column):
    return any(
        top <= row <= bottom and left <= column <= right and (row, column) != (top, left)
        for top, left, bottom, right in merged
    )


def _utf8_or_refuse(data, what):
    declared = re.search(rb"""<\?xml[^>]*\sencoding\s*=\s*["']([^"']+)""", data[:200])
    utf8 = declared is None or declared[1].lower().replace(b"-", b"") == b"utf8"
    if data[:2] in (b"\xff\xfe", b"\xfe\xff") or b"\x00" in data[:64] or not utf8:
        raise ValueError(f"{what} is not in UTF-8, which is all this script can read")


def _xml(data, what="an XML part"):
    try:
        from defusedxml.ElementTree import fromstring
    except ImportError:
        _utf8_or_refuse(data, what)  
        if b"<!DOCTYPE" in data or b"<!ENTITY" in data:
            raise ValueError("XML with a DTD, and defusedxml is not installed") from None
        from xml.etree.ElementTree import fromstring
    return fromstring(data)


def _workbook_part(archive):
    if "_rels/.rels" not in archive.namelist():
        return None
    for rel in _xml(archive.read("_rels/.rels"), "_rels/.rels"):
        if rel.get("Type", "").endswith("/officeDocument"):
            name = posixpath.normpath(rel.get("Target", "")).lstrip("/")
            return name if name in archive.namelist() else None
    return None


def _workbook_xml(archive):
    name = _workbook_part(archive)
    if name is None:
        raise ValueError("the package names no workbook part")
    if archive.getinfo(name).file_size > 50_000_000:
        raise ValueError(f"{name} is too large to be a workbook's")
    return _xml(archive.read(name), name)


def _worksheets(archive, any_namespace=False):
    workbook = _workbook_xml(archive)
    if not any_namespace and workbook.tag != f"{_MAIN_NS}workbook":
        namespace = workbook.tag.partition("}")[0].lstrip("{")
        if "/ooxml/" in namespace:  
            raise ValueError("it is in Strict Open XML format, which this script cannot edit")
        raise ValueError(f"its XML is in a namespace this script does not read ({namespace})")
    folder, file_name = posixpath.split(_workbook_part(archive))
    rels_name = posixpath.join(folder, "_rels", f"{file_name}.rels")
    rels = {rel.get("Id"): rel for rel in _xml(archive.read(rels_name), rels_name)}
    found = []
    for sheet in workbook.iter():
        if not sheet.tag.endswith("}sheet"):
            continue
        rel_id = next((value for key, value in sheet.attrib.items() if key.endswith("}id")), None)
        rel = rels.get(rel_id)
        if rel is None or not rel.get("Type", "").endswith("/worksheet"):
            continue  
        target = rel.get("Target")
        if target.startswith("/"):
            part_name = target.lstrip("/")
        else:
            part_name = posixpath.normpath(posixpath.join(folder, target))
        found.append((sheet.get("name"), part_name))
    return found


def _sheet_names(archive):
    return [s.get("name") for s in _workbook_xml(archive).iter() if s.tag.endswith("}sheet")]


def _scan_xml(filename):
    from defusedxml.ElementTree import iterparse

    error_details = {err: [] for err in EXCEL_ERRORS}
    formula_count = 0
    merge_checks = 0

    with zipfile.ZipFile(filename) as archive:
        shared_errors, shared_equals = {}, set()
        if "xl/sharedStrings.xml" in archive.namelist():
            with archive.open("xl/sharedStrings.xml") as part:
                index = 0
                for _, node in iterparse(part):
                    if node.tag != f"{_MAIN_NS}si":
                        continue
                    text = _rich_text(node).replace("x005F_", "")
                    err = _error_in(text)
                    if err:
                        shared_errors[index] = err
                    if text.startswith("="):
                        shared_equals.add(index)
                    index += 1
                    node.clear()

        for sheet_name, part_name in _worksheets(archive):
            found = []
            xml = archive.read(part_name)
            merged = _merged_ranges(xml)
            for _, node in iterparse(io.BytesIO(xml)):
                if node.tag == f"{_MAIN_NS}row":
                    node.clear()
                if node.tag != f"{_MAIN_NS}c":
                    continue
                if node.get("r") is None:
                    raise ValueError("a cell without its address")
                formula = node.find(f"{_MAIN_NS}f")
                is_formula = formula is not None and formula.get("t") != "dataTable"
                err = None
                cell_type = node.get("t", "n")
                if cell_type == "s":
                    index = int(node.findtext(f"{_MAIN_NS}v"))
                    err = shared_errors.get(index)
                    is_formula = is_formula or (formula is None and index in shared_equals)
                elif cell_type not in ("n", "b", "d"):
                    inline = node.find(f"{_MAIN_NS}is")
                    text = node.findtext(f"{_MAIN_NS}v") if inline is None else _rich_text(inline)
                    err = _error_in(text or "")
                    is_formula = is_formula or (formula is None and (text or "").startswith("="))
                if not is_formula and not err:
                    continue
                row, column = _row_major(node.get("r"))
                merge_checks += len(merged)
                if merge_checks > MAX_MERGE_CHECKS:
                    raise ValueError("too many merged ranges for this many cells")
                if _hidden_by_a_merge(merged, row, column):
                    continue
                formula_count += is_formula
                if err:
                    found.append(((row, column), err, node.get("r")))
            for _, err, coordinate in sorted(found):
                error_details[err].append(f"{sheet_name}!{coordinate}")

    return error_details, formula_count


def _scan_with_openpyxl(filename):
    from openpyxl import load_workbook
    from openpyxl.worksheet.formula import ArrayFormula

    error_details = {err: [] for err in EXCEL_ERRORS}
    wb = load_workbook(filename, data_only=True)
    for sheet_name in wb.sheetnames:
        ws = wb[sheet_name]
        for cell in _existing_cells(ws):
            if isinstance(cell.value, str):
                err = _error_in(cell.value)
                if err:
                    error_details[err].append(f"{sheet_name}!{cell.coordinate}")
    wb.close()

    wb_formulas = load_workbook(filename, data_only=False)
    formula_count = 0
    for sheet_name in wb_formulas.sheetnames:
        ws = wb_formulas[sheet_name]
        for cell in _existing_cells(ws):
            v = cell.value
            if isinstance(v, ArrayFormula):
                v = v.text
            if isinstance(v, str) and v.startswith("="):
                formula_count += 1
    wb_formulas.close()

    return error_details, formula_count


def _sheet_names_too_long(filename):
    try:
        with zipfile.ZipFile(filename) as archive:
            return [name for name in _sheet_names(archive) if len(name or "") > 31]
    except Exception:  
        return []


def _report(filename, found=None):
    try:
        try:
            error_details, formula_count = _scan_xml(filename)
        except Exception:  
            error_details, formula_count = _scan_with_openpyxl(filename)
    except Exception as e:  
        return {"error": str(e)}

    found = found or {}
    kept = found.get("not_computed", [])
    apart = set(kept) | set(found.get("#NAME?", ()))
    in_file = [where for where in error_details["#NAME?"] if where not in apart]
    error_details["#NAME?"] = in_file + found.get("#NAME?", [])
    for error in EXCEL_ERRORS:
        if error != "#NAME?":
            error_details[error] += found.get(error, [])
    error_details[UNBALANCED] = found.get(UNBALANCED, [])
    error_details[TOO_LONG] = _sheet_names_too_long(filename)

    total_errors = sum(len(locations) for locations in error_details.values())
    result = {
        "status": "success" if total_errors == 0 else "errors_found",
        "total_errors": total_errors,
        "error_summary": {},
    }

    for err_type, locations in error_details.items():
        if locations:
            entry = {"count": len(locations), "locations": locations[:MAX_LOCATIONS]}
            if len(locations) > MAX_LOCATIONS:
                entry["locations_truncated"] = len(locations) - MAX_LOCATIONS
            result["error_summary"][err_type] = entry

    result["total_formulas"] = formula_count
    if kept:
        result["not_computed"] = {"count": len(kept), "locations": kept[:MAX_LOCATIONS]}
        if len(kept) > MAX_LOCATIONS:
            result["not_computed"]["locations_truncated"] = len(kept) - MAX_LOCATIONS
    return result



MAX_ARRAY_CELLS = 1_000_000

_ATTRS = rb"""((?:[^>"']|"[^"]*"|'[^']*')*?)"""  
_ROW_OR_CELL_RE = re.compile(
    rb"<((?:\w+:)?)(?:row(?=[\s/>])" + _ATTRS + rb"/?>"
    rb"|c(?=[\s/>])" + _ATTRS + rb"(?:/>|>(.*?)</\1c\s*>))",
    re.S,
)
_F_RE = re.compile(rb"<(?:\w+:)?f(?=[\s/>])" + _ATTRS + rb"(?:/>|>(.*?)</(?:\w+:)?f\s*>)", re.S)
_V_RE = re.compile(rb"<(?:\w+:)?v(?=[\s/>])[^>]*?(?:/>|>(.*?)</(?:\w+:)?v\s*>)", re.S)
_T_OR_VM_RE = re.compile(rb"""\s(?:t|vm)\s*=\s*(?:"[^"]*"|'[^']*')""")
_EXT_LST_RE = re.compile(rb"<(?:\w+:)?extLst\b.*</(?:\w+:)?extLst\s*>", re.S)
_NAME_ERROR = (b"e", b"#NAME?")
_STRING_RE = re.compile(r'"[^"]*"')  
_QUOTED_RE = re.compile(r""""[^"]*"|'[^']*'|\[[^\[\]]*\]""")
_CALL_RE = re.compile(r"(?<![\w.])([A-Za-z_][\w.]*)\(")
_DELIMS = r"\s+\-*/^&=<>(),;:!%{}#@~|"  
_WORD_RE = re.compile(rf"(?<![^{_DELIMS}])[^{_DELIMS}]+(?![^{_DELIMS}]|[(!])")
_EXTERNAL_REF_RE = re.compile(r"""(?<![\w"\[])'?\[[1-9]\d*\][^!"\[\]]*'?!""")
_PREFIX_RE = re.compile(r"^(?:_xlfn\.|_xlws\.)+", re.I)  
UNBALANCED = "unbalanced brackets"
TOO_LONG = "sheet name over 31 characters"
_STORED_BARE = frozenset(
    "CUBEVALUE CUBEMEMBER CUBESET CUBESETCOUNT CUBERANKEDMEMBER CUBEKPIMEMBER CUBEMEMBERPROPERTY "
    "RTD CALL DBCS PHONETIC REGISTER.ID SQL.REQUEST USDOLLAR BAHTTEXT ECMA.CEILING".split()
)
LIBREOFFICE_LACKS = _STORED_BARE | frozenset(
    "XLOOKUP XMATCH SORT SORTBY FILTER UNIQUE SEQUENCE RANDARRAY LET LAMBDA MAP REDUCE SCAN "
    "MAKEARRAY BYROW BYCOL ISOMITTED TEXTBEFORE TEXTAFTER TEXTSPLIT VSTACK HSTACK TOROW TOCOL "
    "WRAPROWS WRAPCOLS TAKE DROP CHOOSEROWS CHOOSECOLS EXPAND VALUETOTEXT ARRAYTOTEXT REGEXTEST "
    "REGEXEXTRACT REGEXREPLACE PERCENTOF GROUPBY PIVOTBY TRIMRANGE IMAGE STOCKHISTORY FIELDVALUE "
    "PY COPILOT TRANSLATE DETECTLANGUAGE ANCHORARRAY SINGLE BINOM.DIST.RANGE IMCOSH IMCOT IMCSC "
    "IMCSCH IMSEC IMSECH IMSINH IMTAN QUERYSTRING".split()
)


def _attr_re(name):
    return re.compile(rb"\s" + name + rb"""\s*=\s*(?:"([^"]*)"|'([^']*)')""")


_R_RE, _T_RE, _REF_RE, _SI_RE = _attr_re(b"r"), _attr_re(b"t"), _attr_re(b"ref"), _attr_re(b"si")


def _attr(pattern, attrs):
    m = pattern.search(attrs)
    if m is None:
        return None
    return m[1] if m[1] is not None else m[2]


def _sheet_data_span(xml):
    if b"<!" in xml:  
        return None
    parser = expat.ParserCreate(namespace_separator="}")
    depth, found = [0], []

    def start(name, _attributes):
        depth[0] += 1
        if depth[0] == 2 and name == _MAIN_NS[1:] + "sheetData" and not found:
            found.append(parser.CurrentByteIndex)

    def end(name):
        if depth[0] == 2 and name == _MAIN_NS[1:] + "sheetData" and len(found) == 1:
            found.append(parser.CurrentByteIndex)
        depth[0] -= 1

    parser.StartElementHandler, parser.EndElementHandler = start, end
    parser.Parse(xml, True)
    return tuple(found) if len(found) == 2 else None


def _cells(xml):
    span = _sheet_data_span(xml)
    row = column = 0
    for m in _ROW_OR_CELL_RE.finditer(xml, *span) if span else ():
        if m[3] is None:
            number = _attr(_R_RE, m[2])
            row, column = int(number) if number else row + 1, 0
            continue
        ref = _attr(_R_RE, m[3])
        if ref:
            row, column = _row_major(ref.decode())
        else:
            column += 1
        yield row, column, m


def _sheet_xml(archive, part_name):
    xml = archive.read(part_name)
    _utf8_or_refuse(xml, part_name)
    body = xml[3:] if xml.startswith(b"\xef\xbb\xbf") else xml
    if b"<!" in xml or body.count(b"<?") > bool(re.match(rb"<\?xml\s", body)):
        raise ValueError(
            f"{part_name} holds a comment, CDATA, a DTD or a processing instruction, which this "
            "script cannot edit. Load and save the workbook with openpyxl first, or leave it as is"
        )
    try:
        expat.ParserCreate().Parse(xml, True)
    except expat.ExpatError as e:
        raise ValueError(f"{part_name} is not well-formed XML: {e}") from None
    return xml


def _array_cells(xml, budget):
    cells = {}
    for f in _F_RE.finditer(xml):
        if _attr(_T_RE, f[1]) not in (b"array", b"dataTable"):
            continue
        first, _, last = (_attr(_REF_RE, f[1]) or b"").decode().partition(":")
        if not last:
            continue
        (top, left), (bottom, right) = _row_major(first), _row_major(last)
        if bottom < top or right < left:
            continue
        if len(cells) + (bottom - top + 1) * (right - left + 1) > budget:
            continue
        cells.update(
            ((r, c), (top, left)) for r in range(top, bottom + 1) for c in range(left, right + 1)
        )
    return cells


def _computed(copy_path, array_cells, names):
    computed, lacked = {}, {}
    with zipfile.ZipFile(copy_path) as archive:
        strings = None
        its_names = _sheet_names(archive)
        by_name = {ours.casefold(): ours for ours in names}
        ours = {its: by_name[its.casefold()] for its in its_names if its.casefold() in by_name}
        if len(its_names) == len(names):
            for its, in_that_place in zip(its_names, names):
                if its not in ours and in_that_place not in ours.values():
                    ours[its] = in_that_place
        for name, part_name in _worksheets(archive):
            name = ours.get(name, name)
            cells, lacks = computed.setdefault(name, {}), lacked.setdefault(name, set())
            wanted = array_cells.get(name, ())
            for row, column, m in _cells(archive.read(part_name)):
                content = m[4] or b""
                if (row, column) not in wanted and not _F_RE.search(content):
                    continue
                v = _V_RE.search(content)
                kind, text = _attr(_T_RE, m[3]) or b"n", v and v[1]
                if text is not None and kind == b"s":
                    if strings is None:
                        shared = _xml(archive.read("xl/sharedStrings.xml"))
                        strings = [_rich_text(si) for si in shared.iter(f"{_MAIN_NS}si")]
                    kind, text = b"str", html.escape(strings[int(text)], quote=False).encode()
                f = _F_RE.search(content)
                its_formula = (f and f[2]) or b""
                if re.search(rb"[a-z]", its_formula):  
                    called = [_PREFIX_RE.sub("", n) for n in _called(_text(its_formula))]
                    if any(n != n.upper() and n.upper() in LIBREOFFICE_LACKS for n in called):
                        lacks.add((row, column))
                    if _calls_its_own(_text(its_formula)):
                        kind, text = _NAME_ERROR
                if text is not None and (kind == b"str" or (text and kind in (b"n", b"b", b"e"))):
                    cells[row, column] = (kind, text)
    return computed, lacked


def _same_value(old_kind, old, kind, text):
    if old is None:
        return False
    if (old_kind, old) == (kind, text):
        return True
    if {old_kind, kind} <= {b"n", b"b"}:
        try:
            return math.isclose(float(old), float(text), rel_tol=1e-14, abs_tol=1e-12)
        except ValueError:
            return False
    return old_kind == kind and html.unescape(old.decode()) == html.unescape(text.decode())


def _cell_with_value(m, f, kind, text):
    p = m[1] or b""
    attrs = _T_OR_VM_RE.sub(b"", m[3])
    if kind != b"n":
        attrs += b' t="' + kind + b'"'
    kept = b"" if f is None else m[4][: f.end()]
    ext_lst = _EXT_LST_RE.search(m[4] or b"")
    rest = ext_lst[0] if ext_lst else b""
    return b"<%sc%s>%s<%sv>%s</%sv>%s</%sc>" % (p, attrs, kept, p, text, p, rest, p)


def _coordinate(row, column):
    letters = ""
    while column:
        column, index = divmod(column - 1, 26)
        letters = chr(ord("A") + index) + letters
    return f"{letters}{row}"


def _text(formula):
    text = formula.decode()
    for entity, character in (("&lt;", "<"), ("&gt;", ">"), ("&quot;", '"'), ("&apos;", "'")):
        text = text.replace(entity, character)
    return text.replace("&amp;", "&")  


def _called(formula):
    names = _CALL_RE.findall(_QUOTED_RE.sub("", formula))
    return [name for name in names if not name.lower().startswith("_xlpm.")]


def _lacking(name):
    bare = _PREFIX_RE.sub("", name)
    if bare.upper() not in LIBREOFFICE_LACKS:
        return None
    return bare != name or bare.upper() in _STORED_BARE


def _calls_its_own(formula):
    names = [_PREFIX_RE.sub("", name) for name in _called(formula)]
    return any(name != name.upper() and name != name.lower() for name in names)


def _unbalanced(formula):
    bare = _QUOTED_RE.sub("", formula)
    return bare.count("(") != bare.count(")")


def _reads_another_workbook(formula, reaching):
    plain = _STRING_RE.sub("", formula)
    if _EXTERNAL_REF_RE.search(plain):
        return True
    words = _WORD_RE.findall(_QUOTED_RE.sub("", plain)) if reaching else ()
    return any(word.lower() in reaching for word in words)


def _names_reaching_another_workbook(archive):
    reaching, used_by = set(), {}
    for name in _workbook_xml(archive).iter(f"{_MAIN_NS}definedName"):
        key, plain = name.get("name", "").lower(), _STRING_RE.sub("", name.text or "")
        if _EXTERNAL_REF_RE.search(plain):
            reaching.add(key)
        for word in _WORD_RE.findall(_QUOTED_RE.sub("", plain)):
            used_by.setdefault(word.lower(), set()).add(key)
    todo = list(reaching)
    while todo:  
        for user in used_by.get(todo.pop(), ()):
            if user not in reaching:
                reaching.add(user)
                todo.append(user)
    return reaching


def _verdict(formula, reaching=frozenset()):
    lacking = [_lacking(name) for name in _called(formula)]
    if False in lacking:
        return "mistake"
    if _reads_another_workbook(formula, reaching):
        return "link"
    return "lacks" if True in lacking else None


def _splice(xml, computed, lacked, array_cells, sheet_name, reaching, found):
    out, done = [], 0
    filling, filled, shared = set(), set(), {}
    for row, column, m in _cells(xml):
        content = m[4] or b""
        f = _F_RE.search(content)
        if f is None and array_cells.get((row, column)) not in filling:
            continue  
        v = _V_RE.search(content, f.end() if f else 0)
        old = v and (v[1] or b"")  
        kind = _attr(_T_RE, m[3]) or b"n"
        new = computed.get((row, column))
        verdict = None
        if f is None:
            filled.add((row, column))
        else:
            where = f"{sheet_name}!{_coordinate(row, column)}"
            text, si = _text(f[2] or b""), _attr(_SI_RE, f[1])
            verdict = _verdict(text, reaching) if text else shared.get(si)
            if text and si:
                shared[si] = verdict
            if verdict == "lacks" and (row, column) not in lacked:
                verdict = None  
            if _unbalanced(text):
                found[UNBALANCED].append(where)
        if verdict or new is None or new == _NAME_ERROR:
            if f is not None:
                has_value = old or (old is not None and kind == b"str")
                held = has_value and (kind, old) != _NAME_ERROR
                no_value_held = not verdict and new == _NAME_ERROR and not held
                mistake = verdict == "mistake" or no_value_held
                found["#NAME?" if mistake else "not_computed"].append(where)
            continue
        if f is not None:
            filling.add((row, column))
        if _same_value(kind, old, *new):
            continue
        out += [xml[done : m.start()], _cell_with_value(m, f, *new)]
        done = m.end()
    for cell, first in array_cells.items():
        new = computed.get(cell)
        held_by_the_sheet = cell == first or cell in filled
        if first in filling and not held_by_the_sheet and new and new[0] == b"e":
            error = new[1].decode()
            if error != "#NAME?" and error in EXCEL_ERRORS:
                found.setdefault(error, []).append(f"{sheet_name}!{_coordinate(*cell)}")
    if not out:
        return xml
    out.append(xml[done:])
    return b"".join(out)


def _replace_parts(path, parts):
    handle, new_path = tempfile.mkstemp(
        dir=os.path.dirname(path), prefix=".recalc-", suffix=Path(path).suffix
    )
    try:
        with (
            os.fdopen(handle, "wb") as out,
            zipfile.ZipFile(path) as old,
            zipfile.ZipFile(out, "w") as new,
        ):
            new.comment = old.comment
            for item in old.infolist():
                if item.filename in parts:
                    new.writestr(item, parts[item.filename])
                    continue
                with old.open(item) as source, new.open(copy.copy(item), "w") as target:
                    shutil.copyfileobj(source, target)
        status = os.stat(path)
        with contextlib.suppress(OSError, AttributeError):
            os.chown(new_path, status.st_uid, status.st_gid)
        shutil.copystat(path, new_path)
        os.utime(new_path)
        os.replace(new_path, path)
    except BaseException:
        with contextlib.suppress(OSError):
            os.unlink(new_path)
        raise


def _write_values(path, copy_path):
    with zipfile.ZipFile(path) as archive:
        sheets = _worksheets(archive)
        reaching = _names_reaching_another_workbook(archive)
        array_cells = {}
        for name, part_name in sheets:
            budget = MAX_ARRAY_CELLS - sum(map(len, array_cells.values()))
            array_cells[name] = _array_cells(_sheet_xml(archive, part_name), budget)
        computed, lacked = _computed(copy_path, array_cells, _sheet_names(archive))
        parts, found = {}, {"#NAME?": [], UNBALANCED: [], "not_computed": []}
        for name, part_name in sheets:
            xml = archive.read(part_name)  
            if name not in computed and _F_RE.search(xml):
                raise ValueError(
                    f"LibreOffice's copy has no sheet called {name!r}: it renames or drops some "
                    "sheets, such as one whose name is over 31 characters, so this sheet's "
                    "formulas cannot be recalculated"
                )
            cells, lacks = computed.get(name, {}), lacked.get(name, ())
            new = _splice(xml, cells, lacks, array_cells[name], name, reaching, found)
            if new is not xml:
                try:
                    expat.ParserCreate().Parse(new, True)
                except expat.ExpatError as e:
                    raise ValueError(f"editing {part_name} as text broke its XML ({e})") from None
                parts[part_name] = new
    if parts:
        _replace_parts(path, parts)
    return found


def main():
    signal.signal(signal.SIGTERM, lambda *_: sys.exit(143))
    args = [a for a in sys.argv[1:] if a != "--force"]
    force = "--force" in sys.argv[1:]

    if not args:
        print("Usage: python recalc.py <excel_file> [timeout_seconds] [--force]")
        print("\nRecalculates all formulas in an Excel file using LibreOffice")
        print("LibreOffice works on a copy; only the values it computes are written into the file.")
        print("\nReturns JSON with error details:")
        print("  - status: 'success' or 'errors_found'")
        print("  - total_errors: Total number of Excel errors found")
        print("  - total_formulas: Number of formulas in the file")
        print("  - error_summary: Breakdown by error type with locations")
        print("    - #VALUE!, #DIV/0!, #REF!, #NAME?, #NULL!, #NUM!, #N/A, unbalanced brackets")
        print("  - not_computed: only if LibreOffice could not compute some formulas: a function")
        print("    it lacks, or a link to another workbook. Those cells are left as they were, and")
        print("    Excel computes them when it opens a file openpyxl saved. A sound formula that")
        print("    depends on one of them reports #NAME? too")
        print("\nOn any failure the JSON has an 'error' key and no 'status'.")
        print("--force is accepted and ignored.")
        sys.exit(1)

    filename = args[0]
    try:
        timeout = int(args[1]) if len(args) > 1 else 30
    except ValueError:
        result = {"error": f"timeout must be an integer number of seconds, got {args[1]!r}"}
        print(json.dumps(result, indent=2))
        sys.exit(1)

    result = recalc(filename, timeout, force=force)
    print(json.dumps(result, indent=2))
    sys.exit(1 if "error" in result else 0)


if __name__ == "__main__":
    main()
