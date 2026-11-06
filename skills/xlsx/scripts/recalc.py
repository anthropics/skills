"""
Excel Formula Recalculation Script
Recalculates all formulas in an Excel file with LibreOffice, or with the xlcalc
engine (Node) on machines that have no LibreOffice.
"""

import contextlib
import json
import os
import platform
import re
import shutil
import subprocess
import sys
import tempfile
import time
import zipfile
from pathlib import Path

from office.soffice import get_soffice_env, run_soffice

from openpyxl import load_workbook

MACRO_FILENAME = "Module1.xba"
SOFFICE_MISSING = (
    "soffice not found on PATH; the LibreOffice backend needs it (run with "
    "--backend xlcalc instead, or install LibreOffice)"
)

MAX_LOCATIONS = 100

LIBREOFFICE = "libreoffice"
XLCALC = "xlcalc"
BACKENDS = ("auto", LIBREOFFICE, XLCALC)
XLCALC_HELPER = Path(__file__).resolve().parent / "recalc_xlcalc.mjs"

BACKEND_REPORT_KEYS = (
    "values_written",
    "values_missing",
    "missing_locations",
    "missing_locations_truncated",
    "unchanged",
    "compute_ms",
)

EXCEL_ERRORS = (
    "#VALUE!",
    "#DIV/0!",
    "#REF!",
    "#NAME?",
    "#NULL!",
    "#NUM!",
    "#N/A",
)

EXTERNAL_REF_RE = re.compile(r"""(?<![\w"\[])'?\[\d+\][^!"\[\]]*'?!""")

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


def external_links_at_risk(filename):
    try:
        with zipfile.ZipFile(filename) as archive:
            names = archive.namelist()
    except (zipfile.BadZipFile, OSError):
        return []
    if not any(n.startswith("xl/externalLinks/") for n in names):
        return []

    with contextlib.ExitStack() as stack:
        formulas = load_workbook(filename, data_only=False)
        stack.callback(formulas.close)
        values = load_workbook(filename, data_only=True)
        stack.callback(values.close)

        external_names = [
            name
            for name, dn in formulas.defined_names.items()
            if isinstance(getattr(dn, "value", None), str) and EXTERNAL_REF_RE.search(dn.value)
        ]
        name_re = (
            re.compile(r"\b(" + "|".join(re.escape(n) for n in external_names) + r")\b")
            if external_names
            else None
        )

        at_risk = []
        for sheet in formulas.sheetnames:
            ws = formulas[sheet]
            if not hasattr(ws, "iter_rows"):
                continue
            cached = values[sheet]
            for row in ws.iter_rows():
                for cell in row:
                    v = cell.value
                    if not (isinstance(v, str) and v.startswith("=")):
                        continue
                    reaches_out = EXTERNAL_REF_RE.search(v) or (name_re and name_re.search(v))
                    if reaches_out and cached[cell.coordinate].value is None:
                        at_risk.append(f"{sheet}!{cell.coordinate}")
        return at_risk


def scan_workbook(filename):
    """Report the error cells and the formula count of a file that was just recalculated."""
    error_details = {err: [] for err in EXCEL_ERRORS}
    formula_count = 0

    with contextlib.ExitStack() as stack:
        values = load_workbook(filename, data_only=True)
        stack.callback(values.close)
        for sheet_name in values.sheetnames:
            ws = values[sheet_name]
            if not hasattr(ws, "iter_rows"):
                continue
            for row in ws.iter_rows():
                for cell in row:
                    if cell.value is not None and isinstance(cell.value, str):
                        for err in EXCEL_ERRORS:
                            if err in cell.value:
                                error_details[err].append(f"{sheet_name}!{cell.coordinate}")
                                break

        wb_formulas = load_workbook(filename, data_only=False)
        stack.callback(wb_formulas.close)
        for sheet_name in wb_formulas.sheetnames:
            ws = wb_formulas[sheet_name]
            if not hasattr(ws, "iter_rows"):
                continue
            for row in ws.iter_rows():
                for cell in row:
                    if (
                        cell.value
                        and isinstance(cell.value, str)
                        and cell.value.startswith("=")
                    ):
                        formula_count += 1

    total_errors = sum(len(locations) for locations in error_details.values())
    result = {
        "status": "success" if total_errors == 0 else "errors_found",
        "total_errors": total_errors,
        "error_summary": {},
        "total_formulas": formula_count,
    }

    for err_type, locations in error_details.items():
        if locations:
            entry = {"count": len(locations), "locations": locations[:MAX_LOCATIONS]}
            if len(locations) > MAX_LOCATIONS:
                entry["locations_truncated"] = len(locations) - MAX_LOCATIONS
            result["error_summary"][err_type] = entry

    return result


def run_xlcalc(filename, timeout=30):
    """Recalculate the file in place with the xlcalc engine and return its JSON report."""
    node = shutil.which("node")
    if not node:
        return {
            "error": "node not found on PATH; the xlcalc recalc backend needs Node 20.19 "
            "or newer. Install Node, or install LibreOffice and use --backend libreoffice."
        }
    if not XLCALC_HELPER.exists():
        return {"error": f"recalc helper is missing: {XLCALC_HELPER}"}

    try:
        completed = subprocess.run(
            [node, str(XLCALC_HELPER), str(Path(filename).resolve())],
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        return {
            "error": f"xlcalc timed out after {timeout}s; formulas were NOT recalculated. "
            "Re-run with a longer timeout."
        }

    stdout = (completed.stdout or "").strip()
    if not stdout:
        detail = (completed.stderr or "").strip() or f"node exited {completed.returncode}"
        return {"error": f"xlcalc produced no report: {detail}"}

    try:
        report = json.loads(stdout.splitlines()[-1])
    except json.JSONDecodeError:
        return {"error": f"xlcalc produced unreadable output: {stdout[:400]}"}

    if "error" in report:
        return report
    report["backend"] = XLCALC
    return report


def choose_backend(requested):
    if requested in (LIBREOFFICE, XLCALC):
        return requested
    return LIBREOFFICE if shutil.which("soffice") else XLCALC


def scan_or_error(filename):
    """scan_workbook, but a file it cannot read becomes a JSON-able error, never a traceback."""
    try:
        return scan_workbook(filename)
    except Exception as e:
        return {"error": f"Could not read {filename} after recalculating it: {e}"}


def merge_backend_report(scanned, report):
    if "error" in scanned:
        return scanned
    for key in BACKEND_REPORT_KEYS:
        scanned[key] = report.get(key)
    return scanned


def recalc(filename, timeout=30, force=False, backend="auto"):
    if not Path(filename).exists():
        return {"error": f"File {filename} does not exist"}

    if backend not in BACKENDS:
        return {"error": f"Unknown backend {backend!r}; choose from {', '.join(BACKENDS)}"}

    abs_path = str(Path(filename).absolute())

    if not os.access(abs_path, os.W_OK):
        return {"error": f"{filename} is not writable; recalculation rewrites the file in place"}

    chosen = choose_backend(backend)

    if not force:
        try:
            at_risk = external_links_at_risk(filename)
        except Exception as e:
            return {"error": f"Could not inspect {filename} for external links: {e}"}
        if at_risk:
            shown = at_risk[:MAX_LOCATIONS]
            return {
                "error": (
                    "Refusing to recalculate: this workbook links to another workbook, and "
                    f"{len(at_risk)} linked cell(s) have lost their cached value (openpyxl strips "
                    "these on save). Recalculating would resolve them to #NAME? and delete the "
                    "external links for good. Copy those cells' values from the original file "
                    "before saving, or pass --force to accept the loss. Charts and conditional "
                    "formats can hold external references too, so this list may not be exhaustive."
                ),
                "external_link_cells": shown,
                "external_link_cells_truncated": max(0, len(at_risk) - len(shown)),
            }

    if chosen == XLCALC:
        report = run_xlcalc(filename, timeout)
        if "error" in report:
            return report
        scanned = merge_backend_report(scan_or_error(abs_path), report)
        scanned["backend"] = XLCALC
        if report.get("values_missing"):
            scanned["warning"] = (
                f"{report['values_missing']} formula cell(s) got no value from the engine and "
                "read back as blank; see missing_locations. Rewrite them with functions the "
                "engine evaluates, or recalculate with --backend libreoffice."
            )
        return scanned

    with tempfile.TemporaryDirectory(
        prefix="recalc-lo-profile-", ignore_cleanup_errors=True
    ) as profile_dir:
        result = _recalc_with_profile(filename, abs_path, timeout, Path(profile_dir))

    if backend == "auto" and "error" in result:
        fallback = run_xlcalc(filename, timeout)
        if "error" not in fallback:
            scanned = merge_backend_report(scan_or_error(abs_path), fallback)
            scanned["backend"] = XLCALC
            scanned["libreoffice_error"] = result["error"]
            return scanned
        return {
            "error": (
                f"Neither recalc backend worked. LibreOffice: {result['error']} "
                f"xlcalc: {fallback['error']}"
            )
        }
    return result


def _recalc_with_profile(filename, abs_path, timeout, profile_dir: Path):
    started = time.monotonic()
    if not shutil.which("soffice"):
        return {"error": SOFFICE_MISSING}
    try:
        get_soffice_env()
    except Exception as e:
        return {"error": f"Could not prepare the LibreOffice environment: {e}"}

    profile_url, err = setup_libreoffice_macro(profile_dir, timeout=timeout)
    if err:
        return {"error": err}

    timeout = max(5, int(timeout - (time.monotonic() - started)))

    before = _stamp(abs_path)

    cmd = [
        "soffice",
        "--headless",
        "--norestore",
        f"-env:UserInstallation={profile_url}",
        "vnd.sun.star.script:Standard.Module1.RecalculateAndSave?language=Basic&location=application",
        abs_path,
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

    if _stamp(abs_path) == before:
        return {
            "error": (
                "LibreOffice exited cleanly but never rewrote the file, so nothing was "
                "recalculated. Check that no other LibreOffice instance is running, then retry."
            )
        }

    try:
        scanned = scan_workbook(abs_path)
    except Exception as e:
        return {"error": str(e)}

    scanned["backend"] = LIBREOFFICE
    return scanned


def parse_args(argv):
    force = "--force" in argv
    rest = [a for a in argv if a != "--force"]
    backend = os.environ.get("XLSX_RECALC_BACKEND", "").strip().lower() or "auto"
    positional = []
    index = 0
    while index < len(rest):
        arg = rest[index]
        if arg == "--backend" and index + 1 < len(rest):
            backend = rest[index + 1].strip().lower()
            index += 2
            continue
        if arg.startswith("--backend="):
            backend = arg.split("=", 1)[1].strip().lower()
            index += 1
            continue
        positional.append(arg)
        index += 1
    return positional, backend, force


USAGE_LINES = [
    "Usage: python recalc.py <excel_file> [timeout_seconds] [--force]"
    " [--backend auto|libreoffice|xlcalc]",
    "",
    "Recalculates all formulas in an Excel file, rewriting the file in place.",
    "  auto (default): LibreOffice when soffice is on PATH, otherwise xlcalc through node.",
    "  XLSX_RECALC_BACKEND sets the backend for every run, the same as --backend.",
    "  The xlcalc backend needs `npm install xlcalc` (Node 20.19 or newer). The package is",
    "  looked up from the file's own directory, this skill's directory, the working",
    "  directory, and any path in XLSX_XLCALC_PATH.",
    "",
    "Returns JSON with error details:",
    "  - status: 'success' or 'errors_found'",
    "  - backend: 'libreoffice' or 'xlcalc'",
    "  - total_errors: Total number of Excel errors found",
    "  - total_formulas: Number of formulas in the file",
    "  - error_summary: Breakdown by error type with locations",
    "    - #VALUE!, #DIV/0!, #REF!, #NAME?, #NULL!, #NUM!, #N/A",
    "  - with xlcalc: values_missing and missing_locations name the formula cells the engine",
    "    could not answer, which stay blank",
    "",
    "On any failure the JSON has an 'error' key and no 'status'.",
    "--force recalculates even when it would destroy external links.",
]


def main():
    positional, backend, force = parse_args(sys.argv[1:])

    if not positional:
        for line in USAGE_LINES:
            print(line)
        sys.exit(1)

    if backend not in BACKENDS:
        print(json.dumps({"error": f"Unknown backend {backend!r}; choose from {', '.join(BACKENDS)}"}))
        sys.exit(1)

    filename = positional[0]
    timeout = int(positional[1]) if len(positional) > 1 else 30

    result = recalc(filename, timeout, force=force, backend=backend)
    print(json.dumps(result, indent=2))
    sys.exit(1 if "error" in result else 0)


if __name__ == "__main__":
    main()
