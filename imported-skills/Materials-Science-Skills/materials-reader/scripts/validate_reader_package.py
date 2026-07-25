from __future__ import annotations

import argparse
import csv
import json
import re
import sys
from pathlib import Path


try:
    from build_reader_package import CSV_HEADERS, REQUIRED_FILES
except ImportError:  # pragma: no cover - supports direct import by tests
    import importlib.util

    _builder_path = Path(__file__).with_name("build_reader_package.py")
    _spec = importlib.util.spec_from_file_location("build_reader_package", _builder_path)
    _builder = importlib.util.module_from_spec(_spec)
    _spec.loader.exec_module(_builder)
    CSV_HEADERS = _builder.CSV_HEADERS
    REQUIRED_FILES = _builder.REQUIRED_FILES


QA_SECTIONS = [
    "## Source Coverage",
    "## Figure/Table Coverage",
    "## Citation Handoff",
    "## Figure Handoff",
    "## Missing Evidence",
    "## Overclaim Risk",
    "## Absolute Path Leakage",
    "## Final Status",
]

OBSIDIAN_SECTIONS = [
    "## Source Anchors",
    "## Evidence Chain",
    "## Figure And Table Cards",
    "## Citation Handoff",
    "## Figure Handoff",
    "## Review Handoff",
    "## QA Flags",
]

JSON_FILES = [
    "package_manifest.json",
    "source_map.json",
    "assets/visual_asset_report.json",
]

ABSOLUTE_PATH_PATTERNS = [
    re.compile(r"[A-Za-z]:\\(?:Users|Documents|Desktop|Downloads|OneDrive)\\"),
    re.compile(r"/(?:Users|home|mnt|Volumes)/[^ \n\r\t]+"),
]


def _read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def _check_required_files(package_dir: Path, errors: list[str]) -> None:
    for relative_path in ["package_manifest.json", *REQUIRED_FILES]:
        path = package_dir / relative_path
        if not path.exists():
            errors.append(f"Missing required file: {relative_path}")


def _check_json(package_dir: Path, errors: list[str]) -> None:
    for relative_path in JSON_FILES:
        path = package_dir / relative_path
        if not path.exists():
            continue
        try:
            json.loads(_read_text(path))
        except json.JSONDecodeError as exc:
            errors.append(f"Invalid JSON in {relative_path}: {exc}")


def _check_csv_headers(package_dir: Path, errors: list[str]) -> None:
    for relative_path, expected_header in CSV_HEADERS.items():
        path = package_dir / relative_path
        if not path.exists():
            continue
        with path.open("r", encoding="utf-8", newline="") as handle:
            reader = csv.reader(handle)
            actual_header = next(reader, [])
        if actual_header != expected_header:
            errors.append(
                f"{relative_path} header mismatch: expected {expected_header}, got {actual_header}"
            )


def _check_markdown_sections(
    package_dir: Path,
    relative_path: str,
    sections: list[str],
    errors: list[str],
) -> None:
    path = package_dir / relative_path
    if not path.exists():
        return
    text = _read_text(path)
    missing = [section for section in sections if section not in text]
    if missing:
        errors.append(f"{relative_path} missing sections: {', '.join(missing)}")


def _check_absolute_path_leakage(package_dir: Path, errors: list[str]) -> None:
    for path in package_dir.rglob("*"):
        if not path.is_file():
            continue
        if path.suffix.lower() in {".png", ".jpg", ".jpeg", ".pdf"}:
            continue
        try:
            text = _read_text(path)
        except UnicodeDecodeError:
            continue
        for pattern in ABSOLUTE_PATH_PATTERNS:
            if pattern.search(text):
                errors.append(
                    f"Absolute path leakage detected in {path.relative_to(package_dir)}"
                )
                break


def validate_reader_package(package_dir: Path) -> dict[str, object]:
    """Validate a reader package scaffold without third-party dependencies."""
    package_dir = Path(package_dir)
    errors: list[str] = []
    warnings: list[str] = []
    if not package_dir.exists():
        return {
            "status": "fail",
            "package_dir": str(package_dir),
            "errors": [f"Package directory does not exist: {package_dir}"],
            "warnings": [],
        }

    _check_required_files(package_dir, errors)
    _check_json(package_dir, errors)
    _check_csv_headers(package_dir, errors)
    _check_markdown_sections(package_dir, "qa_report.md", QA_SECTIONS, errors)
    _check_markdown_sections(package_dir, "obsidian_note.md", OBSIDIAN_SECTIONS, errors)
    _check_absolute_path_leakage(package_dir, errors)

    return {
        "status": "fail" if errors else "pass",
        "package_dir": str(package_dir),
        "errors": errors,
        "warnings": warnings,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Validate a reader package.")
    parser.add_argument("package_dir")
    parser.add_argument("--json", action="store_true", dest="as_json")
    args = parser.parse_args(argv)

    report = validate_reader_package(Path(args.package_dir))
    if args.as_json:
        print(json.dumps(report, ensure_ascii=False, indent=2))
    else:
        for error in report["errors"]:
            print(error, file=sys.stderr)
        print(report["status"])
    return 0 if report["status"] == "pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())
