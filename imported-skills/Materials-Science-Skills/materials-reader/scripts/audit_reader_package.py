from __future__ import annotations

import argparse
import json
from pathlib import Path


try:
    from validate_reader_package import validate_reader_package
except ImportError:  # pragma: no cover
    import importlib.util

    _validator_path = Path(__file__).with_name("validate_reader_package.py")
    _spec = importlib.util.spec_from_file_location(
        "validate_reader_package", _validator_path
    )
    _validator = importlib.util.module_from_spec(_spec)
    _spec.loader.exec_module(_validator)
    validate_reader_package = _validator.validate_reader_package


def audit_reader_package(package_dir: Path) -> dict[str, object]:
    """Alias the validator for release-gate friendly naming."""
    return validate_reader_package(package_dir)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Audit a reader package.")
    parser.add_argument("package_dir")
    parser.add_argument("--json", action="store_true", dest="as_json")
    args = parser.parse_args(argv)

    report = audit_reader_package(Path(args.package_dir))
    if args.as_json:
        print(json.dumps(report, ensure_ascii=False, indent=2))
    else:
        for error in report["errors"]:
            print(error)
        print(report["status"])
    return 0 if report["status"] == "pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())
