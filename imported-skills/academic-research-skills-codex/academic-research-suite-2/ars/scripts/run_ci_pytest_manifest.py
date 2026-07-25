"""Unified runner for the pytest invocations CI exercises (issue #156).

Reads `scripts/_ci_pytest_manifest.toml` and executes
`python -m pytest <path> <args...> -v` for each entry. Each invocation is
wrapped in `::group::<id>` / `::endgroup::` annotations so GitHub Actions
collapses one log block per entry.

Failure semantics: the runner CONTINUES through every entry instead of
failing fast on the first non-zero exit, so a single PR sees every test
suite that broke (not just the first one). The aggregate exit code is
non-zero if any entry failed. The runner does NOT install pip deps — that
happens once at the workflow level via
`pip install -r requirements-dev.txt pytest`.

Local use:
    python scripts/run_ci_pytest_manifest.py            # run everything
    python scripts/run_ci_pytest_manifest.py --id <id>  # run one entry

The drift guard at scripts/check_ci_pytest_manifest.py validates the manifest
shape; this runner trusts the lint and does the minimum schema checks needed
to fail safely if the manifest is malformed.
"""
from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path

try:
    import tomllib
except ModuleNotFoundError:  # pragma: no cover - Python < 3.11 compatibility
    import tomli as tomllib


def _load_manifest(path: Path) -> list[dict]:
    if not path.exists():
        print(f"ERROR: manifest not found: {path}", file=sys.stderr)
        sys.exit(1)
    try:
        data = tomllib.loads(path.read_text(encoding="utf-8"))
    except tomllib.TOMLDecodeError as exc:
        print(f"ERROR: manifest parse error: {exc}", file=sys.stderr)
        sys.exit(1)
    entries = data.get("pytest", [])
    if not isinstance(entries, list):
        print("ERROR: manifest [[pytest]] must be an array of tables", file=sys.stderr)
        sys.exit(1)
    return entries


def _run_entry(entry: dict, root: Path) -> int:
    entry_id = entry.get("id", "<no-id>")
    entry_path = entry.get("path", "")
    entry_args = list(entry.get("args", []))

    cmd = [sys.executable, "-m", "pytest", entry_path, *entry_args, "-v"]
    print(f"::group::{entry_id}")
    print(f"# {' '.join(cmd)}")
    sys.stdout.flush()
    result = subprocess.run(cmd, cwd=str(root))
    print("::endgroup::")
    sys.stdout.flush()
    return result.returncode


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--manifest",
        default="scripts/_ci_pytest_manifest.toml",
        help="Path to the manifest TOML file (default: scripts/_ci_pytest_manifest.toml)",
    )
    parser.add_argument(
        "--root",
        default=".",
        help="Repo root pytest should run from (default: cwd)",
    )
    parser.add_argument(
        "--id",
        dest="only_id",
        default=None,
        help="Run a single named entry instead of the whole manifest (for local debug)",
    )
    args = parser.parse_args()

    manifest_path = Path(args.manifest)
    root = Path(args.root).resolve()

    entries = _load_manifest(manifest_path)

    if args.only_id is not None:
        matches = [e for e in entries if e.get("id") == args.only_id]
        if not matches:
            print(
                f"ERROR: --id {args.only_id!r} not found in manifest",
                file=sys.stderr,
            )
            return 1
        entries = matches

    failed: list[str] = []
    for entry in entries:
        rc = _run_entry(entry, root)
        if rc != 0:
            failed.append(str(entry.get("id", "<no-id>")))

    if failed:
        print(
            f"\nCI pytest manifest run FAILED on {len(failed)} entr(y/ies): "
            + ", ".join(failed),
            file=sys.stderr,
        )
        return 1
    print(f"\nCI pytest manifest run ok ({len(entries)} entr(y/ies)).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
