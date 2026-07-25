"""Drift guard for the unified pytest invocation manifest (issue #156).

Validates `scripts/_ci_pytest_manifest.toml` and the surrounding workflow:

1. every manifest entry's `path` exists on disk
2. `id` values are unique across entries
3. (path, args) tuples are unique across entries (catches accidental duplication
   that would silently double-run a test or bypass the manifest as a single
   source of truth; same path with DIFFERENT args is the legitimate -k case)
4. when present, `args` is a list of strings
5. `.github/workflows/spec-consistency.yml` contains no direct
   `pytest scripts/test_*.py` invocation outside the runner (the manifest
   would otherwise become a parallel list nobody updates)

Out of scope (deliberately, per issue #156):
- whether every `scripts/test_*.py` on disk is listed in the manifest
- `python3 -m unittest scripts.test_*` invocations (unittest is a separate
  runner family; renaming the manifest to `_ci_test_manifest.toml` would
  require also migrating those, which expands scope)
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

try:
    import tomllib
except ModuleNotFoundError:  # pragma: no cover - Python < 3.11 compatibility
    import tomli as tomllib


# Drift guard regex: catches direct pytest invocations on `scripts/test_*.py`
# files outside the manifest runner. Built to tolerate the bypass paths
# observed in dual-track review (gemini P1 + codex empirical probe):
#   - intermediate flags: `pytest -v scripts/test_x.py`, `pytest --tb=short ...`
#   - quoted paths: `pytest "scripts/test_x.py"`, `pytest 'scripts/...'`
#   - explicit relative prefix: `pytest ./scripts/test_x.py`
#   - alt invocation: `python -m pytest scripts/...`, `python3 -m pytest scripts/...`,
#     `py.test scripts/...`, `uv run pytest scripts/...`
# Line continuations (`pytest \<newline>scripts/...`) are handled by collapsing
# backslash-newline sequences before scanning (see `_validate_workflow`).
DIRECT_PYTEST_RE = re.compile(
    r"\b(?:py\.test|pytest)\b"      # invocation token (pytest or py.test)
    r"(?:\s+(?:-[^\s]+|--[^\s]+))*"  # zero or more flag args (short -x or long --x=y)
    r"\s+"                           # whitespace before path
    r"['\"]?"                        # optional quote
    r"(?:\./)?"                      # optional ./ prefix
    r"scripts/test_[A-Za-z0-9_]+\.py"
    r"['\"]?"                        # optional closing quote
)


def _fail(msg: str, errors: list[str]) -> None:
    errors.append(msg)


def _load_manifest(path: Path, errors: list[str]) -> list[dict] | None:
    if not path.exists():
        _fail(f"manifest not found: {path}", errors)
        return None
    try:
        data = tomllib.loads(path.read_text(encoding="utf-8"))
    except tomllib.TOMLDecodeError as exc:
        _fail(f"manifest parse error: {exc}", errors)
        return None
    entries = data.get("pytest", [])
    if not isinstance(entries, list):
        _fail("manifest [[pytest]] must be an array of tables", errors)
        return None
    return entries


ALLOWED_ENTRY_KEYS = {"id", "path", "args"}


def _validate_entries(entries: list[dict], root: Path, errors: list[str]) -> None:
    seen_ids: dict[str, int] = {}
    seen_invocations: dict[tuple, int] = {}
    for idx, entry in enumerate(entries):
        if not isinstance(entry, dict):
            _fail(f"entry #{idx}: not a table", errors)
            continue
        extra_keys = set(entry.keys()) - ALLOWED_ENTRY_KEYS
        if extra_keys:
            _fail(
                f"entry #{idx}: unknown keys {sorted(extra_keys)!r} "
                f"(allowed: {sorted(ALLOWED_ENTRY_KEYS)!r}). "
                f"Likely a typo — e.g. `arg` for `args` would silently broaden the test run.",
                errors,
            )
        entry_id = entry.get("id")
        entry_path = entry.get("path")
        entry_args = entry.get("args", [])

        if not isinstance(entry_id, str) or not entry_id:
            _fail(f"entry #{idx}: missing/invalid `id`", errors)
            continue
        if not isinstance(entry_path, str) or not entry_path:
            _fail(f"entry id={entry_id!r}: missing/invalid `path`", errors)
            continue
        if not isinstance(entry_args, list) or not all(
            isinstance(a, str) for a in entry_args
        ):
            _fail(
                f"entry id={entry_id!r}: `args` must be a list of strings "
                f"(got {type(entry_args).__name__})",
                errors,
            )
            continue

        if entry_id in seen_ids:
            _fail(
                f"duplicate id {entry_id!r}: appears at entries #{seen_ids[entry_id]} and #{idx}",
                errors,
            )
        else:
            seen_ids[entry_id] = idx

        invocation_key = (entry_path, tuple(entry_args))
        if invocation_key in seen_invocations:
            _fail(
                f"duplicate invocation: entry #{idx} (id={entry_id!r}) repeats "
                f"path={entry_path!r} args={entry_args!r} from entry #{seen_invocations[invocation_key]}",
                errors,
            )
        else:
            seen_invocations[invocation_key] = idx

        resolved = root / entry_path
        if not resolved.exists():
            _fail(
                f"entry id={entry_id!r}: path does not exist on disk: {entry_path}",
                errors,
            )


def _validate_workflow(workflow_path: Path, errors: list[str]) -> None:
    if not workflow_path.exists():
        _fail(f"workflow not found: {workflow_path}", errors)
        return
    text = workflow_path.read_text(encoding="utf-8")
    # Strip YAML comments before scanning so commented-out historical examples
    # don't trip the drift guard.
    stripped_lines = []
    for raw_line in text.splitlines():
        comment_idx = raw_line.find("#")
        if comment_idx >= 0:
            raw_line = raw_line[:comment_idx]
        stripped_lines.append(raw_line)
    stripped = "\n".join(stripped_lines)
    # Normalize bash line continuations (`pytest \<newline>scripts/...`) so the
    # regex sees one logical command per scan. Without this a developer could
    # split a bypass across two YAML lines and slip past the guard.
    stripped = stripped.replace("\\\n", " ")
    matches = DIRECT_PYTEST_RE.findall(stripped)
    if matches:
        for m in matches:
            _fail(
                f"direct pytest invocation in {workflow_path.name} (outside runner): {m!r}",
                errors,
            )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--manifest",
        default="scripts/_ci_pytest_manifest.toml",
        help="Path to the manifest TOML file (default: scripts/_ci_pytest_manifest.toml)",
    )
    parser.add_argument(
        "--workflow",
        default=".github/workflows/spec-consistency.yml",
        help="Path to spec-consistency workflow (default: .github/workflows/spec-consistency.yml)",
    )
    parser.add_argument(
        "--root",
        default=".",
        help="Repo root for resolving manifest `path` entries (default: cwd)",
    )
    args = parser.parse_args()

    errors: list[str] = []
    manifest_path = Path(args.manifest)
    workflow_path = Path(args.workflow)
    root = Path(args.root).resolve()

    entries = _load_manifest(manifest_path, errors)
    if entries is not None:
        _validate_entries(entries, root, errors)
    _validate_workflow(workflow_path, errors)

    if errors:
        for err in errors:
            print(f"ERROR: {err}", file=sys.stderr)
        print(f"\nCI pytest manifest lint FAILED ({len(errors)} issue(s)).", file=sys.stderr)
        return 1
    print(
        f"CI pytest manifest lint ok ({len(entries or [])} entries, "
        f"workflow scanned: {workflow_path.name})."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
