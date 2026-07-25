#!/usr/bin/env python3
"""Validate command-list invariants per a per-repo manifest TOML.

A repo that packages a set of commands (one definition file per command,
discovered by glob) often also maintains hand-written files that LIST those
commands — announce scripts, launcher menus, docs. Those lists drift. This
validator discovers the command inventory from the definition files and
asserts every declared listing file is in lockstep: no missing entries, no
stale extras, and (optionally) an accurate stated count. An optional
version-lockstep section asserts a metadata file's version equals the newest
CHANGELOG entry, reusing the release-doc-alignment scanner and extractor.

Cross-repo agnostic per INVARIANT 12. Pure stdlib; deterministic; read-only.
See docs/design/2026-07-03-command-invariants-spec.md (in the toolkit repo).
"""

from __future__ import annotations

import sys
from pathlib import Path

# Ensure repo root is on sys.path so `scripts.*` is importable when the script
# is invoked directly (e.g. python scripts/check_command_invariants.py).
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import argparse
import json as _json
import re
from typing import Any

from scripts._release_doc_alignment_schema import (
    ManifestError,
    PackageError,
    ScannerError,
    _check_path,
    _check_path_shape,
    _check_regex,
    _load_manifest_toml,
    _normalize,
    _require_str,
    _DEFAULT_CHANGELOG,
    _DEFAULT_CHANGELOG_PATTERN,
    extract_package_version,
    scan_changelog_file,
)


# Tokens are matched at a word-ish boundary: start of line or preceded by
# whitespace, then a slash, then the command name. The possessive quantifier
# (*+, Python 3.11+) plus the (?!/) lookahead rejects path-like tokens such as
# absolute paths in prose without backtracking into a shorter false match.
# Names containing dots need an explicit token_pattern; repos whose commands
# share a distinctive prefix should declare a tighter pattern anyway, with
# extra_whitelist for residual cases.
_DEFAULT_TOKEN_PATTERN: str = r"(?:(?<=\s)|^)/(?P<name>[A-Za-z0-9][A-Za-z0-9_-]*+)(?!/)"

_TOP_LEVEL_KEYS: tuple[str, ...] = ("command_glob", "announce", "version_lockstep")
_ANNOUNCE_KEYS: tuple[str, ...] = (
    "path",
    "token_pattern",
    "region_pattern",
    "extra_whitelist",
    "count_pattern",
)
_LOCKSTEP_KEYS: tuple[str, ...] = (
    "changelog_path",
    "package_path",
    "package_key",
    "changelog_entry_pattern",
)


def load_command_manifest(manifest_path: Path) -> dict[str, Any]:
    """Load and validate the command-invariants manifest TOML.

    Raises ManifestError with .kind set per the failure catalog in the spec.
    """
    manifest_path = Path(manifest_path)
    data = _load_manifest_toml(manifest_path)

    # Unknown keys (hard errors, INVARIANT 14) + container shapes.
    for key in data:
        if key not in _TOP_LEVEL_KEYS:
            raise ManifestError(
                kind="unknown_manifest_key",
                message=f"unknown top-level key: {key}",
                field=key,
            )
    announces = data.get("announce", [])
    if not isinstance(announces, list) or any(
        not isinstance(e, dict) for e in announces
    ):
        raise ManifestError(
            kind="manifest_invalid_type",
            message="[[announce]] must be an array of tables",
            field="announce",
        )
    lockstep = data.get("version_lockstep")
    if lockstep is not None and not isinstance(lockstep, dict):
        raise ManifestError(
            kind="manifest_invalid_type",
            message="[version_lockstep] must be a table",
            field="version_lockstep",
        )
    for idx, entry in enumerate(announces):
        for key in entry:
            if key not in _ANNOUNCE_KEYS:
                raise ManifestError(
                    kind="unknown_manifest_key",
                    message=f"unknown key in [[announce]] entry {idx}: {key}",
                    field=f"announce[{idx}].{key}",
                )
    for key in lockstep or {}:
        if key not in _LOCKSTEP_KEYS:
            raise ManifestError(
                kind="unknown_manifest_key",
                message=f"unknown key in [version_lockstep]: {key}",
                field=f"version_lockstep.{key}",
            )

    # Scalar value types.
    _require_str(data.get("command_glob"), field="command_glob")
    for idx, entry in enumerate(announces):
        for key in ("path", "token_pattern", "region_pattern", "count_pattern"):
            _require_str(entry.get(key), field=f"announce[{idx}].{key}")
        whitelist = entry.get("extra_whitelist")
        if whitelist is not None:
            if not isinstance(whitelist, list) or any(
                not isinstance(item, str) for item in whitelist
            ):
                raise ManifestError(
                    kind="manifest_invalid_type",
                    message=f"announce[{idx}].extra_whitelist must be an array of strings",
                    field=f"announce[{idx}].extra_whitelist",
                )
    for key in _LOCKSTEP_KEYS:
        _require_str((lockstep or {}).get(key), field=f"version_lockstep.{key}")

    # Required fields.
    if "command_glob" not in data:
        raise ManifestError(
            kind="manifest_required_field_missing",
            message="manifest missing required field: command_glob",
            field="command_glob",
        )
    if not announces and lockstep is None:
        raise ManifestError(
            kind="empty_manifest",
            message="declare at least one [[announce]] entry or [version_lockstep]",
        )
    for idx, entry in enumerate(announces):
        if entry.get("path") is None:
            raise ManifestError(
                kind="announce_field_missing",
                message=f"[[announce]] entry {idx} missing required field: path",
                field=f"announce[{idx}].path",
            )
    if lockstep is not None:
        for key in ("changelog_path", "package_path", "package_key"):
            if key not in lockstep:
                raise ManifestError(
                    kind="manifest_required_field_missing",
                    message=f"[version_lockstep] missing required field: {key}",
                    field=f"version_lockstep.{key}",
                )

    # Path + glob + pattern safety. Globs get the filesystem-free shape
    # prongs only (a glob is not a single existing file).
    parent = manifest_path.parent
    _check_path_shape(data["command_glob"], field="command_glob")
    seen_paths: set[str] = set()
    for idx, entry in enumerate(announces):
        path = entry["path"]
        if path in seen_paths:
            raise ManifestError(
                kind="duplicate_announce_path",
                message=f"[[announce]] path appears more than once: {path}",
                field=f"announce[{idx}].path",
            )
        seen_paths.add(path)
        _check_path(path, field=f"announce[{idx}].path", manifest_parent=parent)
        if entry.get("token_pattern") is not None:
            _check_regex(
                entry["token_pattern"],
                required_groups=("name",),
                kind_invalid="token_pattern_invalid",
                kind_missing="token_pattern_missing_group",
                field=f"announce[{idx}].token_pattern",
            )
        if entry.get("region_pattern") is not None:
            _check_regex(
                entry["region_pattern"],
                required_groups=("region",),
                kind_invalid="region_pattern_invalid",
                kind_missing="region_pattern_missing_group",
                field=f"announce[{idx}].region_pattern",
            )
        if entry.get("count_pattern") is not None:
            _check_regex(
                entry["count_pattern"],
                required_groups=("count",),
                kind_invalid="count_pattern_invalid",
                kind_missing="count_pattern_missing_group",
                field=f"announce[{idx}].count_pattern",
            )
    if lockstep is not None:
        _check_path(
            lockstep["changelog_path"],
            field="version_lockstep.changelog_path",
            manifest_parent=parent,
        )
        _check_path(
            lockstep["package_path"],
            field="version_lockstep.package_path",
            manifest_parent=parent,
        )
        if lockstep.get("changelog_entry_pattern") is not None:
            _check_regex(
                lockstep["changelog_entry_pattern"],
                required_groups=("version", "date"),
                kind_invalid="changelog_regex_invalid",
                kind_missing="changelog_regex_missing_groups",
                field="version_lockstep.changelog_entry_pattern",
            )

    return data


def discover_commands(manifest_parent: Path, glob_pattern: str) -> list[str]:
    """Return the sorted, deduplicated command names discovered by the glob.

    A command's name is its definition file's stem.
    """
    files = [p for p in manifest_parent.glob(glob_pattern) if p.is_file()]
    return sorted({p.stem for p in files})


def _structural_error(kind: str, message: str, manifest_path: Path) -> dict[str, Any]:
    return {
        "manifest": str(manifest_path),
        "commands": [],
        "checks": [{"kind": kind, "status": "fail", "message": message}],
        "summary": {"pass": 0, "fail": 1, "skip": 0, "exit_code": 1},
    }


def _check_announce(
    entry: dict[str, Any],
    *,
    manifest_parent: Path,
    names: list[str],
) -> list[dict[str, Any]]:
    """All checks for one [[announce]] entry."""
    path = entry["path"]
    try:
        text = _normalize((manifest_parent / path).read_text(encoding="utf-8"))
    except UnicodeDecodeError as exc:
        return [{
            "kind": "announce_decode_error",
            "file": path,
            "status": "fail",
            "message": f"file is not valid UTF-8: {exc}",
        }]

    checks: list[dict[str, Any]] = []
    pattern = re.compile(
        entry.get("token_pattern") or _DEFAULT_TOKEN_PATTERN, re.MULTILINE
    )

    # A region_pattern narrows the scan to each captured region and requires
    # every discovered command in EVERY region: a file with several
    # independently-maintained lists (e.g. a long and a short announce form)
    # then cannot mask drift in one list with a hit in another, and text
    # outside all regions (comments) stops counting as "listed".
    region_pattern = entry.get("region_pattern")
    if region_pattern is not None:
        regions = [
            m.group("region")
            for m in re.compile(region_pattern, re.MULTILINE).finditer(text)
        ]
        if not regions:
            return [{
                "kind": "announce_region_unmatched",
                "file": path,
                "status": "fail",
                "message": "region_pattern matched zero regions",
            }]
    else:
        regions = [text]

    found_per_region = [
        {m.group("name") for m in pattern.finditer(region)} for region in regions
    ]
    found_union = set().union(*found_per_region)

    for name in names:
        missing_from = [
            str(i + 1)
            for i, found in enumerate(found_per_region)
            if name not in found
        ]
        check = {
            "kind": "announce_command_listed",
            "file": path,
            "name": name,
            "status": "pass" if not missing_from else "fail",
        }
        if missing_from:
            if len(regions) == 1:
                check["message"] = f"discovered command {name!r} is not listed"
            else:
                check["message"] = (
                    f"discovered command {name!r} is not listed in "
                    f"region(s) {', '.join(missing_from)} of {len(regions)}"
                )
        checks.append(check)

    whitelist = set(entry.get("extra_whitelist") or [])
    for name in sorted(found_union - set(names) - whitelist):
        checks.append({
            "kind": "announce_extra_command",
            "file": path,
            "name": name,
            "status": "fail",
            "message": (
                f"listed command {name!r} has no definition file "
                f"(stale entry, or add it to extra_whitelist)"
            ),
        })

    count_pattern = entry.get("count_pattern")
    if count_pattern is not None:
        cpat = re.compile(count_pattern, re.MULTILINE)
        raw_counts = [m.group("count") for m in cpat.finditer(text)]
        check = {"kind": "announce_count_match", "file": path, "expected": len(names)}
        if not raw_counts:
            check.update(status="fail", message="count_pattern matched zero times")
        else:
            try:
                counts = [int(c) for c in raw_counts]
            except ValueError:
                check.update(
                    status="fail",
                    message=f"count_pattern group matched non-integer: {raw_counts}",
                )
            else:
                check["found"] = counts
                check["status"] = (
                    "pass" if all(c == len(names) for c in counts) else "fail"
                )
        checks.append(check)

    return checks


def _check_version_lockstep(
    lockstep: dict[str, Any], *, manifest_parent: Path
) -> list[dict[str, Any]]:
    """Newest CHANGELOG entry version must equal the metadata file's version."""
    changelog_path = lockstep["changelog_path"]
    pattern = re.compile(
        lockstep.get("changelog_entry_pattern") or _DEFAULT_CHANGELOG_PATTERN,
        re.MULTILINE,
    )
    try:
        entries = scan_changelog_file(
            manifest_parent / changelog_path,
            pattern=pattern,
            fence_marker=_DEFAULT_CHANGELOG["fence_marker"],
            comment_open=_DEFAULT_CHANGELOG["comment_open"],
            comment_close=_DEFAULT_CHANGELOG["comment_close"],
            near_miss_whitelist=list(_DEFAULT_CHANGELOG["near_miss_whitelist"]),
        )
    except ScannerError as exc:
        return [{
            "kind": exc.kind,
            "file": changelog_path,
            "status": "fail",
            "message": str(exc),
        }]
    newest = entries[0]["version"]

    package_path = lockstep["package_path"]
    try:
        found = extract_package_version(
            manifest_parent / package_path,
            ptype="json",
            key=lockstep["package_key"],
            pattern=None,
        )
    except PackageError as exc:
        return [{
            "kind": exc.kind,
            "file": package_path,
            "status": "fail",
            "message": str(exc),
        }]
    return [{
        "kind": "version_lockstep_match",
        "file": package_path,
        "expected": newest,
        "found": found,
        "status": "pass" if found == newest else "fail",
    }]


def _sort_checks(checks: list[dict[str, Any]]) -> list[dict[str, Any]]:
    # Deterministic order, mirroring the release-doc validator (INVARIANT 18).
    return sorted(
        checks, key=lambda c: (c.get("file") or "", c["kind"], c.get("name") or "")
    )


def _run_pipeline(args: argparse.Namespace) -> dict[str, Any]:
    manifest_path: Path = args.manifest
    try:
        data = load_command_manifest(manifest_path)
    except ManifestError as exc:
        return _structural_error(exc.kind, str(exc), manifest_path)

    parent = manifest_path.parent
    names = discover_commands(parent, data["command_glob"])
    if not names:
        return _structural_error(
            "command_glob_empty",
            f"command_glob matched zero files: {data['command_glob']}",
            manifest_path,
        )

    checks: list[dict[str, Any]] = []
    for entry in data.get("announce", []):
        checks.extend(_check_announce(entry, manifest_parent=parent, names=names))
    lockstep = data.get("version_lockstep")
    if lockstep is not None:
        checks.extend(_check_version_lockstep(lockstep, manifest_parent=parent))

    checks = _sort_checks(checks)
    pass_count = sum(1 for c in checks if c["status"] == "pass")
    fail_count = sum(1 for c in checks if c["status"] == "fail")
    return {
        "manifest": str(manifest_path),
        "commands": names,
        "checks": checks,
        "summary": {
            "pass": pass_count,
            "fail": fail_count,
            "skip": 0,
            "exit_code": 1 if fail_count > 0 else 0,
        },
    }


def _emit_human(report: dict[str, Any], *, verbose: bool) -> None:
    print("command-invariants check")
    print(f"manifest: {report['manifest']}")
    if report["commands"]:
        print(f"commands discovered: {len(report['commands'])}")
    print("")
    for check in report["checks"]:
        status = check["status"].upper()
        if status == "PASS" and not verbose:
            continue
        line = f"{status}: {check['kind']}"
        if "file" in check:
            line += f"  ({check['file']})"
        print(line)
        for key in ("name", "expected", "found", "message"):
            if key in check:
                print(f"  {key}: {check[key]}")
    s = report["summary"]
    print("")
    print(f"Summary: {s['pass']} pass, {s['fail']} fail, {s['skip']} skip. Exit {s['exit_code']}.")


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    p = argparse.ArgumentParser(
        prog="check_command_invariants",
        description="Validate command-list invariants per a per-repo manifest.",
    )
    p.add_argument("--manifest", required=True, type=Path)
    p.add_argument("--json", action="store_true", dest="json_output")
    p.add_argument("--verbose", action="store_true")
    return p.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    report = _run_pipeline(args)
    if args.json_output:
        print(_json.dumps(report, indent=2, sort_keys=False))
    else:
        _emit_human(report, verbose=args.verbose)
    return report["summary"]["exit_code"]


if __name__ == "__main__":
    sys.exit(main())
