#!/usr/bin/env python3
"""Validate release-doc alignment per a per-repo manifest TOML.

Cross-repo agnostic per INVARIANT 12. See docs/design/2026-05-21-manifest-validator-spec.md
for the full design (in the toolkit repo). Pure stdlib; deterministic; read-only.
"""

from __future__ import annotations

import sys
from pathlib import Path

# Ensure repo root is on sys.path so `scripts.*` is importable when the script
# is invoked directly (e.g. python scripts/check_release_doc_alignment.py).
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import argparse
import json as _json
import re
from typing import Any

from scripts._release_doc_alignment_schema import (
    ManifestError,
    PackageError,
    ResolutionError,
    ScannerError,
    changelog_settings,
    check_release_block_presence,
    check_simple_template,
    extract_package_version,
    load_manifest,
    resolve_authoritative_version,
    scan_changelog_file,
    _DEFAULT_CHANGELOG_PATTERN,
)


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    p = argparse.ArgumentParser(
        prog="check_release_doc_alignment",
        description="Validate release-doc alignment per a per-repo manifest.",
    )
    p.add_argument("--manifest", required=True, type=Path)
    p.add_argument("--expected-version", default=None)
    p.add_argument("--ci", action="store_true",
                   help="Reject [suite] fallback (use in release CI)")
    p.add_argument("--json", action="store_true", dest="json_output")
    p.add_argument("--verbose", action="store_true")
    return p.parse_args(argv)


def _emit_human(report: dict[str, Any], *, verbose: bool) -> None:
    print("release-discipline check")
    print(f"manifest: {report['manifest']}")
    av = report.get("authoritative_version")
    av_src = report.get("authoritative_version_source")
    if av is not None:
        print(f"authoritative_version: {av} (source: {av_src})")
    ad = report.get("authoritative_date")
    if ad is not None:
        print(f"authoritative_date: {ad} (source: {report.get('authoritative_date_source')})")
    print("")
    for check in report["checks"]:
        status = check["status"].upper()
        if status == "PASS" and not verbose:
            continue
        line = f"{status}: {check['kind']}"
        if "file" in check:
            line += f"  ({check['file']})"
        print(line)
        for key in ("version", "expected_needle", "expected", "found", "reason", "message"):
            if key in check:
                print(f"  {key}: {check[key]}")
    s = report["summary"]
    print("")
    print(f"Summary: {s['pass']} pass, {s['fail']} fail, {s['skip']} skip. Exit {s['exit_code']}.")


def _structural_error(kind: str, message: str, manifest_path: Path) -> dict[str, Any]:
    report = {
        "manifest": str(manifest_path),
        "authoritative_version": None,
        "authoritative_version_source": None,
        "authoritative_date": None,
        "authoritative_date_source": None,
        "checks": [{"kind": kind, "status": "fail", "message": message}],
        "summary": {"pass": 0, "fail": 1, "skip": 0, "exit_code": 1},
    }
    return report


def _sort_checks(checks: list[dict[str, Any]]) -> list[dict[str, Any]]:
    # INVARIANT 18: deterministic order.
    return sorted(checks, key=lambda c: (c.get("file") or "", c["kind"], c.get("version") or ""))


def _run_pipeline(args: argparse.Namespace) -> dict[str, Any]:
    manifest_path: Path = args.manifest

    try:
        data = load_manifest(manifest_path)
    except ManifestError as exc:
        return _structural_error(exc.kind, str(exc), manifest_path)

    cs = changelog_settings(data)
    # Pattern validity + named groups are guaranteed by load_manifest
    # (_check_changelog_pattern); the default pattern is known-good.
    pattern_text = data.get("changelog_entry_pattern") or _DEFAULT_CHANGELOG_PATTERN
    pattern = re.compile(pattern_text, re.MULTILINE)

    manifest_parent = manifest_path.parent
    try:
        entries = scan_changelog_file(
            manifest_parent / data["changelog_path"],
            pattern=pattern,
            fence_marker=cs["fence_marker"],
            comment_open=cs["comment_open"],
            comment_close=cs["comment_close"],
            near_miss_whitelist=cs["near_miss_whitelist"],
        )
    except ScannerError as exc:
        return _structural_error(exc.kind, str(exc), manifest_path)

    # Version resolution
    try:
        resolution = resolve_authoritative_version(
            manifest=data,
            manifest_parent=manifest_parent,
            expected_version=args.expected_version,
            ci=args.ci,
        )
    except (ResolutionError, PackageError) as exc:
        # Both are structural cascades. PackageError is only reachable when
        # --expected-version is absent (the resolver returns early on the CLI
        # flag before reading any package file), so it always means the
        # package authority source died. With --expected-version supplied,
        # package parse failures surface as regular per-package check
        # failures in the loop below instead.
        return _structural_error(exc.kind, str(exc), manifest_path)

    av = resolution.version
    av_src = resolution.source

    # Find authoritative_date by matching CHANGELOG
    av_date = None
    av_date_src = None
    for e in entries:
        if e["version"] == av:
            av_date = e["date"]
            av_date_src = "changelog_match"
            break
    if av_date is None and resolution.source == "suite_fallback":
        av_date = resolution.date
        av_date_src = "suite_fallback"

    checks: list[dict[str, Any]] = []

    # CHANGELOG ↔ authoritative
    if any(e["version"] == av for e in entries):
        checks.append({"kind": "changelog_authoritative_match", "status": "pass"})
    else:
        checks.append({
            "kind": "changelog_authoritative_match",
            "status": "fail",
            "expected": av,
            "message": f"authoritative version {av!r} has no CHANGELOG entry",
        })

    # Package matches
    for entry in data.get("package", []):
        path = entry["path"]
        try:
            v = extract_package_version(
                manifest_parent / path,
                ptype=entry["type"],
                key=entry.get("key"),
                pattern=entry.get("pattern"),
            )
            status = "pass" if v == av else "fail"
            check = {
                "kind": "package_version_match",
                "file": path,
                "expected": av,
                "found": v,
                "status": status,
            }
        except PackageError as exc:
            check = {
                "kind": exc.kind,
                "file": path,
                "status": "fail",
                "message": str(exc),
            }
        checks.append(check)

    # File checks
    for entry in data.get("file", []):
        path = entry["path"]
        try:
            file_text = (manifest_parent / path).read_text(encoding="utf-8")
        except UnicodeDecodeError as exc:
            checks.append({
                "kind": "file_decode_error",
                "file": path,
                "status": "fail",
                "message": f"file is not valid UTF-8: {exc}",
            })
            continue
        if entry.get("release_block_form"):
            for r in check_release_block_presence(
                file_text=file_text,
                entries=entries,
                release_block_form=entry["release_block_form"],
            ):
                r["file"] = path
                checks.append(r)
        for tf, kind in (
            ("badge_template", "badge_match"),
            ("tag_url_template", "tag_url_match"),
            ("last_updated_template", "last_updated_match"),
        ):
            template = entry.get(tf)
            if template is None:
                continue
            r = check_simple_template(
                file_text=file_text,
                template=template,
                authoritative_version=av,
                authoritative_date=av_date,
                kind=kind,
            )
            r["file"] = path
            checks.append(r)

    checks = _sort_checks(checks)
    pass_count = sum(1 for c in checks if c["status"] == "pass")
    fail_count = sum(1 for c in checks if c["status"] == "fail")
    skip_count = sum(1 for c in checks if c["status"] == "skip")
    exit_code = 1 if fail_count > 0 else 0

    return {
        "manifest": str(manifest_path),
        "authoritative_version": av,
        "authoritative_version_source": av_src,
        "authoritative_date": av_date,
        "authoritative_date_source": av_date_src,
        "checks": checks,
        "summary": {"pass": pass_count, "fail": fail_count, "skip": skip_count, "exit_code": exit_code},
    }


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
