#!/usr/bin/env python3
"""Strict-monotonic verified_at helper for ARS v3.6.7 Step 6 (spec §5.4).

Every orchestrator-side verdict.verified_at write — Path B8d normal merges,
another_round re-merges, ship_with_known_residue acknowledgement appends —
goes through next_verified_at_ms() so the new value is strictly greater
than every prior persisted entry's verified_at regardless of clock
granularity. This is what makes Path A latest-by-verified_at selection
total-order deterministic at passport scope (§3.7 family D row D3).

Reference pseudocode from spec §5.4:

    def _next_verified_at_ms(passport_audit_artifacts: list) -> str:
        now_ms = utc_now_ms()
        if not passport_audit_artifacts:
            return now_ms
        latest_ms = max(entry["verdict"]["verified_at"] for entry in passport_audit_artifacts)
        return max(now_ms, increment_ms(latest_ms, 1))

`latest_ms` spans ALL prior persisted entries (not filtered by tuple) so
total ordering holds passport-wide.

Run as a CLI:
    python scripts/_next_verified_at_ms.py --passport <path>
        Reads passport YAML/JSON, prints the next verified_at value.

Importable API:
    from scripts._next_verified_at_ms import next_verified_at_ms
    next_verified_at_ms(passport["audit_artifact"])  # -> "2026-...Z"
"""
from __future__ import annotations

import argparse
import json
import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any

try:
    import yaml
except ImportError as e:  # pragma: no cover
    print(f"Missing dependency: {e}. Install with: pip install pyyaml", file=sys.stderr)
    sys.exit(2)


_RFC3339_MS_FORMAT = "%Y-%m-%dT%H:%M:%S.%f"


def utc_now_ms() -> str:
    """Current UTC time as RFC 3339 with millisecond precision (Z suffix)."""
    return rfc3339_ms(datetime.now(timezone.utc))


def parse_rfc3339_ms(s: str) -> datetime:
    """Parse a strict RFC 3339 UTC ms-precision timestamp ('...Z' suffix).

    Raises ValueError if the input does not match the exact shape
    YYYY-MM-DDTHH:MM:SS.mmmZ — accepting other RFC 3339 variants would
    let drift in (the schema's regex pattern enforces ms-precision).
    """
    if not (len(s) == 24 and s.endswith("Z") and s[-5] == "." and s[10] == "T"):
        raise ValueError(f"not RFC 3339 ms UTC ('...Z' with .NNN): {s!r}")
    return datetime.strptime(s[:-1] + "000", _RFC3339_MS_FORMAT).replace(tzinfo=timezone.utc)


def rfc3339_ms(dt: datetime) -> str:
    """Format a UTC datetime as RFC 3339 with millisecond precision."""
    if dt.tzinfo is None:
        dt = dt.replace(tzinfo=timezone.utc)
    else:
        dt = dt.astimezone(timezone.utc)
    return dt.strftime(_RFC3339_MS_FORMAT)[:-3] + "Z"


def bump_ms(dt: datetime, n: int = 1) -> datetime:
    """Advance dt by n milliseconds (carries into seconds / minutes / etc.)."""
    return dt + timedelta(milliseconds=n)


def next_verified_at_ms(passport_audit_artifacts: list[dict[str, Any]] | None) -> str:
    """Return the next verified_at value strictly greater than every prior entry.

    Implements §5.4 pseudocode. None / [] is the empty-ledger base case
    and returns the current UTC clock value.

    Picks `latest` via lexicographic max over the prior verified_at strings.
    For ms-precision RFC 3339 UTC strings (`YYYY-MM-DDTHH:MM:SS.NNNZ`,
    fixed width) lex-max coincides with chronological max — this relies on
    the schema regex (§3.2 audit_artifact_entry verified_at constraint)
    rejecting non-canonical shapes upstream so no malformed entry can
    sneak in and reorder the comparison.
    """
    now = parse_rfc3339_ms(utc_now_ms())
    if not passport_audit_artifacts:
        return rfc3339_ms(now)

    latest_str = max(
        entry["verdict"]["verified_at"] for entry in passport_audit_artifacts
    )
    latest = parse_rfc3339_ms(latest_str)
    bumped = bump_ms(latest, 1)
    return rfc3339_ms(max(now, bumped))


def _load_passport_audit_artifacts(path: Path) -> list[dict[str, Any]]:
    """Read passport YAML or JSON, return audit_artifact[] (or [] if absent).

    Raises ValueError if the file cannot be parsed; CLI main() catches and
    exits 2. The three "absent" cases (top-level not a dict, key missing,
    value not a list) all coerce to [] for v3.6.7 — the helper is a
    monotonic-bump primitive, not a passport validator.

    TODO(Phase 6.3): scripts/check_audit_artifact_consistency.py should
    treat `audit_artifact` present-but-not-a-list as malformed and reject,
    not coerce silently. Lifecycle ownership rule §3.7 E2.
    """
    try:
        text = path.read_text(encoding="utf-8")
    except OSError as e:
        raise ValueError(f"failed to read {path}: {e}") from e

    suffix = path.suffix.lower()
    try:
        if suffix == ".json":
            data = json.loads(text)
        else:
            # Use BaseLoader so PyYAML returns every scalar as str — without
            # this, unquoted RFC 3339 timestamps in spec-example passports
            # (e.g. `verified_at: 2026-04-30T15:23:11.847Z`) get auto-cast
            # to datetime objects, which would break parse_rfc3339_ms()
            # downstream. The schema constrains verified_at to a string;
            # strict string load matches that contract.
            data = yaml.load(text, Loader=yaml.BaseLoader)  # noqa: S506 - intentional, str-only
    except (yaml.YAMLError, json.JSONDecodeError) as e:
        raise ValueError(f"failed to parse {path}: {e}") from e

    if not isinstance(data, dict):
        return []
    artifacts = data.get("audit_artifact") or []
    if not isinstance(artifacts, list):
        return []
    return artifacts


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Print the next verified_at value (RFC 3339 UTC ms) strictly "
            "greater than every prior audit_artifact[] entry's verified_at "
            "in the given Material Passport (§5.4)."
        ),
    )
    parser.add_argument(
        "--passport",
        required=True,
        type=Path,
        help="Path to passport YAML or JSON containing audit_artifact[].",
    )
    args = parser.parse_args(argv)

    if not args.passport.exists():
        print(f"ERROR: passport not found: {args.passport}", file=sys.stderr)
        return 2

    try:
        artifacts = _load_passport_audit_artifacts(args.passport)
    except ValueError as e:
        print(f"ERROR: {e}", file=sys.stderr)
        return 2
    print(next_verified_at_ms(artifacts))
    return 0


if __name__ == "__main__":
    sys.exit(main())
