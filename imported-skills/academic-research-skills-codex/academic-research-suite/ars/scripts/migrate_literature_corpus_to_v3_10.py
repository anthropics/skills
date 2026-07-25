#!/usr/bin/env python3
"""#127 v3.10 terminal-policy-layer seed migration tool.

Seeds the passport-level `terminal_policies` block on v3.9.0-onward passports.
This is a PURE LOCAL YAML transform — it needs NO network / API client (unlike
the v3.9.0 migration, which injected OpenAlex / Crossref clients). It only adds
the default-advisory terminal-policy keys where they are absent.

Behavior (spec docs/design/2026-05-31-ars-v3.10-policy-layer-rescope-spec.md
§3 PR-B item 12):

- **Deep-merge, not overwrite (R1 P1):** write each default-advisory key ONLY
  if absent. A passport already carrying a partial `terminal_policies` (e.g. the
  user pre-set `contamination_triangulation: strict`) keeps its existing keys
  untouched; only the missing keys get the advisory default. Re-run is idempotent
  (no key re-written once present).
- **Forbidden:** backfill `venue_type` from the free-form `venue` string
  (fake-precision, R-L3-2-D — adapter-declared only). This tool NEVER touches
  entry-level venue fields.
- **Dry-run mode:** report the seed without writing.
- **Manual-skip scope (R1 P2):** the entry-level manual-skip in the v3.9.0 tool
  applied to lookup / venue backfill. The v3.10 `terminal_policies` seed is
  PASSPORT-LEVEL and global — it does NOT vary by per-entry manual status.
- **Mixed-vintage daisy-chain:** this tool targets v3.9.0-onward passports. A
  pre-v3.9.0 passport (no `contamination_signals` carrying the v3.9.0 lookup
  fields anywhere) is reported as out-of-scope (run the v3.9.0 migration first),
  NOT silently skipped.

Usage:
    python migrate_literature_corpus_to_v3_10.py [--dry-run] [--verbose] PATH
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path
from typing import Any

# Dual-path import (mirrors the v3.9.0 tool): works whether invoked as a module
# (`python -m scripts.migrate...`) or as a script (`python scripts/migrate...`).
try:
    from _passport_yaml import dump_passport, load_passport
except ImportError:
    from scripts._passport_yaml import dump_passport, load_passport


# The default-advisory terminal-policy keys this tool seeds. Mirrors
# terminal_policies.schema.json: each key's absent-default is `advisory`.
DEFAULT_TERMINAL_POLICIES = {
    "contamination_triangulation": "advisory",
    "temporal_integrity": "advisory",
}


class PassportShapeError(ValueError):
    """The passport YAML is structurally unusable (not a mapping, or
    `terminal_policies` is a non-mapping value). Per codex Q3: surface a clear
    error, never silently merge into a malformed block."""


def _entry_has_v3_9_0_signals(entry: Any) -> bool:
    """True iff the entry carries any v3.9.0-era lookup field, marking the
    passport as v3.9.0-onward (in scope). A passport with zero such entries is
    pre-v3.9.0 and out of scope (run the v3.9.0 migration first)."""
    if not isinstance(entry, dict):
        return False
    sig = entry.get("contamination_signals")
    if not isinstance(sig, dict):
        return False
    return any(
        k in sig
        for k in ("semantic_scholar_unmatched", "openalex_unmatched", "crossref_unmatched")
    )


def _passport_in_v3_9_0_scope(doc: Any) -> bool:
    """A passport is v3.9.0-onward when at least one entry carries a v3.9.0
    lookup signal. An empty corpus is treated as in-scope (nothing to gate on;
    the terminal_policies seed is corpus-independent). Pre-v3.9.0 passports
    (a non-empty corpus with no lookup signals anywhere) are out of scope."""
    corpus = doc.get("literature_corpus")
    if not isinstance(corpus, list) or len(corpus) == 0:
        # No corpus / empty corpus → no per-entry vintage evidence; the seed is
        # corpus-independent so we still seed (in scope).
        return True
    return any(_entry_has_v3_9_0_signals(e) for e in corpus)


def migrate_passport(
    path: Path,
    *,
    dry_run: bool,
    verbose: bool = False,
) -> dict[str, Any]:
    """Seed passport-level terminal_policies on a single passport file.

    Returns a report dict. Raises PassportShapeError on a structurally unusable
    passport (codex Q3: clear error, no silent merge)."""
    doc = load_passport(path)

    report: dict[str, Any] = {
        "in_scope": False,
        "seeded_keys": [],
        "preserved_keys": [],
        "out_of_scope": False,
    }

    def _log(msg: str) -> None:
        if verbose:
            print(f"[{path}] {msg}", file=sys.stderr)

    if doc is None or not isinstance(doc, dict):
        raise PassportShapeError(
            f"{path}: passport YAML must be a mapping "
            f"(got {type(doc).__name__}); cannot seed terminal_policies"
        )

    if not _passport_in_v3_9_0_scope(doc):
        report["out_of_scope"] = True
        _log(
            "out of scope (pre-v3.9.0 — run migrate_literature_corpus_to_v3_9_0.py first)"
        )
        return report

    report["in_scope"] = True

    # Distinguish "key absent" from "key present with a null value": an explicit
    # `terminal_policies: null` is a malformed block, NOT an absent one, and must
    # error rather than be silently replaced (codex Q3). `doc.get(...)` cannot
    # tell them apart (both return None), so check membership first.
    if "terminal_policies" not in doc:
        # Whole block absent → seed all default keys.
        new_block = dict(DEFAULT_TERMINAL_POLICIES)
        report["seeded_keys"] = sorted(new_block)
        if not dry_run:
            doc["terminal_policies"] = new_block
        _log(f"seed terminal_policies (whole block absent): {report['seeded_keys']}")
        # seeded_keys is always non-empty here (DEFAULT_TERMINAL_POLICIES has 2
        # keys), so the only condition is dry_run.
        if not dry_run:
            dump_passport(path, doc)
        return report

    existing = doc["terminal_policies"]
    if isinstance(existing, dict):
        # Partial block present → deep-merge: add only absent keys, preserve the rest.
        for key, default_value in DEFAULT_TERMINAL_POLICIES.items():
            if key in existing:
                report["preserved_keys"].append(key)
                _log(f"preserve terminal_policies.{key}={existing[key]!r} (already set)")
            else:
                report["seeded_keys"].append(key)
                if not dry_run:
                    existing[key] = default_value
                _log(f"seed terminal_policies.{key}={default_value!r}")
        report["seeded_keys"].sort()
        report["preserved_keys"].sort()
    else:
        # Non-mapping terminal_policies (null was load-coerced, or a scalar/list)
        # → clear error, never silently overwrite (codex Q3).
        raise PassportShapeError(
            f"{path}: existing 'terminal_policies' must be a mapping "
            f"(got {type(existing).__name__}); refusing to overwrite — "
            f"fix the value by hand"
        )

    if report["seeded_keys"] and not dry_run:
        dump_passport(path, doc)

    return report


def _print_report(path: Path, report: dict[str, Any], dry_run: bool) -> None:
    mode = "(DRY RUN) " if dry_run else ""
    if report["out_of_scope"]:
        print(
            f"v3.10 migration {mode}{path}: OUT OF SCOPE "
            f"(pre-v3.9.0 — run migrate_literature_corpus_to_v3_9_0.py first)"
        )
        return
    verb = "would-seed" if dry_run else "seeded"
    print(
        f"v3.10 migration {mode}{path}: "
        f"{verb}={report['seeded_keys']} "
        f"preserved={report['preserved_keys']} "
        f"dry_run={dry_run}"
    )


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Seed passport-level terminal_policies (default advisory) on "
            "v3.9.0-onward literature_corpus passports. Pure local transform; "
            "deep-merge (only absent keys), idempotent. "
            "See docs/design/2026-05-31-ars-v3.10-policy-layer-rescope-spec.md §3 PR-B item 12"
        )
    )
    parser.add_argument("path", type=Path, help="Passport YAML file")
    parser.add_argument(
        "--dry-run", action="store_true", help="Show proposed seed, write nothing"
    )
    parser.add_argument(
        "--verbose", action="store_true", help="Per-key logging to stderr"
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv or sys.argv[1:])
    try:
        report = migrate_passport(
            args.path, dry_run=args.dry_run, verbose=args.verbose
        )
    except PassportShapeError as e:
        print(f"ERROR: {e}", file=sys.stderr)
        return 2
    _print_report(args.path, report, args.dry_run)
    return 0


if __name__ == "__main__":
    sys.exit(main())
