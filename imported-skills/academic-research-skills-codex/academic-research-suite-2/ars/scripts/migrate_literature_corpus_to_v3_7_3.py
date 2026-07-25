#!/usr/bin/env python3
"""#105 v3.7.3 contamination_signals backfill migration tool.

Re-runs the v3.7.3 spec §3.2 contamination_signals check post-hoc on
pre-v3.7.3 literature_corpus[] entries. Per spec §3.2 R-L3-2-B:
bibliography_agent computes signals at ingest time; this tool delivers
the deferred batch operation for legacy corpora.

Usage:
    python migrate_literature_corpus_to_v3_7_3.py [--dry-run] [--verbose] PATH

PATH is either a passport YAML file or a directory containing passport
YAML files (directory scan is non-recursive).

Design: docs/design/2026-05-15-issue-105-contamination-signals-backfill-design.md
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path
from typing import Any, Iterable, Mapping

# Dual-path import: see openalex_client.py comment.
try:
    import contamination_signals as cs
    from _passport_yaml import dump_passport, load_passport
    from adapters._common import now_iso
except ImportError:
    from scripts import contamination_signals as cs
    from scripts._passport_yaml import dump_passport, load_passport
    from scripts.adapters._common import now_iso


# Skip-reason categories surface in the migration report so users can
# see what wasn't migrated and why.
_SKIP_ALREADY_MIGRATED = "skipped_already_migrated"
_SKIP_INSUFFICIENT_DATA = "skipped_insufficient_data"
# Counts entries where the manual exemption fired (the entry was still
# patched, but `semantic_scholar_unmatched` was omitted per spec §3.2).
# Distinct from skip categories above — these entries DO get patched.
_MANUAL_UNMATCHED_OMITTED = "manual_unmatched_omitted"


def discover_passports(directory: Path) -> Iterable[Path]:
    """Non-recursive scan for *.yaml files in `directory`."""
    return [p for p in directory.iterdir() if p.is_file() and p.suffix == ".yaml"]


def _is_complete(signals: Mapping[str, Any], entry: Mapping[str, Any]) -> bool:
    """An existing contamination_signals object is "complete" iff every
    field that COULD be computed for this entry is already present.

    `preprint_post_llm_inflection` is always computable when the entry
    has year+venue, so its presence is required.

    `semantic_scholar_unmatched` is required UNLESS the entry is exempt
    (obtained_via='manual', where the field is permanently omitted per
    spec §3.2). For non-manual entries lacking this field, an earlier
    migration must have hit API degradation; re-running fills it in.

    This is the codex R1-3 closure: presence-only idempotency was
    correct for first-time migrations but blocked partial-fill recovery.
    """
    if "preprint_post_llm_inflection" not in signals:
        return False
    if entry.get("obtained_via") == "manual":
        return True
    return "semantic_scholar_unmatched" in signals


def _is_insufficient(entry: Mapping[str, Any]) -> bool:
    """An entry missing `year` cannot have Signal 1 computed at all (year
    is the unconditional gate of the AND; without it, both branches of
    the spec rule are undefined). Schema marks `year` as required so this
    only fires on hand-edited YAML.

    `venue` is INTENTIONALLY not in this check (codex R1-2 closure).
    venue is schema-optional. When absent, `compute_preprint_signal`
    correctly returns False (venue not in PREPRINT_VENUES) — that's a
    defined emission ("computed and the venue isn't a preprint server"),
    not half-truth. Skipping on venue absence would prevent Signal 2 from
    running on schema-valid entries that simply omitted the optional
    field, which is the bug codex R1-2 caught."""
    return not isinstance(entry.get("year"), int)


def migrate_passport(
    path: Path,
    *,
    ss_client: cs.SemanticScholarClient,
    dry_run: bool,
    verbose: bool = False,
) -> dict[str, int]:
    """Migrate a single passport file. Returns a report dict counting
    processed / patched / various skip categories.

    `verbose=True` emits per-entry decision lines to stderr (codex R3-2
    closure). Quiet by default; the CLI's --verbose flag wires this up.
    """
    doc = load_passport(path)
    corpus = doc.get("literature_corpus") if doc else None
    report = {
        "processed": 0,
        "patched": 0,
        _SKIP_ALREADY_MIGRATED: 0,
        _SKIP_INSUFFICIENT_DATA: 0,
        _MANUAL_UNMATCHED_OMITTED: 0,
    }
    if not corpus:
        return report

    def _log(msg: str) -> None:
        if verbose:
            print(f"[{path}] {msg}", file=sys.stderr)

    mutated = False
    for entry in corpus:
        report["processed"] += 1
        key = entry.get("citation_key", "<no-citation-key>")
        existing = entry.get("contamination_signals")
        if existing is not None and _is_complete(existing, entry):
            report[_SKIP_ALREADY_MIGRATED] += 1
            _log(f"{key}: skip (already migrated)")
            continue
        if _is_insufficient(entry):
            report[_SKIP_INSUFFICIENT_DATA] += 1
            _log(f"{key}: skip (insufficient data — missing year)")
            continue
        signals = cs.build_signals_object(entry, ss_client)
        if existing is not None:
            # Partial-fill recovery (codex R1-3 closure): an earlier run
            # that hit API degradation wrote contamination_signals with
            # only `preprint_post_llm_inflection`. Merge any newly-
            # computable fields without overwriting the original
            # backfilled_at timestamp. Codex R2-3 closure: only count
            # this as a patch when a NEW field was actually added —
            # otherwise dry-run misreports + non-dry-run rewrites a
            # byte-identical passport.
            added_any = False
            for sig_key, value in signals.items():
                if sig_key not in existing:
                    existing[sig_key] = value
                    added_any = True
            if not added_any:
                report[_SKIP_ALREADY_MIGRATED] += 1
                _log(f"{key}: skip (partial entry, no new fields computable)")
                continue
            # Codex R5-1 closure: if the partial entry pre-dates the
            # backfilled_at field (e.g., v3.7.3 ingest-time partial that
            # came from a degraded S2 lookup), record provenance now so
            # the post-hoc mutation is distinguishable from ingest-time
            # data. Preserve any existing timestamp — that's the original
            # backfill record per the R1-3 contract.
            if "contamination_signals_backfilled_at" not in entry:
                entry["contamination_signals_backfilled_at"] = now_iso()
            _log(f"{key}: patch (partial-fill recovery, fields added)")
        else:
            entry["contamination_signals"] = signals
            entry["contamination_signals_backfilled_at"] = now_iso()
            _log(f"{key}: patch (signals={dict(signals)})")
        report["patched"] += 1
        if entry.get("obtained_via") == "manual":
            report[_MANUAL_UNMATCHED_OMITTED] += 1
        mutated = True

    if mutated and not dry_run:
        dump_passport(path, doc)
    return report


def migrate_directory(
    directory: Path,
    *,
    ss_client: cs.SemanticScholarClient,
    dry_run: bool,
    verbose: bool = False,
) -> dict[str, int]:
    """Migrate every passport YAML in `directory` (non-recursive).

    Between passports, reset the SS client's outage latch (#115 R5-3) so
    a network blip on one passport doesn't permanently disable lookups
    for the rest of the directory. Within a single passport, the latch
    short-circuits to protect against hammering a dead service.
    """
    agg = {"files_processed": 0, "entries_processed": 0, "entries_patched": 0}
    for path in discover_passports(directory):
        agg["files_processed"] += 1
        r = migrate_passport(
            path, ss_client=ss_client, dry_run=dry_run, verbose=verbose
        )
        agg["entries_processed"] += r["processed"]
        agg["entries_patched"] += r["patched"]
        cs.reset_client_outage_latch(ss_client)
    return agg


def _build_default_ss_client() -> cs.SemanticScholarClient:
    """Production SS client per deep-research/references/semantic_scholar_api_protocol.md
    (DOI-first then title-similarity, 429 → 2s backoff × 3, S2_API_KEY env
    var optional). Lazy-imported so test code (which injects a mock)
    doesn't trigger a network-dependent module load."""
    from semantic_scholar_client import SemanticScholarClient
    return SemanticScholarClient()


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Backfill v3.7.3 contamination_signals on pre-v3.7.3 "
            "literature_corpus[] entries. See "
            "docs/migration/v3.7.3-contamination-signals-backfill.md"
        )
    )
    parser.add_argument("path", type=Path, help="Passport YAML file or directory")
    parser.add_argument(
        "--dry-run", action="store_true", help="Show proposed changes, write nothing"
    )
    parser.add_argument(
        "--verbose", action="store_true", help="Per-entry logging to stderr"
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv or sys.argv[1:])
    try:
        client = _build_default_ss_client()
    except NotImplementedError as e:
        print(f"error: {e}", file=sys.stderr)
        return 2
    if args.path.is_dir():
        agg = migrate_directory(
            args.path,
            ss_client=client,
            dry_run=args.dry_run,
            verbose=args.verbose,
        )
        print(
            f"files_processed={agg['files_processed']} "
            f"entries_processed={agg['entries_processed']} "
            f"entries_patched={agg['entries_patched']} "
            f"dry_run={args.dry_run}"
        )
    else:
        report = migrate_passport(
            args.path,
            ss_client=client,
            dry_run=args.dry_run,
            verbose=args.verbose,
        )
        print(
            f"processed={report['processed']} patched={report['patched']} "
            f"skipped_already_migrated={report[_SKIP_ALREADY_MIGRATED]} "
            f"skipped_insufficient_data={report[_SKIP_INSUFFICIENT_DATA]} "
            f"dry_run={args.dry_run}"
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
