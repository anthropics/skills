#!/usr/bin/env python3
"""#102 v3.9.0 cross-index triangulation backfill migration tool.

Re-runs the v3.9.0 spec §3.4 + §3.5 OpenAlex + Crossref lookups post-hoc
on v3.7.3 literature_corpus[] entries that have semantic_scholar_unmatched
set but openalex_unmatched / crossref_unmatched absent.

Scope: v3.7.3-onward entries only. Pre-v3.7.3 entries (no
contamination_signals.semantic_scholar_unmatched) require the v3.7.3
migration tool first — see scripts/migrate_literature_corpus_to_v3_7_3.py.
This is daisy-chained migration per spec §3.7.

Usage:
    python migrate_literature_corpus_to_v3_9_0.py [--dry-run] [--verbose] PATH

Concurrency (#138): when both fields are missing for an entry, the OpenAlex and
Crossref lookups run in parallel via a 2-worker thread pool. This requires
`concurrent.futures`. The library-layer sequential-fallback contract ("run
sequentially if parallelism is not available") documented in
deep-research/agents/bibliography_agent.md is a separate concern — this one-shot
tool simply requires threading and does not fall back.

Design: docs/design/2026-05-17-ars-v3.9.0-cross-index-triangulation-measurement-spec.md §3.7
"""
from __future__ import annotations

import argparse
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from typing import Any, Mapping

# Dual-path import: see openalex_client.py comment.
try:
    from _passport_yaml import dump_passport, load_passport
except ImportError:
    from scripts._passport_yaml import dump_passport, load_passport


# Skip-reason keys surface in the migration report.
_SKIP_MANUAL = "skipped_manual"
_SKIP_PRE_V3_7_3 = "skipped_pre_v3_7_3"
_SKIP_COMPLETE = "skipped_complete"


def _entry_in_v3_7_3_scope(entry: Mapping[str, Any]) -> bool:
    """Return True iff the entry has a v3.7.3-era `contamination_signals`
    object (so v3.9.0 migration can act on it). Return False if
    `contamination_signals` is absent entirely, or if it's present without
    `semantic_scholar_unmatched` on a non-manual entry (out of v3.9.0
    scope — needs `migrate_literature_corpus_to_v3_7_3.py` first per spec
    §3.7 daisy-chain contract).

    Manual entries are reported as in-scope when they carry a
    `contamination_signals` object, because they ARE v3.7.3-era (spec §3.2
    manual exemption gives them only `preprint_post_llm_inflection`, not
    `semantic_scholar_unmatched`). The caller (`migrate_passport`) skips
    manual entries separately before invoking the v3.9.0 fill logic; this
    function's manual-branch is therefore a defensive contract — it
    accurately reports v3.7.3 scope membership even when the caller's
    skip order might change later.
    """
    sig = entry.get("contamination_signals")
    if sig is None:
        return False
    if entry.get("obtained_via") == "manual":
        # Manual entries are v3.7.3-era (carry contamination_signals)
        # but the v3.7.3 §3.2 manual exemption means they have only
        # preprint_post_llm_inflection, not semantic_scholar_unmatched.
        # Caller's manual-skip handles the migration filter separately.
        return True
    return "semantic_scholar_unmatched" in sig


def _is_complete(sig: Mapping[str, Any]) -> bool:
    """Entry already has both v3.9.0 fields set — nothing to do."""
    return "openalex_unmatched" in sig and "crossref_unmatched" in sig


def migrate_passport(
    path: Path,
    *,
    oa_client: Any,
    cr_client: Any,
    dry_run: bool,
    verbose: bool = False,
) -> dict[str, int]:
    """Migrate a single passport file. Returns a report dict.

    `oa_client`: OpenAlexClient (or mock) — must expose
        doi_lookup_with_title_check(doi, title) and title_search(title).
    `cr_client`: CrossrefClient (or mock) — same interface.

    Mirrors migrate_literature_corpus_to_v3_7_3.migrate_passport() design:
    accept injected clients for testability (no subprocess, no env-var mock).
    """
    import contamination_signals as cs
    from openalex_client import OpenAlexUnavailable
    from crossref_client import CrossrefUnavailable

    doc = load_passport(path)
    corpus = doc.get("literature_corpus") if doc else None
    report: dict[str, int] = {
        "processed": 0,
        "patched": 0,
        _SKIP_MANUAL: 0,
        _SKIP_PRE_V3_7_3: 0,
        _SKIP_COMPLETE: 0,
        "degraded_openalex": 0,
        "degraded_crossref": 0,
    }
    if not corpus:
        return report

    def _log(msg: str) -> None:
        if verbose:
            print(f"[{path}] {msg}", file=sys.stderr)

    degradation_log: list[str] = []
    mutated = False

    for entry in corpus:
        report["processed"] += 1
        key = entry.get("citation_key", "<no-citation-key>")

        # --- Skip: manual entry (v3.9.0 spec: exempt, never touch) ---
        if entry.get("obtained_via") == "manual":
            report[_SKIP_MANUAL] += 1
            _log(f"{key}: skip (manual entry)")
            continue

        # --- Skip: pre-v3.7.3 (no contamination_signals or no SS field) ---
        if not _entry_in_v3_7_3_scope(entry):
            report[_SKIP_PRE_V3_7_3] += 1
            _log(f"{key}: skip (pre-v3.7.3 — run v3.7.3 migration first)")
            continue

        sig = entry.get("contamination_signals", {})

        # --- Skip: already complete (both fields set) ---
        if _is_complete(sig):
            report[_SKIP_COMPLETE] += 1
            _log(f"{key}: skip (already complete)")
            continue

        # --- Backfill missing fields ---
        entry_changed = False

        # Reconcile one resolver's outcome on the orchestrator thread: get_result
        # either returns the bool/None value or re-raises the resolver's Unavailable
        # exception. All passport mutation, report bookkeeping, and degradation
        # logging stay single-threaded here — the worker only performs the network
        # call. Returns True iff a field was filled.
        def _reconcile(get_result, sig_key, exc_type, label) -> bool:
            try:
                result = get_result()
            except exc_type as e:
                degradation_log.append(
                    f"[CORPUS MIGRATION INCOMPLETE: {label}] {key}: {e}"
                )
                report[f"degraded_{label}"] += 1
                _log(f"{key}: degraded ({label}) — {e}")
                return False
            # result=None means manual (already handled); API-down would have
            # raised exc_type above, so None here just means "nothing to write".
            if result is None:
                return False
            if not dry_run:
                sig[sig_key] = result
                entry["contamination_signals"] = sig
            _log(f"{key}: fill {sig_key}={result}")
            return True

        need_oa = "openalex_unmatched" not in sig
        need_cr = "crossref_unmatched" not in sig
        if not need_oa:
            _log(f"{key}: preserve openalex_unmatched (already set)")
        if not need_cr:
            _log(f"{key}: preserve crossref_unmatched (already set)")

        # #138: the OpenAlex and Crossref lookups for this entry are independent
        # (different hosts, per-instance throttle state, monotonic timing), so when
        # both are missing dispatch the two network calls in parallel. Only missing
        # fields are dispatched, so an already-set field never consults its client
        # (preserves the partial-degradation contract). A single missing field skips
        # the pool and calls directly — no parallelism to gain from one call.
        if need_oa and need_cr:
            with ThreadPoolExecutor(max_workers=2) as pool:
                oa_future = pool.submit(cs.resolve_openalex_unmatched, entry, oa_client)
                cr_future = pool.submit(cs.resolve_crossref_unmatched, entry, cr_client)
            oa_changed = _reconcile(
                oa_future.result, "openalex_unmatched", OpenAlexUnavailable, "openalex"
            )
            cr_changed = _reconcile(
                cr_future.result, "crossref_unmatched", CrossrefUnavailable, "crossref"
            )
            entry_changed = oa_changed or cr_changed
        elif need_oa:
            entry_changed = _reconcile(
                lambda: cs.resolve_openalex_unmatched(entry, oa_client),
                "openalex_unmatched", OpenAlexUnavailable, "openalex",
            )
        elif need_cr:
            entry_changed = _reconcile(
                lambda: cs.resolve_crossref_unmatched(entry, cr_client),
                "crossref_unmatched", CrossrefUnavailable, "crossref",
            )

        if entry_changed:
            report["patched"] += 1
            mutated = True

    if mutated and not dry_run:
        dump_passport(path, doc)

    # Summary to stdout (mirrors v3.7.3 tool print-on-main pattern but
    # here we always emit; caller may also call _print_report() below).
    if degradation_log:
        for line in degradation_log:
            print(line, file=sys.stderr)

    return report


def _print_report(path: Path, report: dict[str, int], dry_run: bool) -> None:
    mode = "(DRY RUN) " if dry_run else ""
    would = "would-add" if dry_run else "patched"
    print(
        f"v3.9.0 migration {mode}{path}: "
        f"processed={report['processed']} "
        f"{would}={report['patched']} "
        f"skipped_manual={report[_SKIP_MANUAL]} "
        f"skipped_pre_v3_7_3={report[_SKIP_PRE_V3_7_3]} "
        f"skipped_complete={report[_SKIP_COMPLETE]} "
        f"degraded_openalex={report['degraded_openalex']} "
        f"degraded_crossref={report['degraded_crossref']} "
        f"dry_run={dry_run}"
    )


def _build_default_oa_client():
    """Production OpenAlex client. Lazy-imported so tests that inject
    mock clients never trigger a network-dependent module load."""
    from openalex_client import OpenAlexClient
    return OpenAlexClient()


def _build_default_cr_client():
    """Production Crossref client. Lazy-imported for the same reason."""
    from crossref_client import CrossrefClient
    return CrossrefClient()


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Backfill v3.9.0 openalex_unmatched + crossref_unmatched on "
            "v3.7.3-onward literature_corpus[] entries. "
            "See docs/design/2026-05-17-ars-v3.9.0-cross-index-triangulation-measurement-spec.md §3.7"
        )
    )
    parser.add_argument("path", type=Path, help="Passport YAML file")
    parser.add_argument(
        "--dry-run", action="store_true", help="Show proposed changes, write nothing"
    )
    parser.add_argument(
        "--verbose", action="store_true", help="Per-entry logging to stderr"
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv or sys.argv[1:])
    oa_client = _build_default_oa_client()
    cr_client = _build_default_cr_client()
    report = migrate_passport(
        args.path,
        oa_client=oa_client,
        cr_client=cr_client,
        dry_run=args.dry_run,
        verbose=args.verbose,
    )
    _print_report(args.path, report, args.dry_run)
    return 0


if __name__ == "__main__":
    sys.exit(main())
