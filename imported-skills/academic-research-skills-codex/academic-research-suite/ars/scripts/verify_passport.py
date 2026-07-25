#!/usr/bin/env python3
"""verify_passport CLI — ad-hoc citation existence verification (Delta 5).

    python -m scripts.verify_passport <passport.yaml>

Loads a Material Passport YAML, runs verification_gate.verify_passport over its
literature_corpus[], and prints the list of per-citation summaries as JSON. A
standalone entry point for ad-hoc verification, separate from the Stage 4->5
audit pipeline.

ref_slug note (#332): both the ref_slug AND the anchor live in writer prose (the
<!--ref:slug--> / <!--anchor:...--> markers), not in literature_corpus. The
summary contract REQUIRES a non-null string ref_slug, so a passport-only CLI
cannot honestly emit a summary — by default it REFUSES (nonzero exit). Pass
`--synthetic-ref-slug citation_key` to synthesize ref_slug from citation_key for
DIAGNOSTIC output (warned on stderr, not a real prose join). The real
{citation_key: ref_slug} + {ref_slug: anchor} joins are wired by the Stage 4->5
pipeline / formatter batch, not by this standalone tool.

Spec: docs/design/2026-05-21-v3.10-182-promote-citation-gate-spec.md §2 Delta 5.
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

import yaml

try:
    from verification_gate import verify_passport
except ImportError:  # pragma: no cover
    from scripts.verification_gate import verify_passport


def _real_clients() -> dict:
    """Construct the four production resolver clients. Imported lazily so the
    CLI module loads without network deps and tests can inject a stub factory.
    Dual-path import: under `python -m scripts.verify_passport` the repo root is
    on sys.path (not scripts/), so the bare imports fall back to scripts.*."""
    try:
        from crossref_client import CrossrefClient
        from openalex_client import OpenAlexClient
        from arxiv_client import ArxivClient
        from semantic_scholar_client import SemanticScholarClient
    except ImportError:  # pragma: no cover - exercised via `python -m`
        from scripts.crossref_client import CrossrefClient
        from scripts.openalex_client import OpenAlexClient
        from scripts.arxiv_client import ArxivClient
        from scripts.semantic_scholar_client import SemanticScholarClient
    return {
        "crossref": CrossrefClient(),
        "openalex": OpenAlexClient(),
        "semantic_scholar": SemanticScholarClient(),
        "arxiv": ArxivClient(),
    }


def run(argv: list[str] | None = None, *, clients_factory=_real_clients) -> int:
    parser = argparse.ArgumentParser(
        prog="verify_passport",
        description="Verify citation existence across a Material Passport.",
    )
    parser.add_argument("passport", help="Path to the passport YAML file.")
    parser.add_argument(
        "--synthetic-ref-slug", choices=["citation_key"], default=None,
        help="Synthesize ref_slug from each entry's citation_key for DIAGNOSTIC "
             "output (the tool refuses by default; this is not a real prose "
             "join, #332).")
    args = parser.parse_args(argv)

    path = Path(args.passport)
    if not path.is_file():
        print(f"[verify_passport ERROR] passport not found: {path}",
              file=sys.stderr)
        return 1
    try:
        passport = yaml.safe_load(path.read_text(encoding="utf-8")) or {}
    except yaml.YAMLError as e:
        print(f"[verify_passport ERROR] could not parse YAML: {e}",
              file=sys.stderr)
        return 1

    # Refuse by default — a passport alone carries no prose <!--ref:slug--> join,
    # so it cannot produce a contract-valid summary (see module docstring, #332).
    corpus = passport.get("literature_corpus") or []
    if args.synthetic_ref_slug is None:
        print(
            "[verify_passport ERROR] cannot emit citation_verification_summary "
            "from a passport alone: ref_slug is a prose-sourced join "
            "(<!--ref:slug--> markers) that a passport does not carry. Run the "
            "Stage 4->5 pipeline (which supplies the prose join), or pass "
            "--synthetic-ref-slug citation_key for diagnostic output.",
            file=sys.stderr)
        return 2

    # synthetic mode: ref_slug := citation_key. Diagnostic only.
    ref_slug_by_key = {
        e.get("citation_key"): e.get("citation_key") for e in corpus
    }
    print(
        "[verify_passport WARNING] --synthetic-ref-slug citation_key: ref_slug "
        "synthesized from citation_key. Output is DIAGNOSTIC, not a real prose "
        "join — do NOT feed it to a consumer that expects prose-joined ref_slugs.",
        file=sys.stderr)

    outcomes = verify_passport(
        passport, clients=clients_factory(), ref_slug_by_key=ref_slug_by_key)
    print(json.dumps(outcomes, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(run())
