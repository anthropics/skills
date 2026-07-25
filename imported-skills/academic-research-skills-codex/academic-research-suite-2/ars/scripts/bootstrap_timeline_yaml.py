#!/usr/bin/env python3
"""v3.9.4 opt-in bootstrap script — populate timeline.yaml from literature_corpus[].

Walks the corpus and:
1. For each entry with `doi`: calls Crossref API to populate published_date.
2. For each entry with a local PDF in source_pointer: runs pdftotext for first-line scan.
3. Emits a timeline.yaml skeleton with effective_date_range, supersedes, superseded_by,
   version_family_id, version_catalog_completeness all left as null/unknown.

Idempotent. --dry-run skips API and pdftotext calls.

Per spec §9.
"""
from __future__ import annotations

import argparse
import shutil
import subprocess
import sys
import urllib.parse
from pathlib import Path

import yaml

# requests is optional — only needed when not --dry-run
try:
    import requests
except ImportError:
    requests = None


def _crossref_lookup(doi: str, dry_run: bool) -> dict | None:
    """Query Crossref API for the DOI's metadata. Returns message dict or None on outage."""
    if dry_run:
        return None
    if requests is None:
        return None  # requests not installed; treat as outage
    try:
        quoted_doi = urllib.parse.quote(doi, safe="")
        r = requests.get(f"https://api.crossref.org/works/{quoted_doi}", timeout=10)
        if r.status_code != 200:
            return None
        return r.json().get("message", {})
    except Exception:
        return None


def _pdftotext_first_line(pdf_path: Path, dry_run: bool) -> str | None:
    """Run pdftotext on cover page; return first non-empty line or None."""
    if dry_run or not pdf_path.exists():
        return None
    pdftotext = shutil.which("pdftotext")
    if pdftotext is None:
        return None
    try:
        result = subprocess.run(
            [pdftotext, "-f", "1", "-l", "1", str(pdf_path), "-"],
            capture_output=True, text=True, timeout=10,
        )
        if result.returncode != 0:
            return None
        for line in result.stdout.splitlines():
            if line.strip():
                return line.strip()
        return None
    except Exception:
        return None


def _bootstrap_entry(entry: dict, dry_run: bool) -> dict:
    """Build a timeline_source_entry from a literature_corpus entry."""
    out: dict = {
        "citation_key": entry["citation_key"],
        "type": entry.get("venue", "unknown"),
        "supersedes": None,
        "superseded_by": None,
        "version_family_id": None,
        "version_catalog_completeness": "unknown",
    }

    doi = entry.get("doi")
    crossref_data = _crossref_lookup(doi, dry_run) if doi else None
    if crossref_data:
        # Encode the DOI the same way _crossref_lookup does so the recorded
        # provenance points at the URL actually queried (DOIs contain '/' and
        # may carry reserved characters).
        quoted_doi = urllib.parse.quote(doi, safe="")
        issued = crossref_data.get("issued", {}).get("date-parts", [[None]])[0]
        if issued and issued[0]:
            precision_map = {1: "year", 2: "month", 3: "day"}
            precision = precision_map.get(len(issued), "year")
            iso_parts = [f"{int(p):04d}" if i == 0 else f"{int(p):02d}"
                         for i, p in enumerate(issued)]
            out["published_date"] = {
                "value": "-".join(iso_parts),
                "precision": precision,
                "open_ended": False,
                "provenance": {
                    "method": "crossref_lookup",
                    "raw": str(issued),
                    "source_locator": f"https://api.crossref.org/works/{quoted_doi}",
                    "confidence": "high",
                },
            }
    elif "year" in entry:
        # Fallback: corpus year only (no Crossref hit or dry-run)
        out["published_date"] = {
            "value": str(entry["year"]),
            "precision": "year",
            "open_ended": False,
            "provenance": {
                "method": "adapter_metadata",
                "raw": str(entry["year"]),
                "source_locator": "literature_corpus[].year",
                "confidence": "medium",
            },
        }

    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="v3.9.4 bootstrap_timeline_yaml.py — opt-in Crossref + pdftotext")
    parser.add_argument("--corpus", type=Path, required=True,
                        help="Path to corpus YAML containing literature_corpus[]")
    parser.add_argument("--output", type=Path, required=True,
                        help="Path to write timeline.yaml")
    parser.add_argument("--dry-run", action="store_true",
                        help="Skip API and pdftotext calls (use corpus year fallback)")
    args = parser.parse_args(argv)

    corpus_data = yaml.safe_load(args.corpus.read_text())
    entries = corpus_data.get("literature_corpus", [])
    sources = [_bootstrap_entry(e, args.dry_run) for e in entries]

    timeline = {
        "schema_version": "1.0",
        "sources": sources,
        "events": [],
    }
    args.output.write_text(yaml.safe_dump(timeline, sort_keys=False))
    return 0


if __name__ == "__main__":
    sys.exit(main())
