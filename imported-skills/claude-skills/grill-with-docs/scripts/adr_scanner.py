#!/usr/bin/env python3
"""adr_scanner.py — Walk docs/adr/ and validate ADR files against the format.

Stdlib-only. Applies the rules from Matt Pocock's upstream ADR-FORMAT.md
(preserved verbatim in the skill's ADR-FORMAT.md):

  1. Each file matches the `NNNN-slug.md` pattern (4-digit zero-padded number + kebab-case slug)
  2. Numbering is sequential — no gaps, no duplicates
  3. Each ADR has an H1 (the title)
  4. Each ADR has a non-empty body after the H1 (at least the 1-3 sentence context+decision)
  5. Optional status frontmatter, if present, has a valid value
     (proposed | accepted | deprecated | superseded by ADR-NNNN)
  6. Superseded-by references point at an existing ADR number

Output: directory-level summary + per-file findings.

NO LLM CALLS. Pure regex + filesystem walking.

Usage:
    python adr_scanner.py docs/adr/
    python adr_scanner.py docs/adr/ --output json
    python adr_scanner.py --sample          # scan an embedded sample directory layout
"""

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple


ADR_FILENAME_RE = re.compile(r"^(\d{4})-([a-z0-9]+(?:-[a-z0-9]+)*)\.md$")
VALID_STATUSES = {"proposed", "accepted", "deprecated"}
SUPERSEDED_RE = re.compile(r"^superseded\s+by\s+ADR-?(\d{1,4})$", re.IGNORECASE)


SAMPLE_ADRS: Dict[str, str] = {
    "0001-event-sourced-orders.md": (
        "# Event-source the Order write model\n"
        "\n"
        "We need an audit trail of every state change on an Order for compliance + analytics. "
        "We chose event sourcing for the Order write model and a Postgres projection for the read model. "
        "Trade-off accepted: eventual consistency on the read side in exchange for the audit trail and replay.\n"
    ),
    "0002-postgres-for-write-model.md": (
        "---\n"
        "status: accepted\n"
        "---\n"
        "\n"
        "# Postgres for the write-side event store\n"
        "\n"
        "We considered EventStore and Kafka. Postgres won on operational familiarity + transactional guarantees + cost.\n"
    ),
    "0003-rest-over-graphql.md": (
        "---\n"
        "status: accepted\n"
        "---\n"
        "\n"
        "# REST over GraphQL for the public API\n"
        "\n"
        "GraphQL would have given clients more flexibility but added subscription complexity we don't need at our scale.\n"
    ),
}


def parse_frontmatter(text: str) -> Tuple[Dict[str, str], str]:
    """Return (frontmatter_dict, body) for a file that may have YAML-ish frontmatter.

    Only handles simple `key: value` lines (no nested YAML, no lists) — stdlib-only.
    """
    if not text.startswith("---\n"):
        return {}, text
    end_marker = text.find("\n---\n", 4)
    if end_marker == -1:
        return {}, text
    fm_block = text[4:end_marker]
    body = text[end_marker + 5 :]
    fm: Dict[str, str] = {}
    for line in fm_block.splitlines():
        if ":" in line:
            k, v = line.split(":", 1)
            fm[k.strip().lower()] = v.strip()
    return fm, body


def scan_directory(adr_dir: Path) -> Dict[str, Any]:
    findings: List[Dict[str, Any]] = []
    files: List[Tuple[int, str, Path]] = []

    def add(file: str, rule: str, level: str, message: str) -> None:
        findings.append({"file": file, "rule": rule, "level": level, "message": message})

    if not adr_dir.exists():
        add("(root)", "directory", "FAIL", f"Directory does not exist: {adr_dir}")
        return finalize(findings, 0)

    if not adr_dir.is_dir():
        add("(root)", "directory", "FAIL", f"Path is not a directory: {adr_dir}")
        return finalize(findings, 0)

    md_files = sorted(p for p in adr_dir.iterdir() if p.is_file() and p.suffix == ".md")
    if not md_files:
        add("(root)", "directory", "WARN", "Directory is empty — no ADRs scanned. Create lazily when the first ADR is needed.")
        return finalize(findings, 0)

    # Rule 1: filename pattern
    for p in md_files:
        m = ADR_FILENAME_RE.match(p.name)
        if not m:
            add(p.name, "filename-pattern", "FAIL", f"Filename does not match NNNN-slug.md pattern. Expected e.g. 0001-event-sourced-orders.md.")
            continue
        number = int(m.group(1))
        files.append((number, p.name, p))
        add(p.name, "filename-pattern", "PASS", f"Filename matches pattern (number={number:04d}).")

    files.sort(key=lambda t: t[0])

    # Rule 2: numbering sequence (no gaps, no duplicates)
    seen: Dict[int, List[str]] = {}
    for number, name, _ in files:
        seen.setdefault(number, []).append(name)
    for number, names in seen.items():
        if len(names) > 1:
            add(", ".join(names), "numbering-duplicate", "FAIL", f"Duplicate ADR number {number:04d}.")
    if files:
        expected = list(range(1, files[-1][0] + 1))
        actual = sorted(seen.keys())
        gaps = [n for n in expected if n not in actual]
        if gaps:
            add("(root)", "numbering-gap", "WARN", f"Number gap(s) in sequence: {', '.join(f'{g:04d}' for g in gaps)}. Either commit withdrawn ADRs as 'proposed → withdrawn' or renumber.")
        else:
            add("(root)", "numbering-sequence", "PASS", f"Sequential numbering 0001..{files[-1][0]:04d} with no gaps.")

    # Rules 3, 4, 5, 6: per-ADR
    numbers_present = {n for n, _, _ in files}
    for number, name, path in files:
        text = path.read_text(encoding="utf-8") if path.is_file() else SAMPLE_ADRS.get(name, "")
        fm, body = parse_frontmatter(text)

        # Rule 3: H1 present
        h1_match = re.search(r"^#\s+(.+?)\s*$", body, re.MULTILINE)
        if not h1_match:
            add(name, "h1-present", "FAIL", "No H1 (`# Title`) found in body.")
            continue
        else:
            add(name, "h1-present", "PASS", f"H1 found: '{h1_match.group(1).strip()}'.")

        # Rule 4: non-empty body after H1
        after_h1 = body[h1_match.end():].strip()
        if not after_h1:
            add(name, "body-non-empty", "FAIL", "ADR has H1 but no body. The 1-3 sentence context+decision is required.")
        else:
            word_count = len(re.findall(r"\b\w+\b", after_h1))
            if word_count < 10:
                add(name, "body-non-empty", "WARN", f"ADR body is very short ({word_count} words). Confirm context+decision+why are all stated.")
            else:
                add(name, "body-non-empty", "PASS", f"Body present ({word_count} words).")

        # Rule 5: optional status frontmatter sanity
        status = fm.get("status", "").strip().lower() if fm else ""
        if status:
            if status in VALID_STATUSES:
                add(name, "status-frontmatter", "PASS", f"Status '{status}' is valid.")
            elif SUPERSEDED_RE.match(status):
                m = SUPERSEDED_RE.match(status)
                target = int(m.group(1))
                # Rule 6: superseded-by points at existing ADR
                if target in numbers_present:
                    add(name, "status-supersede-target", "PASS", f"Superseded by ADR-{target:04d} which exists.")
                else:
                    add(name, "status-supersede-target", "FAIL", f"Superseded by ADR-{target:04d} but that ADR is not present in this directory.")
            else:
                add(name, "status-frontmatter", "FAIL", f"Status '{status}' is not one of {sorted(VALID_STATUSES)} or 'superseded by ADR-NNNN'.")

    return finalize(findings, len(files))


def finalize(findings: List[Dict[str, Any]], adr_count: int) -> Dict[str, Any]:
    counts = {"PASS": 0, "WARN": 0, "FAIL": 0}
    for f in findings:
        counts[f["level"]] += 1
    if counts["FAIL"] > 0:
        verdict = "FAIL"
    elif counts["WARN"] > 0:
        verdict = "WARN"
    else:
        verdict = "PASS"
    return {"verdict": verdict, "adr_count": adr_count, "counts": counts, "findings": findings}


def render_human(result: Dict[str, Any]) -> str:
    out: List[str] = []
    out.append(f"ADR directory scan verdict: {result['verdict']}")
    out.append(f"  ADRs scanned: {result['adr_count']}")
    counts = result["counts"]
    out.append(f"  PASS: {counts['PASS']}  WARN: {counts['WARN']}  FAIL: {counts['FAIL']}")
    out.append("")
    out.append("Findings:")
    for f in result["findings"]:
        marker = {"PASS": "[ok]", "WARN": "[warn]", "FAIL": "[FAIL]"}[f["level"]]
        out.append(f"  {marker} {f['file']:<40s} {f['rule']}: {f['message']}")
    return "\n".join(out)


def run_sample() -> Dict[str, Any]:
    """Scan the embedded sample by writing it to a tempdir."""
    import tempfile

    with tempfile.TemporaryDirectory() as td:
        d = Path(td) / "adr"
        d.mkdir()
        for name, content in SAMPLE_ADRS.items():
            (d / name).write_text(content, encoding="utf-8")
        return scan_directory(d)


def main(argv: List[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("adr_dir", nargs="?", help="Path to docs/adr/ directory")
    parser.add_argument("--sample", action="store_true", help="Scan the embedded sample ADR layout")
    parser.add_argument("--output", choices=["human", "json"], default="human")
    args = parser.parse_args(argv)

    if args.sample:
        result = run_sample()
    elif args.adr_dir:
        result = scan_directory(Path(args.adr_dir))
    else:
        parser.print_help()
        return 0

    if args.output == "json":
        print(json.dumps(result, indent=2))
    else:
        print(render_human(result))
    return 0 if result["verdict"] != "FAIL" else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
