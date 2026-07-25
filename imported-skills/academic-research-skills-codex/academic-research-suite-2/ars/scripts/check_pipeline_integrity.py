#!/usr/bin/env python3
"""Advisory verifier for ARS pipeline phase scope (v3.9.2).

Spec: docs/design/2026-05-18-ars-v3.9.2-phase-boundary-spec.md Phase 4
Issue: #133 (phase scope inflation hot-fix)
Forward note: v3.10 active conductor (#134) replaces this with deterministic
provenance-based verification via task envelope; this v3.9.2 advisory is
heuristic and FP-prone by design.

Usage:
    python scripts/check_pipeline_integrity.py [workdir]
    python scripts/check_pipeline_integrity.py --json [workdir]

Default workdir: current directory.

This script SCANS a working directory for `phaseN_*/` subdirectories (where
N is 1-6 per the ARS pipeline phase convention) and flags advisory signals
that suggest #133-class scope inflation. Output is ADVISORY ONLY — it does
NOT block any workflow. User reviews findings and decides.

Detection rules (v3.9.2 lite):

1. **Phase 5 missing independent reviewer attribution** (HIGH-VALUE structural rule)
   When `phase5_*/` exists but contains no separate files matching the
   independent-reviewer naming convention (devils_advocate / editor_in_chief /
   ethics_review / eic / methodology / domain / perspective / editorial_synthesizer),
   flag INTEGRITY-ADVISORY. This catches the exact #133 reported pattern:
   a single agent producing phase5_*/ output that looks like a review but was
   never actually crosschecked by independent reviewer agents.

   **NORMATIVE FILENAME CONVENTION:** This rule is filename-based regex matching
   over a closed set of agent stem names. For the verifier to recognize a
   reviewer report, the filename MUST contain one of the canonical agent stems:
   - `devils_advocate` (or `devil-s_advocate` / `devils-advocate`)
   - `editor_in_chief` or `eic`
   - `ethics_review` (the full stem; bare `ethics` does NOT match)
   - `methodology_review` / `domain_review` / `perspective_review`
   - `editorial_synth` (matches editorial_synthesizer family)

   Orchestrator runs that emit terse filenames like `round1_ethics.md` (without
   `_review` suffix) WILL produce a false-positive STRUCTURAL finding here.
   Resolution options: (a) rename file to match convention, or (b) ignore the
   advisory finding (verifier exits 0; advisory does not block). The verifier
   trades filename-convention discipline for zero-dependency cross-platform
   simplicity in v3.9.2. v3.10 conductor (#134) replaces filename matching
   with task envelope author provenance.

2. **Multi-phase same-call generation heuristic** (LOWER-VALUE, FP-prone)
   When files in phaseN_*/ and phase{N+1}_*/ share creation timestamps within
   a configurable window (default 5 minutes), flag as POSSIBLE same-call
   inflation. Acknowledged FP risk: legitimate fast orchestrator runs trigger
   this. Use --strict to enable, default OFF.

Exit codes:
    0  No findings, or only --strict findings without --strict flag
    0  Findings produced (advisory output, NOT a hard gate); printed to stdout
    1  Script error (invalid workdir, IO failure)

The verifier intentionally fails open (exit 0) on findings — it is advisory,
not a CI gate. CI should not rely on this for v3.9.2.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable

PHASE_DIR_RE = re.compile(r"^phase([1-6])(?:_.*)?$")

# Phase 5 reviewer file-name heuristics. A phase5_*/ directory should contain
# files whose names match at least one of these per independent crosscheck
# (Devil's Advocate, Editor-in-Chief, Ethics Review). Missing all three →
# advisory flag per #133 root pattern.
PHASE5_REVIEWER_PATTERNS = {
    "devils_advocate": re.compile(r"devils?[_-]?advocate", re.IGNORECASE),
    "editor_in_chief": re.compile(r"(?:editor[_-]?in[_-]?chief|^eic|[_-]eic[_-])", re.IGNORECASE),
    "ethics_review": re.compile(r"ethics?[_-]?review", re.IGNORECASE),
    "methodology_reviewer": re.compile(r"methodology[_-]?review", re.IGNORECASE),
    "domain_reviewer": re.compile(r"domain[_-]?review", re.IGNORECASE),
    "perspective_reviewer": re.compile(r"perspective[_-]?review", re.IGNORECASE),
    "editorial_synthesizer": re.compile(r"editorial[_-]?synth", re.IGNORECASE),
}

# Required minimum reviewer attributions for a valid Phase 5 output per
# academic-pipeline Stage 3 review protocol. At least one from each category
# must appear in phase5_*/ filenames.
PHASE5_REQUIRED_CATEGORIES = [
    ("devil's advocate", ["devils_advocate"]),
    ("editorial/EIC", ["editor_in_chief", "editorial_synthesizer"]),
    ("ethics or panel reviewer", ["ethics_review", "methodology_reviewer", "domain_reviewer", "perspective_reviewer"]),
]

DEFAULT_SAME_CALL_WINDOW_SECONDS = 300  # 5 minutes


@dataclass
class Finding:
    rule: str
    severity: str  # ADVISORY (default), STRUCTURAL (high-value), HEURISTIC (FP-prone)
    phase: int | None
    path: str
    message: str


@dataclass
class Report:
    workdir: str
    phase_dirs: dict[int, list[str]] = field(default_factory=dict)  # phase → list of dir paths
    findings: list[Finding] = field(default_factory=list)


def scan_workdir(workdir: Path) -> Report:
    """Locate all phase{1-6}_*/ subdirectories under workdir."""
    report = Report(workdir=str(workdir))
    if not workdir.is_dir():
        return report

    for entry in workdir.iterdir():
        if not entry.is_dir():
            continue
        match = PHASE_DIR_RE.match(entry.name)
        if not match:
            continue
        phase = int(match.group(1))
        report.phase_dirs.setdefault(phase, []).append(str(entry))
    return report


def check_phase5_attribution(report: Report) -> None:
    """Rule 1 — STRUCTURAL: phase5_*/ must contain independent reviewer files."""
    phase5_dirs = report.phase_dirs.get(5, [])
    if not phase5_dirs:
        return

    for dir_path in phase5_dirs:
        path = Path(dir_path)
        try:
            # Skip hidden files (.DS_Store, Thumbs.db, .gitkeep, etc.) — they're
            # never reviewer reports and would clutter advisory output noise.
            files = [
                p.name for p in path.rglob("*")
                if p.is_file() and not p.name.startswith(".")
            ]
        except OSError as exc:
            report.findings.append(Finding(
                rule="phase5_attribution_io_error",
                severity="ADVISORY",
                phase=5,
                path=dir_path,
                message=f"Could not read phase5 directory: {exc}",
            ))
            continue

        if not files:
            report.findings.append(Finding(
                rule="phase5_empty",
                severity="ADVISORY",
                phase=5,
                path=dir_path,
                message="phase5_*/ directory is empty — Phase 5 should produce review reports",
            ))
            continue

        # Tally which reviewer categories are present
        matched_agents: set[str] = set()
        for fname in files:
            for agent, pattern in PHASE5_REVIEWER_PATTERNS.items():
                if pattern.search(fname):
                    matched_agents.add(agent)

        missing_categories: list[str] = []
        for category_label, agent_list in PHASE5_REQUIRED_CATEGORIES:
            if not any(agent in matched_agents for agent in agent_list):
                missing_categories.append(category_label)

        if missing_categories:
            report.findings.append(Finding(
                rule="phase5_missing_independent_reviewer",
                severity="STRUCTURAL",
                phase=5,
                path=dir_path,
                message=(
                    f"phase5_*/ missing independent reviewer attribution for categories: "
                    f"{', '.join(missing_categories)}. "
                    f"Files found: {files[:5]}{'...' if len(files) > 5 else ''}. "
                    f"#133 pattern: Phase 5 deliverable was likely produced by a single agent "
                    f"that inflated past its scope, skipping mandatory independent crosschecks "
                    f"(DA / EIC / Ethics). Re-run via orchestrator-driven Mode A with "
                    f"`/ars-full` or invoke each reviewer agent separately."
                ),
            ))


def _file_mtime(path: Path) -> float | None:
    try:
        return path.stat().st_mtime
    except OSError:
        return None


def check_same_call_heuristic(report: Report, window_seconds: int) -> None:
    """Rule 2 — HEURISTIC (--strict only): adjacent-phase same-window timestamps."""
    phases_present = sorted(report.phase_dirs.keys())
    if len(phases_present) < 2:
        return

    # Collect (phase, file_path, mtime) tuples
    file_records: dict[int, list[tuple[Path, float]]] = {}
    for phase, dirs in report.phase_dirs.items():
        records: list[tuple[Path, float]] = []
        for dir_path in dirs:
            path = Path(dir_path)
            for file_path in path.rglob("*"):
                if not file_path.is_file():
                    continue
                mtime = _file_mtime(file_path)
                if mtime is None:
                    continue
                records.append((file_path, mtime))
        if records:
            file_records[phase] = records

    # For each adjacent (N, N+1) pair, find files with mtime within window
    for phase in phases_present:
        next_phase = phase + 1
        if next_phase not in file_records:
            continue
        for file_a, mtime_a in file_records.get(phase, []):
            for file_b, mtime_b in file_records[next_phase]:
                delta = abs(mtime_a - mtime_b)
                if delta <= window_seconds:
                    report.findings.append(Finding(
                        rule="adjacent_phase_same_window",
                        severity="HEURISTIC",
                        phase=phase,
                        path=str(file_a),
                        message=(
                            f"phase{phase} file {file_a.name} and phase{next_phase} file "
                            f"{file_b.name} share mtime within {int(delta)}s "
                            f"(window={window_seconds}s). POSSIBLE same-call inflation. "
                            f"Note: legitimate fast orchestrator runs also trigger this "
                            f"heuristic — verify against orchestrator state ledger before "
                            f"treating as #133-class violation."
                        ),
                    ))


def format_text(report: Report) -> str:
    lines = [f"ARS pipeline integrity check (v3.9.2 advisory)"]
    lines.append(f"Workdir: {report.workdir}")
    lines.append(f"Phase dirs found: {dict(sorted(report.phase_dirs.items()))}")
    lines.append("")
    if not report.findings:
        lines.append("No advisory findings.")
        return "\n".join(lines)

    lines.append(f"Findings ({len(report.findings)}):")
    for i, finding in enumerate(report.findings, 1):
        lines.append("")
        lines.append(f"  [{i}] {finding.severity} — {finding.rule}")
        if finding.phase is not None:
            lines.append(f"      Phase: {finding.phase}")
        lines.append(f"      Path:  {finding.path}")
        lines.append(f"      {finding.message}")

    lines.append("")
    lines.append("Reminder: this output is ADVISORY. Findings do NOT block any workflow.")
    lines.append("See docs/design/2026-05-18-ars-v3.9.2-phase-boundary-spec.md for rationale.")
    return "\n".join(lines)


def format_json(report: Report) -> str:
    payload = {
        "workdir": report.workdir,
        "phase_dirs": {str(k): v for k, v in sorted(report.phase_dirs.items())},
        "findings": [
            {
                "rule": f.rule,
                "severity": f.severity,
                "phase": f.phase,
                "path": f.path,
                "message": f.message,
            }
            for f in report.findings
        ],
    }
    return json.dumps(payload, indent=2, ensure_ascii=False)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Advisory check for ARS pipeline phase scope inflation (v3.9.2)"
    )
    parser.add_argument(
        "workdir",
        nargs="?",
        default=".",
        help="Working directory to scan (default: current directory)",
    )
    parser.add_argument(
        "--strict",
        action="store_true",
        help="Enable heuristic same-call timestamp check (FP-prone, default OFF)",
    )
    parser.add_argument(
        "--window-seconds",
        type=int,
        default=DEFAULT_SAME_CALL_WINDOW_SECONDS,
        help=f"Same-call window for --strict heuristic (default: {DEFAULT_SAME_CALL_WINDOW_SECONDS}s)",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Output JSON instead of human-readable text",
    )
    args = parser.parse_args(argv)

    workdir = Path(args.workdir).resolve()
    if not workdir.is_dir():
        print(f"ERROR: workdir not found or not a directory: {workdir}", file=sys.stderr)
        return 1

    report = scan_workdir(workdir)
    check_phase5_attribution(report)
    if args.strict:
        check_same_call_heuristic(report, args.window_seconds)

    if args.json:
        print(format_json(report))
    else:
        print(format_text(report))
    return 0


if __name__ == "__main__":
    sys.exit(main())
