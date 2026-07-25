#!/usr/bin/env python3
"""check_audit_artifact_consistency.py — ARS v3.6.7 Step 6 Phase 6.3 lint.

Implements every row of spec §3.7 invariant families A-F (cross-artifact
contract for the audit-artifact lifecycle). Reads a proposal/persisted entry
plus its companion JSONL / sidecar / verdict files (and optionally the
passport for D1/D3/E2/E6 ledger-level checks) and aggregates findings.

CLI modes:
  --mode proposal             — proposal-state entry validation (oneOf.proposal)
  --mode persisted            — persisted-state entry validation (oneOf.persisted)
  --mode jsonl-stream         — A7 stream-shape pairing only (orchestrator §5.2 L2-5)
  --example-validation-harness — F4: walk docs/design/*.md, validate spec example
                                 payloads against the audit/* schemas

Exit codes:
  0   no findings
  1   lint findings (printed to stdout, one per line)
  2   internal error (exception, missing file the rule cannot ignore)
  64  EX_USAGE — bad CLI arguments

Lifecycle ownership notes (E8/E9 — discipline rules with no lint surface):
  E8 — proposal entry file is the LAST file the wrapper writes (after JSONL +
       sidecar + verdict are all on disk). This is wrapper-side atomicity
       discipline; orchestrator has no lint signal beyond "proposal entry
       exists" (a partial wrapper write is invisible from the entry alone).
  E9 — wrapper is NOT invoked from an in-LLM Bash tool call from the same
       session producing the deliverable (deployment discipline; spec §4.7).
       A same-session in-LLM call is undetectable from artifact evidence;
       defense lives at deployment-level (CI / SubagentStop / out-of-band
       human terminal).

Reuse:
  - tests/test_helpers.load_json_schema / build_schema_validator (FORMAT_CHECKER)
  - scripts/_next_verified_at_ms.next_verified_at_ms (D3 monotonic helper)
  - audit_snapshot is the Phase 6.1 reference for argparse subcommand pattern.

The spec §3.7 table is the source of truth; this script is the executable
mirror. Each rule function is annotated with its rule id and one-line summary
so reviewers can grep both directions.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Iterable

try:
    import yaml
except ImportError as e:  # pragma: no cover
    print(f"Missing dependency: {e}. Install with: pip install pyyaml", file=sys.stderr)
    sys.exit(2)

# ---------------------------------------------------------------------------
# Constants — mirror the schema regexes so we don't depend on a JSON Schema
# load just to get a pattern. Keep regex pair in sync with shared/contracts/.
# ---------------------------------------------------------------------------

RUN_ID_RE = re.compile(
    r"^[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}-[0-9]{2}-[0-9]{2}Z-[0-9a-f]{4}$"
)
RFC3339_MS_RE = re.compile(
    r"^[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}\.[0-9]{3}Z$"
)
THREAD_UUID_RE = re.compile(
    r"^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$"
)
SHA256_RE = re.compile(r"^[a-f0-9]{64}$")

REPO_ROOT = Path(__file__).resolve().parent.parent
PASSPORT_SCHEMAS = REPO_ROOT / "shared/contracts/passport"
AUDIT_SCHEMAS = REPO_ROOT / "shared/contracts/audit"

ENTRY_SCHEMA_PATH = PASSPORT_SCHEMAS / "audit_artifact_entry.schema.json"
JSONL_SCHEMA_PATH = AUDIT_SCHEMAS / "audit_jsonl.schema.json"
SIDECAR_SCHEMA_PATH = AUDIT_SCHEMAS / "audit_sidecar.schema.json"
VERDICT_SCHEMA_PATH = AUDIT_SCHEMAS / "audit_verdict.schema.json"

# audit template path is a const in the sidecar schema — used by B3 to know
# which file is the "template" role in the bundle manifest computation.
AUDIT_TEMPLATE_PATH = "shared/templates/codex_audit_multifile_template.md"


def _load_parse_audit_verdict():
    """Load parse_audit_verdict module by file path via importlib.

    Codex round 5 P2 closure: a bare `from parse_audit_verdict import …`
    only resolves when scripts/ is on sys.path (typical for the CLI
    invocation `python scripts/check_audit_artifact_consistency.py …`).
    A package-style invocation `python -m
    scripts.check_audit_artifact_consistency` or import-from-package
    usage leaves scripts/ off sys.path, the import fails, and the
    fallback silently disabled the L2-3/L2-4 stream-shape gate. Loading
    by absolute file path via importlib makes the gate work in every
    invocation context. The module is co-located by repo convention; if
    it ever moves, this helper raises rather than degrading the gate.
    """
    import importlib.util as _ilu

    here = Path(__file__).resolve().parent
    target = here / "parse_audit_verdict.py"
    spec = _ilu.spec_from_file_location("parse_audit_verdict", target)
    if spec is None or spec.loader is None:
        raise RuntimeError(
            f"could not load parse_audit_verdict from {target}; "
            "Phase 6.1 dependency missing — Phase 6.3 gate cannot run "
            "without the stream-shape validator"
        )
    module = _ilu.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _load_stream_shape_validator():
    """Backwards-compatible accessor returning (validate_stream_shape, ParseError)."""
    module = _load_parse_audit_verdict()
    return module.validate_stream_shape, module.ParseError


# ---------------------------------------------------------------------------
# Data structures
# ---------------------------------------------------------------------------

@dataclass
class LintError:
    """One finding from a rule check.

    rule_id  — stable handle from spec §3.7 (e.g., "A1", "B7", "F2").
    message  — human-readable finding; should name the offending value.
    location — file path or logical location (e.g., "<entry>", "<jsonl>:row=12").
    severity — "error" (default; counts toward exit code 1) or "info"
               (printed to stderr but does not fail the run; used by the
               F4 harness for `...` placeholder rows that are intentional).
    """

    rule_id: str
    message: str
    location: str = "<unknown>"
    severity: str = "error"

    def render(self) -> str:
        prefix = self.rule_id if self.severity == "error" else f"{self.rule_id} info"
        return f"[{prefix}] {self.location}: {self.message}"


@dataclass
class LintContext:
    """Bundle of artifacts a check might want to read.

    Members are Optional because some modes don't need every artifact (e.g.,
    jsonl-stream mode only sees the JSONL). Each rule guards against the
    missing pieces it needs and skips silently if irrelevant; that lets the
    aggregator run every rule it can without short-circuiting.
    """

    mode: str  # "proposal" | "persisted" | "jsonl-stream" | "harness"
    entry: dict[str, Any] | None = None
    entry_path: Path | None = None
    sidecar: dict[str, Any] | None = None
    sidecar_path: Path | None = None
    verdict: dict[str, Any] | None = None
    verdict_path: Path | None = None
    jsonl_events: list[dict[str, Any]] | None = None
    jsonl_path: Path | None = None
    output_dir: Path | None = None
    passport_audit_artifacts: list[dict[str, Any]] | None = None
    passport_path: Path | None = None
    repo_root: Path = field(default_factory=lambda: REPO_ROOT)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _sha256_file(path: Path) -> str | None:
    """SHA-256 hex of a file (None if unreadable)."""
    try:
        h = hashlib.sha256()
        with path.open("rb") as f:
            for chunk in iter(lambda: f.read(65536), b""):
                h.update(chunk)
        return h.hexdigest()
    except OSError:
        return None


def _safe_get(d: Any, *path: str) -> Any:
    """Dotted-path get on a dict tree; returns None if any segment missing."""
    for key in path:
        if not isinstance(d, dict):
            return None
        d = d.get(key)
        if d is None:
            return None
    return d


def _load_yaml_or_json(path: Path) -> Any:
    """Parse YAML/JSON keeping RFC 3339 timestamps as strings.

    PyYAML's safe_load auto-casts unquoted ISO-8601 datetimes to datetime
    objects (which fails our string-typed schema). We use a custom loader
    that disables the timestamp constructor so timestamps stay strings,
    while still parsing ints/floats/bools as native types — BaseLoader's
    str-only output broke C1 mirror checks comparing verdict_file (loaded
    as YAML, all-string) against entry (loaded as JSON, typed).
    """
    text = path.read_text(encoding="utf-8")
    if path.suffix.lower() == ".json":
        return json.loads(text)
    return yaml.load(text, Loader=_StrTimestampSafeLoader)


class _StrTimestampSafeLoader(yaml.SafeLoader):
    """SafeLoader variant that keeps timestamps as strings.

    Otherwise PyYAML auto-converts `2026-04-30T15:22:04.123Z` into a
    datetime object, which breaks string-typed schema validation and the
    C1 mirror equality check (entry side reads as str via JSON).
    """


def _yaml_str_timestamp_constructor(loader: yaml.Loader, node: yaml.Node) -> str:
    return loader.construct_scalar(node)


_StrTimestampSafeLoader.add_constructor(
    "tag:yaml.org,2002:timestamp", _yaml_str_timestamp_constructor
)


def _load_jsonl(path: Path) -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []
    with path.open(encoding="utf-8") as fh:
        for lineno, line in enumerate(fh, start=1):
            line = line.strip()
            if not line:
                continue
            try:
                row = json.loads(line)
            except json.JSONDecodeError as e:
                raise ValueError(f"jsonl row {lineno}: {e}") from e
            if not isinstance(row, dict):
                raise ValueError(f"jsonl row {lineno}: not a JSON object")
            out.append(row)
    return out


def _bare_run_id_from_basename(filename: str, ext: str) -> str | None:
    """Strip a known extension and return the bare <run_id>, or None on mismatch.

    We avoid Path.stem / .name parsing tricks to keep the rule legible: a
    sidecar named `2026-04-30T15-22-04Z-d8f3.meta.json` returns
    `2026-04-30T15-22-04Z-d8f3` only when ext='.meta.json'.
    """
    if not filename.endswith(ext):
        return None
    return filename[: -len(ext)]


# ---------------------------------------------------------------------------
# Family A — Per-artifact cross-field rules
# ---------------------------------------------------------------------------


def check_a1(entry: dict[str, Any] | None, verdict: dict[str, Any] | None,
             location: str = "<entry>") -> list[LintError]:
    """A1 — verdict.status agrees with finding_counts and failure_reason.

    Applies to BOTH the entry's verdict block and the verdict file. We
    check whichever is provided. Spec rules:
      PASS:           p1==0 AND p2==0 AND p3==0 AND failure_reason absent
      MINOR:          p1==0 AND p2==0 AND p3<=3 AND failure_reason absent
      MATERIAL:       (p1>0 OR p2>0 OR p3>3) AND failure_reason absent
      AUDIT_FAILED:   p1==0 AND p2==0 AND p3==0 AND failure_reason set non-empty
    """
    findings: list[LintError] = []
    for label, doc in (("entry.verdict", _safe_get(entry, "verdict")), ("verdict_file", verdict)):
        if doc is None:
            continue
        # verdict file uses verdict_status; entry.verdict uses status
        status = doc.get("status") if "status" in doc else doc.get("verdict_status")
        counts = doc.get("finding_counts") or {}
        p1 = counts.get("p1")
        p2 = counts.get("p2")
        p3 = counts.get("p3")
        if status is None or not all(isinstance(x, int) for x in (p1, p2, p3)):
            continue  # schema-level rejection; not A1's surface
        failure_reason = doc.get("failure_reason")
        has_failure = isinstance(failure_reason, str) and len(failure_reason) > 0

        loc = f"{location}:{label}"
        if status == "PASS":
            if not (p1 == 0 and p2 == 0 and p3 == 0):
                findings.append(LintError("A1",
                    f"PASS requires p1==p2==p3==0 (got p1={p1},p2={p2},p3={p3})", loc))
            if has_failure:
                findings.append(LintError("A1",
                    "PASS forbids failure_reason", loc))
        elif status == "MINOR":
            # Codex round 10 P2 closure: spec §3.2 cross-field rule for MINOR
            # is "p1==0 AND p2==0 AND p3<=3" — but PASS already covers
            # p3==0 case, and the wrapper / parse_audit_verdict.py classifies
            # zero findings as PASS not MINOR. A MINOR verdict with
            # p1=p2=p3=0 is malformed (status disagrees with the parser's
            # classification) and would let an inconsistent verdict file
            # send the orchestrator down the MINOR escalation path with
            # no findings to show. Require p3>=1 for MINOR — the lower
            # bound that distinguishes MINOR from PASS.
            if not (p1 == 0 and p2 == 0 and 1 <= p3 <= 3):
                findings.append(LintError("A1",
                    f"MINOR requires p1==0 AND p2==0 AND 1<=p3<=3 (got p1={p1},p2={p2},p3={p3}); "
                    f"zero-count MINOR is malformed — wrapper classifies zero findings as PASS",
                    loc))
            if has_failure:
                findings.append(LintError("A1",
                    "MINOR forbids failure_reason", loc))
        elif status == "MATERIAL":
            if not (p1 > 0 or p2 > 0 or p3 > 3):
                findings.append(LintError("A1",
                    f"MATERIAL requires p1>0 OR p2>0 OR p3>3 (got p1={p1},p2={p2},p3={p3})", loc))
            if has_failure:
                findings.append(LintError("A1",
                    "MATERIAL forbids failure_reason", loc))
        elif status == "AUDIT_FAILED":
            if not (p1 == 0 and p2 == 0 and p3 == 0):
                findings.append(LintError("A1",
                    f"AUDIT_FAILED requires p1==p2==p3==0 (got p1={p1},p2={p2},p3={p3})", loc))
            if not has_failure:
                findings.append(LintError("A1",
                    "AUDIT_FAILED requires failure_reason (non-empty)", loc))
    return findings


def check_a2(entry: dict[str, Any] | None, verdict: dict[str, Any] | None,
             location: str = "<entry>") -> list[LintError]:
    """A2 — failure_reason required iff status == AUDIT_FAILED.

    Mostly redundant with A1 when both sides provide a status, but A2
    surfaces the rule independently so partial documents still get flagged.
    """
    findings: list[LintError] = []
    for label, doc in (("entry.verdict", _safe_get(entry, "verdict")), ("verdict_file", verdict)):
        if doc is None:
            continue
        status = doc.get("status") if "status" in doc else doc.get("verdict_status")
        if status is None:
            continue
        failure_reason = doc.get("failure_reason")
        has_failure = isinstance(failure_reason, str) and len(failure_reason) > 0
        loc = f"{location}:{label}"
        if status == "AUDIT_FAILED" and not has_failure:
            findings.append(LintError("A2",
                "AUDIT_FAILED requires non-empty failure_reason", loc))
        if status != "AUDIT_FAILED" and has_failure:
            findings.append(LintError("A2",
                f"failure_reason forbidden when status={status!r}", loc))
    return findings


def check_a3(entry: dict[str, Any] | None, verdict: dict[str, Any] | None,
             location: str = "<entry>") -> list[LintError]:
    """A3 — round <= target_rounds (entry-side and verdict-file)."""
    findings: list[LintError] = []
    for label, doc in (("entry.verdict", _safe_get(entry, "verdict")), ("verdict_file", verdict)):
        if doc is None:
            continue
        rnd = doc.get("round")
        target = doc.get("target_rounds")
        if not isinstance(rnd, int) or not isinstance(target, int):
            continue
        if rnd > target:
            findings.append(LintError("A3",
                f"round={rnd} > target_rounds={target}", f"{location}:{label}"))
    return findings


def check_a4(entry: dict[str, Any] | None, mode: str,
             location: str = "<entry>") -> list[LintError]:
    """A4 — acknowledgement allowed only on persisted MATERIAL entries.

    Proposal arm forbids acknowledgement entirely (per JSON Schema sketch).
    Persisted PASS / MINOR with acknowledgement → reject.
    """
    if entry is None:
        return []
    if "acknowledgement" not in entry:
        return []
    findings: list[LintError] = []
    if mode == "proposal":
        findings.append(LintError("A4",
            "proposal arm forbids acknowledgement", location))
        return findings
    if mode != "persisted":
        return []
    status = _safe_get(entry, "verdict", "status")
    if status != "MATERIAL":
        findings.append(LintError("A4",
            f"acknowledgement requires verdict.status==MATERIAL (got {status!r})", location))
    return findings


def check_a5(verdict: dict[str, Any] | None,
             location: str = "<verdict>") -> list[LintError]:
    """A5 — verdict file's finding_counts.pN == count(findings[severity == PN]).

    Verdict-file rule only (entry's verdict block is a counts-only mirror per C1).
    """
    if verdict is None:
        return []
    counts = verdict.get("finding_counts") or {}
    findings_list = verdict.get("findings")
    if not isinstance(findings_list, list):
        return []
    out: list[LintError] = []
    actual = {"P1": 0, "P2": 0, "P3": 0}
    for f in findings_list:
        sev = f.get("severity") if isinstance(f, dict) else None
        if sev in actual:
            actual[sev] += 1
    for n in (1, 2, 3):
        declared = counts.get(f"p{n}")
        seen = actual[f"P{n}"]
        if isinstance(declared, int) and declared != seen:
            out.append(LintError("A5",
                f"finding_counts.p{n}={declared} disagrees with findings[severity==P{n}].count={seen}",
                location))
    return out


def check_a6(verdict: dict[str, Any] | None,
             location: str = "<verdict>") -> list[LintError]:
    """A6 — when verdict_status==AUDIT_FAILED, findings == []."""
    if verdict is None:
        return []
    status = verdict.get("verdict_status")
    findings_list = verdict.get("findings")
    if status == "AUDIT_FAILED" and isinstance(findings_list, list) and len(findings_list) > 0:
        return [LintError("A6",
            f"AUDIT_FAILED requires findings==[] (got {len(findings_list)} entries)",
            location)]
    return []


def check_a7(events: list[dict[str, Any]] | None,
             location: str = "<jsonl>") -> list[LintError]:
    """A7 — JSONL stream tool-event pairing.

    For every NON-agent_message item.started, exactly one matching
    item.completed with same item.id, completed-row > started-row, each id
    at most once on each side. agent_message item.completed events are
    EXEMPT from prior-item.started requirement (they don't have one).
    Orphan completions (non-agent_message item.completed without prior
    item.started) are rejected.
    """
    if events is None:
        return []
    findings: list[LintError] = []
    started: dict[str, int] = {}      # item.id -> row
    started_dups: list[tuple[str, int]] = []
    completed: dict[str, int] = {}    # item.id -> row (non-agent_message only)
    completed_dups: list[tuple[str, int]] = []

    for idx, ev in enumerate(events):
        ev_type = ev.get("type")
        if ev_type == "item.started":
            item = ev.get("item") or {}
            iid = item.get("id")
            itype = item.get("type")
            if not isinstance(iid, str):
                continue
            # agent_message starts shouldn't happen but be conservative
            if itype == "agent_message":
                continue
            if iid in started:
                started_dups.append((iid, idx))
            else:
                started[iid] = idx
        elif ev_type == "item.completed":
            item = ev.get("item") or {}
            iid = item.get("id")
            itype = item.get("type")
            if not isinstance(iid, str):
                continue
            if itype == "agent_message":
                continue  # exempt
            if iid in completed:
                completed_dups.append((iid, idx))
            else:
                completed[iid] = idx

    # Duplicates
    for iid, row in started_dups:
        findings.append(LintError("A7",
            f"duplicate item.started for item.id={iid!r} at row {row}", location))
    for iid, row in completed_dups:
        findings.append(LintError("A7",
            f"duplicate item.completed for item.id={iid!r} at row {row}", location))

    # Orphan completions (no prior started)
    for iid, row in completed.items():
        if iid not in started:
            findings.append(LintError("A7",
                f"orphan item.completed for item.id={iid!r} at row {row} (no prior item.started)",
                location))

    # Unmatched starts (no completion)
    for iid, row in started.items():
        if iid not in completed:
            findings.append(LintError("A7",
                f"unmatched item.started for item.id={iid!r} at row {row} (no item.completed)",
                location))
        else:
            # ordering — completed-row must exceed started-row
            crow = completed[iid]
            srow = started[iid]
            if crow <= srow:
                findings.append(LintError("A7",
                    f"item.completed (row {crow}) precedes or equals item.started (row {srow}) for id={iid!r}",
                    location))
    return findings


# ---------------------------------------------------------------------------
# Family B — Cross-file rules (Layer 3)
# ---------------------------------------------------------------------------


def check_b1(sidecar: dict[str, Any] | None, events: list[dict[str, Any]] | None,
             verdict: dict[str, Any] | None, location: str = "<sidecar/jsonl>") -> list[LintError]:
    """B1 — sidecar.stream.jsonl_thread_id matches JSONL's thread.started.thread_id.

    SUSPENDED when companion verdict.verdict_status == AUDIT_FAILED (per
    §3.4 conditional — empty string permitted there).
    """
    if sidecar is None or events is None:
        return []
    side_tid = _safe_get(sidecar, "stream", "jsonl_thread_id")
    # AUDIT_FAILED suspension
    v_status = (_safe_get(verdict, "verdict_status")
                if verdict is not None else None)
    if v_status == "AUDIT_FAILED":
        # rule suspended; empty string allowed
        return []
    # find first thread.started event
    jsonl_tid = None
    for ev in events:
        if ev.get("type") == "thread.started":
            jsonl_tid = ev.get("thread_id")
            break
    if side_tid is None or jsonl_tid is None:
        return [LintError("B1",
            f"missing thread_id (sidecar={side_tid!r}, jsonl={jsonl_tid!r})",
            location)]
    if side_tid != jsonl_tid:
        return [LintError("B1",
            f"sidecar.stream.jsonl_thread_id={side_tid!r} != JSONL.thread.started.thread_id={jsonl_tid!r}",
            location)]
    return []


def check_b2(entry: dict[str, Any] | None, sidecar: dict[str, Any] | None,
             repo_root: Path, location: str = "<entry/sidecar>") -> list[LintError]:
    """B2 — entry.deliverable_sha == sidecar's matching primary sha
    == current SHA-256 of deliverable file on disk."""
    if entry is None or sidecar is None:
        return []
    findings: list[LintError] = []
    entry_sha = entry.get("deliverable_sha")
    deliv_path = entry.get("deliverable_path")
    primaries = _safe_get(sidecar, "prompt", "bundle", "primary_deliverables") or []
    side_sha = None
    for p in primaries:
        if isinstance(p, dict) and p.get("path") == deliv_path:
            side_sha = p.get("sha")
            break
    if side_sha is None:
        return [LintError("B2",
            f"sidecar.prompt.bundle.primary_deliverables has no entry for {deliv_path!r}",
            location)]
    if entry_sha != side_sha:
        findings.append(LintError("B2",
            f"entry.deliverable_sha={entry_sha!r} != sidecar primary[{deliv_path!r}].sha={side_sha!r}",
            location))
    # Verify against on-disk file
    if isinstance(deliv_path, str):
        disk_path = repo_root / deliv_path
        if disk_path.exists():
            disk_sha = _sha256_file(disk_path)
            if disk_sha is not None and disk_sha != entry_sha:
                findings.append(LintError("B2",
                    f"current_file_SHA256({deliv_path!r})={disk_sha!r} != entry.deliverable_sha={entry_sha!r}",
                    location))
        # Missing file is not a B2 failure if entry/sidecar agree — caller
        # may be running against synthetic fixtures. Spec allows lint to
        # detect mutation; absence of file is a separate concern.
    return findings


def compute_bundle_manifest(primary: list[dict[str, Any]],
                            supporting: list[dict[str, Any]],
                            template_path: str,
                            template_sha: str) -> tuple[str, str]:
    """Compute (manifest_text, manifest_sha) per spec §3.6.

    Manifest format: '<role>:<path>:<sha>' lines, sorted lex by (role, path),
    LF separator, trailing LF, then SHA-256 of UTF-8 bytes.
    """
    lines: list[tuple[str, str, str]] = []
    for p in primary:
        if isinstance(p, dict) and "path" in p and "sha" in p:
            lines.append(("primary", str(p["path"]), str(p["sha"])))
    for p in supporting:
        if isinstance(p, dict) and "path" in p and "sha" in p:
            lines.append(("supporting", str(p["path"]), str(p["sha"])))
    lines.append(("template", template_path, template_sha))
    lines.sort(key=lambda t: (t[0], t[1]))
    text = "".join(f"{role}:{path}:{sha}\n" for role, path, sha in lines)
    sha = hashlib.sha256(text.encode("utf-8")).hexdigest()
    return text, sha


def check_b3(sidecar: dict[str, Any] | None, repo_root: Path,
             location: str = "<sidecar>") -> list[LintError]:
    """B3 — sidecar.prompt.bundle.bundle_manifest_sha == recomputed_sha.

    Recomputes over the CURRENT on-disk SHA-256 of every primary +
    supporting + template file (per §3.6 manifest format).

    NOTE: this rule needs the actual files on disk. When fixtures use fake
    paths, we recompute using the SHAs the sidecar declared (so the rule
    still catches the case where the manifest_sha doesn't agree with the
    declared per-file SHAs even before live-disk verification). When the
    files DO exist on disk, we additionally verify that the live SHAs
    agree, raising the more specific finding if they don't.
    """
    if sidecar is None:
        return []
    bundle = _safe_get(sidecar, "prompt", "bundle")
    if not isinstance(bundle, dict):
        return []
    declared_sha = bundle.get("bundle_manifest_sha")
    primary = bundle.get("primary_deliverables") or []
    supporting = bundle.get("supporting_context") or []
    template_path = _safe_get(sidecar, "prompt", "audit_template_path") or AUDIT_TEMPLATE_PATH
    template_sha = _safe_get(sidecar, "prompt", "audit_template_sha")
    if template_sha is None:
        return [LintError("B3",
            "sidecar.prompt.audit_template_sha missing", location)]

    # Step 1 — recompute against the SHAs the sidecar itself declares.
    _, sha_from_declared = compute_bundle_manifest(primary, supporting, template_path, template_sha)
    findings: list[LintError] = []
    if declared_sha != sha_from_declared:
        findings.append(LintError("B3",
            f"declared bundle_manifest_sha={declared_sha!r} disagrees with manifest of declared file SHAs (computed={sha_from_declared!r})",
            location))

    # Step 2 — verify against live disk SHAs. Codex round 2 P2 closure:
    # a missing bundle file must NOT fall back to the sidecar-declared SHA
    # (that would let a deleted/moved file silently pass B3 because the
    # recomputed manifest would still match). Treat missing as
    # stale/unverifiable: emit B3 finding and skip live-manifest comparison
    # (no live manifest exists when files are gone). When repo_root has no
    # .git/ marker (synthetic fixtures in tmp_path), skip the live check
    # entirely — same convention as B4.
    if not (repo_root / ".git").exists():
        return findings  # Step 1 already ran; Step 2 needs a real repo

    live_primary: list[dict[str, Any]] = []
    live_supporting: list[dict[str, Any]] = []
    missing_bundle_files: list[str] = []
    for role, items, sink in (("primary", primary, live_primary), ("supporting", supporting, live_supporting)):
        for p in items:
            if not isinstance(p, dict):
                continue
            path = p.get("path")
            if not isinstance(path, str):
                continue
            disk_path = repo_root / path
            if disk_path.exists():
                disk_sha = _sha256_file(disk_path)
                sink.append({"path": path, "sha": disk_sha or p.get("sha")})
            else:
                missing_bundle_files.append(f"{role}:{path}")
    template_disk = repo_root / template_path
    if template_disk.exists():
        live_template_sha = _sha256_file(template_disk) or template_sha
    else:
        missing_bundle_files.append(f"template:{template_path}")
        live_template_sha = template_sha

    if missing_bundle_files:
        # File-level mutation evidence (deletion / move) — flag explicitly so
        # the auditor sees which file is gone, not just a manifest SHA mismatch.
        findings.append(LintError("B3",
            f"bundle file(s) missing on disk; cannot verify live manifest: "
            f"{missing_bundle_files} — treat as stale/unverifiable",
            location))
        return findings

    # All files present — recompute live manifest and compare.
    _, sha_live = compute_bundle_manifest(live_primary, live_supporting, template_path, live_template_sha)
    if declared_sha != sha_live:
        findings.append(LintError("B3",
            f"declared bundle_manifest_sha={declared_sha!r} disagrees with live bundle (computed={sha_live!r}) — bundle file changed since audit",
            location))
    return findings


def check_b4(sidecar: dict[str, Any] | None, repo_root: Path,
             location: str = "<sidecar>") -> list[LintError]:
    """B4 — sidecar.runner.git_sha resolves to a real commit."""
    if sidecar is None:
        return []
    git_sha = _safe_get(sidecar, "runner", "git_sha")
    if not isinstance(git_sha, str):
        return []
    if not (
        (repo_root / ".git").exists()
        or (repo_root / "scripts" / "check_audit_artifact_consistency.py").is_file()
    ):
        return []
    # Skip live-git check when not inside a real git worktree (allows
    # synthetic fixtures with valid-looking but fictitious SHAs to pass B4
    # without false positive). Use git itself instead of repo_root/.git so
    # nested vendored roots inside a larger checkout are still checked.
    inside = subprocess.run(
        ["git", "-C", str(repo_root), "rev-parse", "--is-inside-work-tree"],
        capture_output=True, text=True, timeout=10,
    )
    if inside.returncode != 0 or inside.stdout.strip() != "true":
        return []
    try:
        result = subprocess.run(
            ["git", "-C", str(repo_root), "cat-file", "-e", f"{git_sha}^{{commit}}"],
            capture_output=True, text=True, timeout=10,
        )
        if result.returncode != 0:
            return [LintError("B4",
                f"runner.git_sha={git_sha!r} does not resolve to a real commit",
                location)]
    except (subprocess.SubprocessError, OSError) as e:
        # Internal — don't fail the whole lint over a git error
        return [LintError("B4",
            f"git resolve failed for {git_sha!r}: {e}", location)]
    return []


def check_b5(sidecar: dict[str, Any] | None,
             location: str = "<sidecar>") -> list[LintError]:
    """B5 — ended_at - started_at == duration_seconds (±1s)."""
    if sidecar is None:
        return []
    timing = sidecar.get("timing") or {}
    started = timing.get("started_at")
    ended = timing.get("ended_at")
    duration_raw = timing.get("duration_seconds")
    if not (isinstance(started, str) and isinstance(ended, str)):
        return []
    try:
        duration = float(duration_raw)
    except (TypeError, ValueError):
        return [LintError("B5",
            f"duration_seconds not numeric: {duration_raw!r}", location)]
    # Parse RFC3339 ms strings
    if not (RFC3339_MS_RE.match(started) and RFC3339_MS_RE.match(ended)):
        # Schema-level rejection territory; B5 still flags arithmetic mismatch
        # but only if we can parse. Skip non-RFC3339-ms here.
        return []
    from datetime import datetime, timezone
    fmt = "%Y-%m-%dT%H:%M:%S.%fZ"
    try:
        dt_s = datetime.strptime(started, fmt).replace(tzinfo=timezone.utc)
        dt_e = datetime.strptime(ended, fmt).replace(tzinfo=timezone.utc)
    except ValueError:
        return []
    delta = (dt_e - dt_s).total_seconds()
    if abs(delta - duration) > 1.0:
        return [LintError("B5",
            f"timing arithmetic: ended_at - started_at = {delta:.3f}s, duration_seconds = {duration:.3f}s (±1s tolerance exceeded)",
            location)]
    return []


def check_b6(sidecar: dict[str, Any] | None, verdict: dict[str, Any] | None,
             location: str = "<sidecar/verdict>") -> list[LintError]:
    """B6 — sidecar.process.exit_code == 0 for non-AUDIT_FAILED entries.

    Non-zero exit_code allowed only when verdict_status == AUDIT_FAILED.
    """
    if sidecar is None:
        return []
    exit_code = _safe_get(sidecar, "process", "exit_code")
    if not isinstance(exit_code, int):
        return []
    v_status = _safe_get(verdict, "verdict_status") if verdict else None
    if exit_code != 0 and v_status != "AUDIT_FAILED":
        return [LintError("B6",
            f"process.exit_code={exit_code} non-zero with verdict_status={v_status!r} (only AUDIT_FAILED permits non-zero exit)",
            location)]
    if exit_code == 0 and v_status == "AUDIT_FAILED":
        # Spec doesn't strictly forbid; AUDIT_FAILED can come from JSONL parse
        # error even when codex exited 0. Don't flag.
        pass
    return []


def check_b7(entry: dict[str, Any] | None, sidecar: dict[str, Any] | None,
             entry_path: Path | None, sidecar_path: Path | None,
             jsonl_path: Path | None, verdict_path: Path | None,
             mode: str, location: str = "<artifacts>",
             repo_root: Path | None = None,
             verdict: dict[str, Any] | None = None) -> list[LintError]:
    """B7 — entry.run_id == sidecar.run_id == verdict.run_id == bare basename of every co-located file.

    Proposal mode: 4 files (jsonl + meta.json + verdict.yaml + entry.json).
    Persisted mode: 3 files (entry consumed; not file-checked here).

    repo_root enables the round-8 P2 closure: cross-check that entry's
    recorded artifact_paths actually resolve to (and equal) the CLI-loaded
    files. Without this, an entry could record artifact_paths pointing at
    a missing or wrong directory while the CLI loads valid evidence from
    --output-dir; the orchestrator later follows the recorded paths.

    `verdict` enables the round-15 P1 closure: cross-check the verdict
    file's internal `run_id` field against entry+sidecar+basename. C1
    mirrors only the nested verdict block (status/round/counts/...) and
    skips the verdict-file-level run_id; without this check, swapping a
    valid verdict.yaml from a different run into the canonical filename
    slot would pass B7 (basenames match), C1 (counts mirror entry), and
    the rest of the gate as long as PASS/MINOR/MATERIAL counts agree.
    """
    if entry is None or sidecar is None:
        return []
    findings: list[LintError] = []
    entry_run_id = entry.get("run_id")
    side_run_id = sidecar.get("run_id")
    if entry_run_id != side_run_id:
        findings.append(LintError("B7",
            f"entry.run_id={entry_run_id!r} != sidecar.run_id={side_run_id!r}",
            location))
    # Codex round 15 P1 closure: also verify verdict.run_id matches.
    if verdict is not None:
        v_run_id = verdict.get("run_id")
        if v_run_id is not None and v_run_id != side_run_id:
            findings.append(LintError("B7",
                f"verdict.run_id={v_run_id!r} != sidecar.run_id={side_run_id!r} "
                f"(swap-one-verdict-file forgery seam — verdict file was renamed "
                f"into <run_id>.verdict.yaml but internal run_id belongs to a "
                f"different run)",
                location))

    # File basename checks (only when we have actual paths)
    canonical = side_run_id if isinstance(side_run_id, str) else entry_run_id
    if not isinstance(canonical, str):
        return findings

    files_to_check: list[tuple[Path, str, str]] = []
    if sidecar_path is not None:
        files_to_check.append((sidecar_path, ".meta.json", "sidecar"))
    if jsonl_path is not None:
        files_to_check.append((jsonl_path, ".jsonl", "jsonl"))
    if verdict_path is not None:
        files_to_check.append((verdict_path, ".verdict.yaml", "verdict"))
    if mode == "proposal" and entry_path is not None:
        files_to_check.append((entry_path, ".audit_artifact_entry.json", "entry"))

    for path, ext, role in files_to_check:
        bare = _bare_run_id_from_basename(path.name, ext)
        if bare is None:
            findings.append(LintError("B7",
                f"{role} file {path.name!r} does not end with {ext!r}",
                location))
        elif bare != canonical:
            findings.append(LintError("B7",
                f"{role} file basename stem={bare!r} != canonical run_id={canonical!r}",
                location))

    # Codex round 4 P2 closure: entry["artifact_paths"] is the contract the
    # orchestrator follows post-merge. A hand-edited entry that points its
    # artifact_paths at a different run's files (jsonl/sidecar/verdict)
    # would forge the swap-one-artifact-file attack seam (§3.7 B7). The
    # B7 cross-file check above only inspects the paths supplied to the
    # CLI; an explicit basename validation of the recorded artifact_paths
    # closes the gap regardless of how the lint was invoked.
    artifact_paths = entry.get("artifact_paths") if isinstance(entry, dict) else None
    cli_loaded_paths = {
        "jsonl": jsonl_path,
        "sidecar": sidecar_path,
        "verdict": verdict_path,
    }
    if isinstance(artifact_paths, dict):
        for key, ext in (("jsonl", ".jsonl"),
                         ("sidecar", ".meta.json"),
                         ("verdict", ".verdict.yaml")):
            recorded = artifact_paths.get(key)
            if not isinstance(recorded, str) or not recorded:
                continue  # schema validation already covers missing/non-str
            recorded_basename = recorded.rsplit("/", 1)[-1]
            bare = _bare_run_id_from_basename(recorded_basename, ext)
            if bare is None:
                findings.append(LintError("B7",
                    f"entry.artifact_paths.{key}={recorded!r} basename does not end with {ext!r}",
                    location))
                continue
            if bare != canonical:
                findings.append(LintError("B7",
                    f"entry.artifact_paths.{key}={recorded!r} basename stem={bare!r} "
                    f"!= canonical run_id={canonical!r} (artifact-paths forgery seam)",
                    location))
                continue
            # Codex round 8 P2 closure: basename match alone leaves the path
            # forgery seam open — entry can record paths pointing at a
            # missing or wrong directory while CLI loads valid files from
            # elsewhere. Resolve the recorded path against repo_root and
            # confirm (a) the file actually exists at that location, and
            # (b) it matches the CLI-loaded artifact for that role.
            if repo_root is not None:
                resolved = (repo_root / recorded).resolve()
                if not resolved.exists():
                    findings.append(LintError("B7",
                        f"entry.artifact_paths.{key}={recorded!r} resolves to "
                        f"{resolved} which does not exist on disk — recorded "
                        f"path is the contract orchestrator follows post-merge",
                        location))
                    continue
                cli_path = cli_loaded_paths.get(key)
                if cli_path is not None and cli_path.exists():
                    cli_resolved = cli_path.resolve()
                    if resolved != cli_resolved and not resolved.samefile(cli_resolved):
                        findings.append(LintError("B7",
                            f"entry.artifact_paths.{key}={recorded!r} resolves to "
                            f"{resolved} but CLI loaded {cli_resolved} — declared "
                            f"path is the evidence the orchestrator will verify; "
                            f"loading from a different location masks divergence",
                            location))
    return findings


def check_b8(entry: dict[str, Any] | None, mode: str,
             location: str = "<entry>") -> list[LintError]:
    """B8 — persisted ack: verdict.verified_at == acknowledgement.acknowledged_at."""
    if entry is None or mode != "persisted":
        return []
    ack = entry.get("acknowledgement")
    if not isinstance(ack, dict):
        return []
    verified_at = _safe_get(entry, "verdict", "verified_at")
    ack_at = ack.get("acknowledged_at")
    if verified_at != ack_at:
        return [LintError("B8",
            f"verified_at={verified_at!r} != acknowledgement.acknowledged_at={ack_at!r} (must be same instant by D3 construction)",
            location)]
    return []


def check_b9(entry: dict[str, Any] | None, sidecar: dict[str, Any] | None,
             location: str = "<entry/sidecar>") -> list[LintError]:
    """B9 — when entry.bundle_id present, equals sidecar.prompt.bundle.bundle_id."""
    if entry is None or sidecar is None:
        return []
    if "bundle_id" not in entry:
        return []
    entry_bid = entry.get("bundle_id")
    side_bid = _safe_get(sidecar, "prompt", "bundle", "bundle_id")
    if entry_bid != side_bid:
        return [LintError("B9",
            f"entry.bundle_id={entry_bid!r} != sidecar.prompt.bundle.bundle_id={side_bid!r}",
            location)]
    return []


def check_b10(entry: dict[str, Any] | None, verdict: dict[str, Any] | None,
              mode: str, location: str = "<entry/verdict>") -> list[LintError]:
    """B10 — persisted ack acknowledgement.finding_ids: non-empty, all exist
    in verdict.findings[].id, full coverage (set equality)."""
    if entry is None or verdict is None or mode != "persisted":
        return []
    ack = entry.get("acknowledgement")
    if not isinstance(ack, dict):
        return []
    declared = ack.get("finding_ids")
    if not isinstance(declared, list):
        return [LintError("B10",
            f"acknowledgement.finding_ids must be array (got {type(declared).__name__})",
            location)]
    if len(declared) == 0:
        return [LintError("B10",
            "acknowledgement.finding_ids must be non-empty", location)]
    findings_list = verdict.get("findings") or []
    real_ids = {f.get("id") for f in findings_list if isinstance(f, dict)}
    declared_set = set(declared)
    out: list[LintError] = []
    missing_in_real = declared_set - real_ids
    if missing_in_real:
        out.append(LintError("B10",
            f"acknowledgement.finding_ids contains unknown ids {sorted(missing_in_real)} (not in verdict.findings[].id)",
            location))
    missing_in_declared = real_ids - declared_set
    if missing_in_declared:
        out.append(LintError("B10",
            f"acknowledgement.finding_ids missing full coverage: {sorted(missing_in_declared)} not acknowledged",
            location))
    return out


# ---------------------------------------------------------------------------
# Family C — Mirror rules
# ---------------------------------------------------------------------------


def check_c1(entry: dict[str, Any] | None, verdict: dict[str, Any] | None,
             location: str = "<entry/verdict>") -> list[LintError]:
    """C1 — entry.verdict.{status, round, target_rounds, finding_counts, failure_reason}
    mirrors verdict file's matching fields (verdict file wins)."""
    if entry is None or verdict is None:
        return []
    ev = entry.get("verdict") or {}
    findings: list[LintError] = []

    pairs = [
        ("status", "verdict_status"),
        ("round", "round"),
        ("target_rounds", "target_rounds"),
        ("finding_counts", "finding_counts"),
        ("failure_reason", "failure_reason"),
    ]
    for entry_key, vfile_key in pairs:
        ev_val = ev.get(entry_key)
        vf_val = verdict.get(vfile_key)
        # failure_reason is conditional — present-or-absent on each side; we
        # compare presence consistency too.
        if entry_key == "failure_reason":
            if (ev_val is None) != (vf_val is None):
                findings.append(LintError("C1",
                    f"failure_reason presence drift: entry={ev_val!r}, verdict_file={vf_val!r}",
                    location))
            elif ev_val is not None and ev_val != vf_val:
                findings.append(LintError("C1",
                    f"failure_reason drift: entry={ev_val!r}, verdict_file={vf_val!r}",
                    location))
            continue
        if ev_val != vf_val:
            findings.append(LintError("C1",
                f"{entry_key} drift: entry={ev_val!r}, verdict_file={vf_val!r} (verdict file wins)",
                location))
    return findings


def check_c2(entry: dict[str, Any] | None, sidecar: dict[str, Any] | None,
             location: str = "<entry/sidecar>") -> list[LintError]:
    """C2 — entry.bundle_manifest_sha == sidecar.prompt.bundle.bundle_manifest_sha."""
    if entry is None or sidecar is None:
        return []
    e_sha = entry.get("bundle_manifest_sha")
    s_sha = _safe_get(sidecar, "prompt", "bundle", "bundle_manifest_sha")
    if e_sha != s_sha:
        return [LintError("C2",
            f"entry.bundle_manifest_sha={e_sha!r} != sidecar.bundle_manifest_sha={s_sha!r}",
            location)]
    return []


def check_c3(new_entry: dict[str, Any] | None, prior_entry: dict[str, Any] | None,
             location: str = "<entry/prior>") -> list[LintError]:
    """C3 — Acknowledgement append entry copies prior entry's
    (stage, agent, deliverable_path, deliverable_sha, run_id,
     bundle_manifest_sha, artifact_paths) AND inner verdict shape
    (status, round, target_rounds, finding_counts, failure_reason)
    byte-for-byte. verified_at and verified_by are FRESHLY set, NOT copied.
    """
    if new_entry is None or prior_entry is None:
        return []
    findings: list[LintError] = []
    copied_fields = ("stage", "agent", "deliverable_path", "deliverable_sha",
                     "run_id", "bundle_manifest_sha", "artifact_paths")
    for f in copied_fields:
        if new_entry.get(f) != prior_entry.get(f):
            findings.append(LintError("C3",
                f"ack entry must copy {f} byte-for-byte: prior={prior_entry.get(f)!r}, new={new_entry.get(f)!r}",
                location))
    # Inner verdict shape
    new_v = new_entry.get("verdict") or {}
    prior_v = prior_entry.get("verdict") or {}
    inner_fields = ("status", "round", "target_rounds", "finding_counts", "failure_reason")
    for f in inner_fields:
        if new_v.get(f) != prior_v.get(f):
            findings.append(LintError("C3",
                f"ack entry must copy verdict.{f} byte-for-byte: prior={prior_v.get(f)!r}, new={new_v.get(f)!r}",
                location))
    # verified_at must be FRESHLY SET (different from prior).
    if (new_v.get("verified_at") is not None and
        new_v.get("verified_at") == prior_v.get("verified_at")):
        findings.append(LintError("C3",
            f"ack entry verified_at={new_v.get('verified_at')!r} must be freshly set (>= prior + 1ms via D3); equals prior",
            location))
    return findings


def check_c4(entry: dict[str, Any] | None, sidecar: dict[str, Any] | None,
             location: str = "<entry/sidecar>") -> list[LintError]:
    """C4 — entry.deliverable_sha == sidecar primary_deliverables[].sha
    for matching primary deliverable (entry-side half of B2)."""
    # We reuse the same check as B2 minus the disk verification; emit C4 not B2.
    if entry is None or sidecar is None:
        return []
    findings: list[LintError] = []
    entry_sha = entry.get("deliverable_sha")
    deliv_path = entry.get("deliverable_path")
    primaries = _safe_get(sidecar, "prompt", "bundle", "primary_deliverables") or []
    side_sha = None
    for p in primaries:
        if isinstance(p, dict) and p.get("path") == deliv_path:
            side_sha = p.get("sha")
            break
    if side_sha is None:
        findings.append(LintError("C4",
            f"sidecar.prompt.bundle.primary_deliverables has no entry for {deliv_path!r}",
            location))
    elif entry_sha != side_sha:
        findings.append(LintError("C4",
            f"entry.deliverable_sha={entry_sha!r} != sidecar primary[{deliv_path!r}].sha={side_sha!r}",
            location))
    return findings


# ---------------------------------------------------------------------------
# Family D — Ordering rules
# ---------------------------------------------------------------------------


def check_d1(passport_audit_artifacts: list[dict[str, Any]] | None,
             location: str = "<passport>") -> list[LintError]:
    """D1 — Latest persisted entry by max(verdict.verified_at) per (stage, agent,
    deliverable_sha) tuple. Lint flags duplicate verified_at within group as
    ordering ambiguity (D3 should make this impossible).

    We report duplicates; selection logic itself isn't a runtime check.
    """
    if not passport_audit_artifacts:
        return []
    findings: list[LintError] = []
    seen: dict[tuple, list[str]] = {}
    for entry in passport_audit_artifacts:
        if not isinstance(entry, dict):
            continue
        key = (entry.get("stage"), entry.get("agent"),
               entry.get("deliverable_sha"), entry.get("run_id"))
        va = _safe_get(entry, "verdict", "verified_at")
        if va is None:
            continue
        seen.setdefault(key, []).append(va)
    for key, vas in seen.items():
        if len(vas) != len(set(vas)):
            findings.append(LintError("D1",
                f"duplicate verified_at in (stage,agent,sha,run_id)={key}: {vas} — D3 monotonic helper should prevent this",
                location))
    return findings


def check_d2(proposals: list[dict[str, Any]] | None,
             location: str = "<output-dir>") -> list[LintError]:
    """D2 — Path B proposal selection determinism check.

    Lint surface: detect proposals sharing identical sidecar.timing.started_at
    where run_id lex-max would be the only tie-breaker (legitimate but worth
    surfacing as ambiguity warning).
    """
    if not proposals:
        return []
    findings: list[LintError] = []
    by_started: dict[str, list[str]] = {}
    for p in proposals:
        st = _safe_get(p, "sidecar", "timing", "started_at")
        rid = _safe_get(p, "entry", "run_id")
        if not isinstance(st, str) or not isinstance(rid, str):
            continue
        by_started.setdefault(st, []).append(rid)
    for st, rids in by_started.items():
        if len(rids) > 1:
            findings.append(LintError("D2",
                f"proposals share started_at={st!r}: {sorted(rids)} — falling back to run_id lex-max tie-breaker",
                location))
    return findings


def check_d3(passport_audit_artifacts: list[dict[str, Any]] | None,
             location: str = "<passport>") -> list[LintError]:
    """D3 — every persisted verified_at strictly greater than every prior.

    Validates monotonicity over the ledger as ordered. A correctly-running
    orchestrator (using _next_verified_at_ms) emits monotonic verified_at;
    if the ledger is not in append order we instead check lex-max property:
    no entry's verified_at is < a later-indexed entry's verified_at.
    Strictly: each entry's verified_at must be > all earlier entries'.
    """
    if not passport_audit_artifacts:
        return []
    findings: list[LintError] = []
    seen: list[str] = []
    for idx, entry in enumerate(passport_audit_artifacts):
        if not isinstance(entry, dict):
            continue
        va = _safe_get(entry, "verdict", "verified_at")
        if not isinstance(va, str):
            continue
        for prior_idx, prior_va in enumerate(seen):
            if va <= prior_va:
                findings.append(LintError("D3",
                    f"audit_artifact[{idx}].verified_at={va!r} not > audit_artifact[{prior_idx}].verified_at={prior_va!r}",
                    location))
                break
        seen.append(va)
    return findings


def check_d4(persisted_round: int | None, proposal_round: int | None,
             location: str = "<entry>") -> list[LintError]:
    """D4 — higher-round unmerged proposals supersede lower-round persisted entries.

    Lint surface: when an unmerged proposal exists alongside a persisted
    entry for the same (stage, agent, deliverable_sha) tuple AND the
    proposal's round is greater than the persisted round, surface the
    supersession requirement (spec §3.7 family D row D4 + §5.6 A1.5).
    The orchestrator must preempt Path A and run Path B with
    supersession_required=true; persisted-mode lint flagging this lets
    the caller see the supersession before the orchestrator processes
    the artifacts.
    """
    if persisted_round is None or proposal_round is None:
        return []
    if proposal_round > persisted_round:
        return [LintError("D4",
            f"unmerged proposal round={proposal_round} supersedes persisted round={persisted_round} "
            f"— orchestrator must preempt Path A and run Path B with supersession_required=true",
            location)]
    return []


# ---------------------------------------------------------------------------
# Family E — Lifecycle ownership
# ---------------------------------------------------------------------------


def check_e1_e2_e6(passport_audit_artifacts: list[dict[str, Any]] | None,
                   location: str = "<passport>") -> list[LintError]:
    """E1/E2/E6 — post-hoc passport-shape checks.

    Detect non-orchestrator-emitted entries by looking for entries that lack
    the orchestrator-set fields (verified_at / verified_by). Also detect
    AUDIT_FAILED entries in the passport (E5/E2 — never persisted).
    """
    if not passport_audit_artifacts:
        return []
    findings: list[LintError] = []
    for idx, entry in enumerate(passport_audit_artifacts):
        if not isinstance(entry, dict):
            findings.append(LintError("E1/E2/E6",
                f"audit_artifact[{idx}] is not an object (type={type(entry).__name__})",
                location))
            continue
        verdict = entry.get("verdict") or {}
        if "verified_at" not in verdict:
            findings.append(LintError("E1/E2/E6",
                f"audit_artifact[{idx}].verdict missing verified_at — non-orchestrator writer suspected",
                location))
        if "verified_by" not in verdict:
            findings.append(LintError("E1/E2/E6",
                f"audit_artifact[{idx}].verdict missing verified_by — non-orchestrator writer suspected",
                location))
        elif verdict.get("verified_by") != "pipeline_orchestrator_agent":
            findings.append(LintError("E1/E2/E6",
                f"audit_artifact[{idx}].verdict.verified_by={verdict.get('verified_by')!r} not 'pipeline_orchestrator_agent'",
                location))
        # Codex round 3 P2 closure: §3.2 lifecycle-conditional table
        # excludes AUDIT_FAILED from the persisted arm. A hand-edited
        # passport entry with verified_at + verified_by + AUDIT_FAILED
        # status would otherwise pass E1/E2/E6's verified_at + verified_by
        # checks above (E5 lives at schema level for CLI modes via the
        # persisted oneOf arm; passport scan needs the same enforcement
        # because AUDIT_FAILED entries are forbidden in `audit_artifact[]`).
        if verdict.get("status") == "AUDIT_FAILED":
            findings.append(LintError("E5",
                f"audit_artifact[{idx}].verdict.status='AUDIT_FAILED' is forbidden in "
                f"passport audit_artifact[] (§3.2: AUDIT_FAILED is proposal-arm only; "
                f"persisted ledger never carries failed-audit entries)",
                location))
    return findings


def check_e3_e4(entry: dict[str, Any] | None, mode: str,
                location: str = "<entry>") -> list[LintError]:
    """E3/E4 — wrapper-emitted proposals carrying verified_at/verified_by are rejected.

    Defense-in-depth on top of schema oneOf.proposal arm.
    """
    if entry is None or mode != "proposal":
        return []
    findings: list[LintError] = []
    verdict = entry.get("verdict") or {}
    if "verified_at" in verdict:
        findings.append(LintError("E3/E4",
            "proposal entry carries verdict.verified_at (Pattern C3 attack surface)",
            location))
    if "verified_by" in verdict:
        findings.append(LintError("E3/E4",
            "proposal entry carries verdict.verified_by (Pattern C3 attack surface)",
            location))
    return findings


def check_e5(entry: dict[str, Any] | None, mode: str,
             location: str = "<entry>") -> list[LintError]:
    """E5 — --mode persisted rejects AUDIT_FAILED status."""
    if entry is None or mode != "persisted":
        return []
    status = _safe_get(entry, "verdict", "status")
    if status == "AUDIT_FAILED":
        return [LintError("E5",
            "persisted entry MUST NOT carry status=AUDIT_FAILED (proposal-arm only)",
            location)]
    return []


def check_e7(entry: dict[str, Any] | None, location: str = "<entry>") -> list[LintError]:
    """E7 — ack entry's verdict.status remains MATERIAL (not synthetic
    'MATERIAL_ACKNOWLEDGED' or similar)."""
    if entry is None:
        return []
    if "acknowledgement" not in entry:
        return []
    status = _safe_get(entry, "verdict", "status")
    if status != "MATERIAL":
        return [LintError("E7",
            f"ack entry must keep verdict.status='MATERIAL'; got {status!r} (no synthetic MATERIAL_ACKNOWLEDGED)",
            location)]
    return []


# ---------------------------------------------------------------------------
# Family F — Naming conventions
# ---------------------------------------------------------------------------


def check_f1(run_id: Any, location: str = "<entry>") -> list[LintError]:
    """F1 — run_id format <ISO-8601-Z>-<4-hex>."""
    if not isinstance(run_id, str):
        return [LintError("F1",
            f"run_id missing or not string (got {type(run_id).__name__})",
            location)]
    if not RUN_ID_RE.match(run_id):
        return [LintError("F1",
            f"run_id={run_id!r} does not match {RUN_ID_RE.pattern}",
            location)]
    return []


def check_f2(jsonl_path: Path | None, sidecar_path: Path | None,
             verdict_path: Path | None, entry_path: Path | None,
             mode: str, location: str = "<artifacts>") -> list[LintError]:
    """F2 — 4 (proposal) or 3 (persisted) artifact basenames use bare run_id stem with
    extensions .jsonl / .meta.json / .verdict.yaml / .audit_artifact_entry.json.
    No stage/agent/deliverable prefix.
    """
    findings: list[LintError] = []
    expectations: list[tuple[Path | None, str, str]] = [
        (jsonl_path, ".jsonl", "jsonl"),
        (sidecar_path, ".meta.json", "sidecar"),
        (verdict_path, ".verdict.yaml", "verdict"),
    ]
    if mode == "proposal":
        expectations.append((entry_path, ".audit_artifact_entry.json", "entry"))

    for path, ext, role in expectations:
        if path is None:
            continue
        if not path.name.endswith(ext):
            findings.append(LintError("F2",
                f"{role} file {path.name!r} does not end with {ext!r}",
                location))
            continue
        bare = path.name[: -len(ext)]
        if not RUN_ID_RE.match(bare):
            findings.append(LintError("F2",
                f"{role} file basename stem={bare!r} not bare run_id (no stage/agent prefix allowed)",
                location))
    return findings


def check_f3(sidecar: dict[str, Any] | None, sidecar_path: Path | None,
             location: str = "<sidecar>") -> list[LintError]:
    """F3 — sidecar.run_id == file basename (with .meta.json stripped)."""
    if sidecar is None or sidecar_path is None:
        return []
    side_run_id = sidecar.get("run_id")
    bare = _bare_run_id_from_basename(sidecar_path.name, ".meta.json")
    if bare is None:
        return [LintError("F3",
            f"sidecar file {sidecar_path.name!r} does not end with .meta.json",
            location)]
    if side_run_id != bare:
        return [LintError("F3",
            f"sidecar.run_id={side_run_id!r} != file basename stem={bare!r}",
            location)]
    return []


# ---------------------------------------------------------------------------
# Aggregation per mode
# ---------------------------------------------------------------------------


def run_checks(ctx: LintContext) -> list[LintError]:
    """Run every applicable rule for the given mode."""
    findings: list[LintError] = []
    mode = ctx.mode

    if mode == "jsonl-stream":
        findings.extend(check_a7(ctx.jsonl_events, location=str(ctx.jsonl_path or "<jsonl>")))
        return findings

    # Proposal / persisted modes — full sweep
    entry_loc = str(ctx.entry_path or "<entry>")
    verdict_loc = str(ctx.verdict_path or "<verdict>")
    sidecar_loc = str(ctx.sidecar_path or "<sidecar>")

    # Family A
    findings.extend(check_a1(ctx.entry, ctx.verdict, location=entry_loc))
    findings.extend(check_a2(ctx.entry, ctx.verdict, location=entry_loc))
    findings.extend(check_a3(ctx.entry, ctx.verdict, location=entry_loc))
    findings.extend(check_a4(ctx.entry, mode, location=entry_loc))
    findings.extend(check_a5(ctx.verdict, location=verdict_loc))
    findings.extend(check_a6(ctx.verdict, location=verdict_loc))
    if ctx.jsonl_events is not None:
        # Codex round 6 P2 closure: A7 tool-event pairing is suspended for
        # AUDIT_FAILED bundles. A failed audit's stream is legitimately
        # truncated — codex may be killed after an item.started but before
        # the matching item.completed — so unmatched starts are expected
        # evidence, not pairing violations. §3.4 suspends Layer 3 cross-
        # file rules for AUDIT_FAILED; the symmetric Layer 2 suspension
        # for stream-shape (round 3 closure) applies to A7 too.
        v_status_for_a7 = (ctx.verdict or {}).get("verdict_status")
        if v_status_for_a7 != "AUDIT_FAILED":
            findings.extend(check_a7(ctx.jsonl_events, location=str(ctx.jsonl_path or "<jsonl>")))
        # Codex round 3 P1 closure: A7 alone does not reject a JSONL that
        # ends after `thread.started + turn.started` (no item.started, so
        # no pairing violation). Phase 6.1's parse_audit_verdict.validate_
        # stream_shape covers L2-3/L2-4 stream-shape gates: exactly one
        # thread.started, second event is turn.started, exactly one
        # terminal turn.completed strictly after the last agent_message,
        # turn.completed.usage all integers >= 0 with input_tokens > 0,
        # canonical UUID thread_id, no error events. Reuse it here so a
        # truncated stream is rejected before the rest of the gate runs.
        # AUDIT_FAILED bundles legitimately have malformed streams (codex
        # was killed mid-run); §3.4 already suspends Layer 3 cross-file
        # rules for them, and we apply the same suspension here.
        v_status = (ctx.verdict or {}).get("verdict_status")
        if v_status != "AUDIT_FAILED":
            # Codex round 5 P2 closure: load parse_audit_verdict by file path
            # via importlib so the stream-shape gate runs regardless of how
            # this checker is invoked (CLI on sys.path, `python -m
            # scripts.check_audit_artifact_consistency`, or imported as
            # `scripts.check_audit_artifact_consistency` from elsewhere).
            # Silent ImportError degrade was hiding the gate from package
            # callers and letting truncated streams pass.
            module = _load_parse_audit_verdict()
            ParseError = module.ParseError
            try:
                module.validate_stream_shape(ctx.jsonl_events)
            except ParseError as e:
                findings.append(LintError(
                    "L2-3/L2-4",
                    f"jsonl stream-shape rejected: {e} — non-AUDIT_FAILED "
                    f"verdict requires a complete stream (thread.started → "
                    f"turn.started → … → turn.completed with valid usage)",
                    str(ctx.jsonl_path or "<jsonl>"),
                ))
            else:
                # Codex round 8 P1 closure: stream-shape alone validates
                # ordering / usage / canonical UUID but does NOT verify the
                # last agent_message contains a parseable Section 6 verdict.
                # A bundle whose JSONL ends with arbitrary text or no
                # verdict at all could pass stream-shape and exit 0 as long
                # as the separate verdict.yaml mirrored the entry. L2-4 in
                # spec §5.2 is `parse_audit_verdict.py --probe` — extract
                # the last agent_message and parse_section6 on its text.
                # cmd_probe in parse_audit_verdict already chains all three
                # checks; we replicate that chain here without invoking
                # the module's CLI (avoids subprocess overhead in lint
                # path) and capture each layer as its own LintError.
                try:
                    verdict_text = module.extract_verdict_text(ctx.jsonl_events)
                except ParseError as e:
                    findings.append(LintError(
                        "L2-4",
                        f"verdict text extraction failed: {e} — non-AUDIT_FAILED "
                        f"bundle requires a parseable agent_message in the JSONL",
                        str(ctx.jsonl_path or "<jsonl>"),
                    ))
                else:
                    try:
                        # Probe-style: pass current_round=None to accept any
                        # parseable summary; cross-field count validation is
                        # already covered by A5 against the verdict.yaml.
                        module.parse_section6(verdict_text, current_round=None)
                    except ParseError as e:
                        findings.append(LintError(
                            "L2-4",
                            f"verdict text Section 6 parse failed: {e} — "
                            f"agent_message did not contain a parseable "
                            f"audit-template Section 6 verdict block",
                            str(ctx.jsonl_path or "<jsonl>"),
                        ))

    # Codex round 9 P2 closure: §3.4 + §5.6 Path B5 + §3.7 family B note say
    # "Layer 3 verification is suspended for AUDIT_FAILED" — the orchestrator
    # short-circuits to BLOCK with failure_reason without running L3-2..L3-8
    # gates. A failed audit caused by bundle mutation legitimately has a
    # different live deliverable SHA from the recorded audit-time SHA;
    # treating that as a B2/B3 violation would reject the failure-signaling
    # artifact instead of letting the orchestrator surface failure_reason.
    # Same suspension extends to B4 git_sha, B5 timing arithmetic, B7
    # cross-file basename / path resolution: all are Layer 3 cross-file
    # verification rules that don't apply when the audit boundary itself
    # failed. B6 is suspended internally by its own AUDIT_FAILED branch
    # (spec §3.4 rule 6 + F-027); B1 has its own conditional handling.
    is_audit_failed = (ctx.verdict or {}).get("verdict_status") == "AUDIT_FAILED"

    # Family B
    findings.extend(check_b1(ctx.sidecar, ctx.jsonl_events, ctx.verdict, location=sidecar_loc))
    if not is_audit_failed:
        findings.extend(check_b2(ctx.entry, ctx.sidecar, ctx.repo_root, location=entry_loc))
        findings.extend(check_b3(ctx.sidecar, ctx.repo_root, location=sidecar_loc))
        findings.extend(check_b4(ctx.sidecar, ctx.repo_root, location=sidecar_loc))
        findings.extend(check_b5(ctx.sidecar, location=sidecar_loc))
    findings.extend(check_b6(ctx.sidecar, ctx.verdict, location=sidecar_loc))
    if not is_audit_failed:
        findings.extend(check_b7(ctx.entry, ctx.sidecar, ctx.entry_path, ctx.sidecar_path,
                                  ctx.jsonl_path, ctx.verdict_path, mode, location=entry_loc,
                                  repo_root=ctx.repo_root, verdict=ctx.verdict))
    findings.extend(check_b8(ctx.entry, mode, location=entry_loc))
    findings.extend(check_b9(ctx.entry, ctx.sidecar, location=entry_loc))
    findings.extend(check_b10(ctx.entry, ctx.verdict, mode, location=entry_loc))

    # Family C
    findings.extend(check_c1(ctx.entry, ctx.verdict, location=entry_loc))
    findings.extend(check_c2(ctx.entry, ctx.sidecar, location=entry_loc))
    # C3 needs prior_entry (passport scan) — skipped in single-entry mode unless
    # the caller passes a passport. For ack entries we'd compare against the latest
    # MATERIAL non-ack entry of the same (stage, agent, deliverable_sha).
    if mode == "persisted" and ctx.passport_audit_artifacts is not None and ctx.entry is not None:
        if "acknowledgement" in ctx.entry:
            prior = _find_latest_material_entry_for_ack(
                ctx.passport_audit_artifacts, ctx.entry)
            if prior is None:
                # Codex round 5 P1 closure: an ack entry without a prior
                # MATERIAL entry of the same (stage, agent, deliverable_sha,
                # run_id) tuple violates C3's copy contract by construction
                # — there is nothing to copy from. A standalone ack or one
                # whose copied fields were altered to break the tuple match
                # would silently pass C3 if `prior is None` skipped the
                # check. Surface as C3 finding.
                findings.append(LintError(
                    "C3",
                    f"acknowledgement entry has no prior MATERIAL entry to copy "
                    f"from: no passport entry matches "
                    f"(stage={ctx.entry.get('stage')!r}, "
                    f"agent={ctx.entry.get('agent')!r}, "
                    f"deliverable_sha={ctx.entry.get('deliverable_sha')!r}, "
                    f"run_id={ctx.entry.get('run_id')!r}) — §5.4 ack mechanism "
                    f"requires the prior MATERIAL entry to exist before append",
                    entry_loc,
                ))
            else:
                findings.extend(check_c3(ctx.entry, prior, location=entry_loc))
    findings.extend(check_c4(ctx.entry, ctx.sidecar, location=entry_loc))

    # Family D
    if ctx.passport_audit_artifacts is not None:
        findings.extend(check_d1(ctx.passport_audit_artifacts, location=str(ctx.passport_path or "<passport>")))
        findings.extend(check_d3(ctx.passport_audit_artifacts, location=str(ctx.passport_path or "<passport>")))
        findings.extend(check_e1_e2_e6(ctx.passport_audit_artifacts, location=str(ctx.passport_path or "<passport>")))

    # Codex round 13 P2 closure: D2/D4 supersession is only meaningful in
    # persisted mode (proposal mode is itself the unmerged proposal). When
    # --mode persisted runs with --output-dir present, scan the dir for
    # OTHER unmerged proposal entries matching the same (stage, agent,
    # deliverable_sha) tuple, then run:
    #   - D2: detect ambiguous proposal selection (proposals sharing
    #     started_at where run_id lex-max would be the only tie-breaker)
    #   - D4: detect supersession requirement — a higher-round unmerged
    #     proposal preempts the persisted entry's Path A selection
    if mode == "persisted" and ctx.output_dir is not None and ctx.output_dir.is_dir() and ctx.entry is not None:
        proposals = _scan_unmerged_proposals(ctx.output_dir, ctx.entry,
                                              exclude_path=ctx.entry_path)
        if proposals:
            findings.extend(check_d2(proposals, location=str(ctx.output_dir)))
            persisted_round = _safe_get(ctx.entry, "verdict", "round")
            for p in proposals:
                proposal_round = _safe_get(p, "entry", "verdict", "round")
                findings.extend(check_d4(
                    persisted_round if isinstance(persisted_round, int) else None,
                    proposal_round if isinstance(proposal_round, int) else None,
                    location=str(p.get("entry_path") or "<proposal-entry>"),
                ))

    # Family E
    findings.extend(check_e3_e4(ctx.entry, mode, location=entry_loc))
    findings.extend(check_e5(ctx.entry, mode, location=entry_loc))
    findings.extend(check_e7(ctx.entry, location=entry_loc))

    # Family F
    if ctx.entry is not None:
        findings.extend(check_f1(ctx.entry.get("run_id"), location=entry_loc))
    findings.extend(check_f2(ctx.jsonl_path, ctx.sidecar_path, ctx.verdict_path,
                              ctx.entry_path, mode, location=entry_loc))
    findings.extend(check_f3(ctx.sidecar, ctx.sidecar_path, location=sidecar_loc))

    return findings


def _find_latest_material_entry_for_ack(
    artifacts: list[dict[str, Any]], ack_entry: dict[str, Any]
) -> dict[str, Any] | None:
    """Find the prior MATERIAL entry (no acknowledgement) matching the ack
    entry's (stage, agent, deliverable_sha, run_id) tuple, latest by verified_at."""
    key = (ack_entry.get("stage"), ack_entry.get("agent"),
           ack_entry.get("deliverable_sha"), ack_entry.get("run_id"))
    candidates = []
    for e in artifacts:
        if not isinstance(e, dict):
            continue
        if "acknowledgement" in e:
            continue
        if (e.get("stage"), e.get("agent"), e.get("deliverable_sha"),
                e.get("run_id")) != key:
            continue
        if _safe_get(e, "verdict", "status") != "MATERIAL":
            continue
        candidates.append(e)
    if not candidates:
        return None
    return max(candidates, key=lambda e: _safe_get(e, "verdict", "verified_at") or "")


def _scan_unmerged_proposals(
    output_dir: Path, persisted_entry: dict[str, Any],
    exclude_path: Path | None = None,
) -> list[dict[str, Any]]:
    """Scan output_dir for unmerged proposal entries matching the persisted
    entry's (stage, agent, deliverable_sha) tuple.

    `exclude_path` is the persisted entry's own path (when present in
    output_dir, e.g. fixture smoke tests where the persisted entry hasn't
    been moved to consumed/ yet) — exclude it so we don't compare an
    entry against itself.

    Returns a list of dicts shaped {entry: <parsed entry>, sidecar: <parsed
    sidecar>, entry_path: <Path>} so D2/D4 callers can read both sides
    (entry has verdict.round; sidecar has timing.started_at).
    Errors loading any single proposal are silently skipped — D2/D4 are
    advisory checks; SCHEMA findings on those files would already fire
    via validate_against_schema if they were the target of --mode
    proposal in a separate invocation.
    """
    key = (persisted_entry.get("stage"), persisted_entry.get("agent"),
           persisted_entry.get("deliverable_sha"))
    proposals: list[dict[str, Any]] = []
    try:
        candidates = sorted(output_dir.glob("*.audit_artifact_entry.json"))
    except OSError:
        return proposals
    exclude_resolved = exclude_path.resolve() if exclude_path is not None else None
    for entry_path in candidates:
        if exclude_resolved is not None:
            try:
                if entry_path.resolve() == exclude_resolved:
                    continue
            except OSError:
                pass
        try:
            entry_data = json.loads(entry_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        if not isinstance(entry_data, dict):
            continue
        # Proposal arm: no verified_at / verified_by
        verdict = entry_data.get("verdict") or {}
        if "verified_at" in verdict or "verified_by" in verdict:
            continue
        if (entry_data.get("stage"), entry_data.get("agent"),
                entry_data.get("deliverable_sha")) != key:
            continue
        # Try to load companion sidecar (for D2 started_at)
        sidecar_path = entry_path.parent / entry_path.name.replace(
            ".audit_artifact_entry.json", ".meta.json")
        sidecar_data: dict[str, Any] = {}
        if sidecar_path.exists():
            try:
                sidecar_data = _load_yaml_or_json(sidecar_path)
                if not isinstance(sidecar_data, dict):
                    sidecar_data = {}
            except Exception:
                sidecar_data = {}
        proposals.append({
            "entry": entry_data,
            "sidecar": sidecar_data,
            "entry_path": entry_path,
        })
    return proposals


# ---------------------------------------------------------------------------
# Schema validation (defense in depth — re-run schemas at lint time)
# ---------------------------------------------------------------------------


def validate_against_schema(doc: Any, schema_path: Path) -> list[LintError]:
    """Validate a document against a JSON Schema; return findings (one per error)."""
    try:
        from jsonschema import Draft202012Validator
        with schema_path.open("r", encoding="utf-8") as f:
            schema = json.load(f)
        validator = Draft202012Validator(
            schema, format_checker=Draft202012Validator.FORMAT_CHECKER
        )
        out: list[LintError] = []
        for err in validator.iter_errors(doc):
            out.append(LintError("SCHEMA",
                f"{err.message} (path={list(err.absolute_path)})",
                str(schema_path.name)))
        return out
    except Exception as e:  # pragma: no cover
        return [LintError("SCHEMA", f"validator error: {e}", str(schema_path.name))]


# ---------------------------------------------------------------------------
# §3.7 F4 example-validation harness
# ---------------------------------------------------------------------------


def run_example_harness(repo_root: Path) -> list[LintError]:
    """F4 — walk docs/design/*.md, find code-fenced example payloads, validate
    against the appropriate schema. Any spec drift emerges as findings.

    We look for fenced blocks marked ```yaml / ```json / ```jsonl. For each
    block, we apply heuristics: if it contains 'verdict_status:' it's a verdict
    file; 'audit_artifact:' is a Schema 9 list of entries; 'codex_cli_version:'
    is a sidecar; first event 'thread.started' is a JSONL stream.
    """
    findings: list[LintError] = []
    design_dir = repo_root / "docs/design"
    if not design_dir.exists():
        return [LintError("F4", f"docs/design not found at {design_dir}", str(design_dir))]

    fence_re = re.compile(r"^```(\w+)?\s*$")
    for md_path in sorted(design_dir.glob("*.md")):
        try:
            text = md_path.read_text(encoding="utf-8")
        except OSError as e:
            findings.append(LintError("F4", f"cannot read: {e}", str(md_path)))
            continue
        lines = text.splitlines()
        in_fence = False
        fence_lang = None
        fence_start = 0
        buffer: list[str] = []
        for lineno, line in enumerate(lines, start=1):
            m = fence_re.match(line)
            if m:
                if not in_fence:
                    in_fence = True
                    fence_lang = (m.group(1) or "").lower()
                    fence_start = lineno
                    buffer = []
                else:
                    block = "\n".join(buffer)
                    findings.extend(_classify_and_validate_block(
                        block, fence_lang, md_path, fence_start))
                    in_fence = False
                    fence_lang = None
                    buffer = []
            elif in_fence:
                buffer.append(line)
    return findings


def _classify_and_validate_block(
    block: str, lang: str | None, md_path: Path, fence_start: int
) -> list[LintError]:
    """Heuristically classify a fenced block and validate against the right schema."""
    out: list[LintError] = []
    location = f"{md_path}:{fence_start}"
    stripped = block.strip()
    if not stripped:
        return []

    # JSONL detection — multiple lines each starting with `{"type":`
    looks_like_jsonl = (
        ("\n" in stripped) and all(
            s.strip().startswith("{") for s in stripped.splitlines() if s.strip()
        )
    )
    # heuristic guard: at least one line looks like a JSON object with a "type" field
    if looks_like_jsonl and ('"type":"thread.started"' in stripped or
                             '"type":"turn.started"' in stripped or
                             '"type":"item.completed"' in stripped):
        # Validate each line against jsonl schema
        try:
            with JSONL_SCHEMA_PATH.open("r", encoding="utf-8") as fh:
                jsonl_schema = json.load(fh)
            from jsonschema import Draft202012Validator
            validator = Draft202012Validator(
                jsonl_schema, format_checker=Draft202012Validator.FORMAT_CHECKER
            )
            for ln_idx, line in enumerate(stripped.splitlines(), start=fence_start + 1):
                line = line.strip()
                if not line:
                    continue
                # Skip ellipsis-only schematic rows from the spec, e.g.
                # `..."input_tokens":...,...`
                if "..." in line:
                    # Mark as "schematic, not validated" if it contains literal '...'
                    out.append(LintError("F4",
                        f"schematic JSONL line contains '...' placeholder (skipped from validation)",
                        f"{md_path}:{ln_idx}",
                        severity="info"))
                    continue
                try:
                    row = json.loads(line)
                except json.JSONDecodeError as e:
                    out.append(LintError("F4",
                        f"invalid JSON in fenced JSONL: {e}",
                        f"{md_path}:{ln_idx}"))
                    continue
                for err in validator.iter_errors(row):
                    out.append(LintError("F4",
                        f"jsonl row drift from schema: {err.message}",
                        f"{md_path}:{ln_idx}"))
        except Exception as e:  # pragma: no cover
            out.append(LintError("F4", f"jsonl harness error: {e}", location))
        return out

    if lang == "yaml":
        # Cheap pre-filter: only parse blocks that LOOK like audit artifacts.
        # The harness's job is to surface drift in §3.1/§3.3/§3.4/§3.5
        # examples, not lint every YAML fence in every design doc.
        audit_signature_keys = (
            "audit_artifact:", "verdict_status:", "codex_cli_version:",
            "primary_deliverables:", "audit_template_path:",
        )
        if not any(sig in stripped for sig in audit_signature_keys):
            return out
        # parse as YAML — use timestamp-as-string loader so we don't double-flag
        # `2026-04-30T15:22:04.123Z` as a YAML datetime object (schema needs str).
        try:
            doc = yaml.load(stripped, Loader=_StrTimestampSafeLoader)
        except yaml.YAMLError as e:
            out.append(LintError("F4", f"yaml parse error: {e}", location))
            return out
        if not isinstance(doc, dict):
            return out
        # Classify
        if "verdict_status" in doc:
            # verdict file
            out.extend([_relabel(f, "F4") for f in
                        validate_against_schema(doc, VERDICT_SCHEMA_PATH)])
            out[-len(out) or 0:] = [_with_location(f, location) for f in out[-len(out) or 0:]]
        elif "codex_cli_version" in doc:
            # sidecar — but note this section may have hyphen drift in timestamps
            out.extend([_with_location(_relabel(f, "F4"), location) for f in
                        validate_against_schema(doc, SIDECAR_SCHEMA_PATH)])
        elif "audit_artifact" in doc:
            # Schema 9 list of persisted entries
            entries = doc.get("audit_artifact") or []
            if isinstance(entries, list):
                for idx, e in enumerate(entries):
                    if isinstance(e, dict):
                        loc = f"{location}:audit_artifact[{idx}]"
                        out.extend([_with_location(_relabel(f, "F4"), loc) for f in
                                    validate_against_schema(e, ENTRY_SCHEMA_PATH)])
        elif {"stage", "agent", "deliverable_path", "run_id"} <= set(doc.keys()):
            # bare entry block
            out.extend([_with_location(_relabel(f, "F4"), location) for f in
                        validate_against_schema(doc, ENTRY_SCHEMA_PATH)])
        return out

    if lang == "json":
        try:
            doc = json.loads(stripped)
        except json.JSONDecodeError:
            return out
        if not isinstance(doc, dict):
            return out
        # Same classification
        if "verdict_status" in doc:
            out.extend([_with_location(_relabel(f, "F4"), location) for f in
                        validate_against_schema(doc, VERDICT_SCHEMA_PATH)])
        elif "codex_cli_version" in doc:
            out.extend([_with_location(_relabel(f, "F4"), location) for f in
                        validate_against_schema(doc, SIDECAR_SCHEMA_PATH)])
        elif {"stage", "agent", "deliverable_path", "run_id"} <= set(doc.keys()):
            out.extend([_with_location(_relabel(f, "F4"), location) for f in
                        validate_against_schema(doc, ENTRY_SCHEMA_PATH)])
        return out

    return out


def _relabel(f: LintError, rule_id: str) -> LintError:
    return LintError(rule_id, f.message, f.location)


def _with_location(f: LintError, location: str) -> LintError:
    return LintError(f.rule_id, f.message, location)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


class _ExUsageParser(argparse.ArgumentParser):
    """ArgumentParser subclass enforcing the EX_USAGE=64 contract.

    Codex round 4 P3 closure: stock argparse calls sys.exit(2) on any
    parser-level failure (invalid --mode value, unknown option, missing
    required arg). The CLI contract documented at the top of this module
    promises 64 EX_USAGE for every bad-CLI-arg case. Override .error() so
    the exit code matches the contract.
    """

    def error(self, message: str) -> None:  # type: ignore[override]
        self.print_usage(sys.stderr)
        print(f"{self.prog}: error: {message}", file=sys.stderr)
        sys.exit(64)


def _build_parser() -> argparse.ArgumentParser:
    p = _ExUsageParser(
        description="Lint audit-artifact contract per ARS v3.6.7 §3.7 invariants.")
    p.add_argument("--mode", choices=("proposal", "persisted", "jsonl-stream"))
    p.add_argument("--example-validation-harness", action="store_true",
                   help="Walk docs/design/*.md and validate fenced example payloads.")
    p.add_argument("--entry", type=Path,
                   help="Path to entry JSON (proposal or persisted).")
    p.add_argument("--sidecar", type=Path,
                   help="Path to sidecar .meta.json. Auto-discovered via run_id when --output-dir given.")
    p.add_argument("--verdict", type=Path,
                   help="Path to verdict .verdict.yaml. Auto-discovered.")
    p.add_argument("--jsonl", type=Path,
                   help="Path to JSONL file. Auto-discovered, or explicitly required by jsonl-stream mode.")
    p.add_argument("--output-dir", type=Path,
                   help="Directory containing the four artifact files (used for auto-discovery).")
    p.add_argument("--passport-path", type=Path,
                   help="Passport YAML/JSON. Enables D1/D3/E2/E6 ledger checks.")
    p.add_argument("--run-id", type=str,
                   help="Used with --output-dir for auto-discovery.")
    p.add_argument("--repo-root", type=Path, default=REPO_ROOT,
                   help="Repo root for B2/B3/B4 disk verification.")
    return p


def _autodiscover(output_dir: Path | None, run_id: str | None,
                  jsonl: Path | None, sidecar: Path | None,
                  verdict: Path | None, entry: Path | None,
                  mode: str) -> tuple[Path | None, Path | None, Path | None, Path | None]:
    """Fill missing artifact paths from --output-dir + --run-id."""
    if output_dir is None:
        return jsonl, sidecar, verdict, entry
    if run_id is None and entry is not None and entry.exists():
        # peek run_id from entry
        try:
            data = json.loads(entry.read_text(encoding="utf-8"))
            run_id = data.get("run_id")
        except Exception:
            pass
    if run_id is None:
        return jsonl, sidecar, verdict, entry
    if jsonl is None:
        jsonl = output_dir / f"{run_id}.jsonl"
    if sidecar is None:
        sidecar = output_dir / f"{run_id}.meta.json"
    if verdict is None:
        verdict = output_dir / f"{run_id}.verdict.yaml"
    if entry is None:
        # Persisted mode entry files are conventionally moved to consumed/
        # at §4.9 step 9, but the CLI must still be able to read an entry
        # the caller has on disk. Default to the bare-run_id name; if not
        # found, fall back to consumed/<run_id>.audit_artifact_entry.json.
        candidate = output_dir / f"{run_id}.audit_artifact_entry.json"
        consumed = output_dir / "consumed" / f"{run_id}.audit_artifact_entry.json"
        if candidate.exists():
            entry = candidate
        elif consumed.exists():
            entry = consumed
        else:
            entry = candidate  # report the missing path in the loader error
    return jsonl, sidecar, verdict, entry


def main(argv: list[str] | None = None) -> int:
    parser = _build_parser()
    args = parser.parse_args(argv)

    # Harness mode
    if args.example_validation_harness:
        repo_root = args.repo_root or REPO_ROOT
        findings = run_example_harness(repo_root)
        for f in findings:
            print(f.render())
        # Only error-severity findings drive a non-zero exit. Info findings
        # (e.g., schematic '...' placeholders the harness intentionally skips)
        # are surfaced but don't fail the run.
        return 1 if any(f.severity == "error" for f in findings) else 0

    if args.mode is None:
        # Phase 6.1 EX_USAGE convention is exit 64. argparse's parser.error()
        # calls sys.exit(2), which would silently downgrade our usage errors;
        # print + return 64 keeps the exit-code contract aligned with
        # scripts/audit_snapshot.py and scripts/run_codex_audit.sh.
        print("ERROR: either --mode or --example-validation-harness is required",
              file=sys.stderr)
        return 64

    # jsonl-stream mode — orchestrator §5.2 L2-5 invocation
    if args.mode == "jsonl-stream":
        if args.jsonl is None:
            print("ERROR: --mode jsonl-stream requires --jsonl", file=sys.stderr)
            return 64
        if not args.jsonl.exists():
            print(f"ERROR: jsonl not found: {args.jsonl}", file=sys.stderr)
            return 2
        try:
            events = _load_jsonl(args.jsonl)
        except ValueError as e:
            print(f"ERROR: {e}", file=sys.stderr)
            return 2
        ctx = LintContext(mode="jsonl-stream", jsonl_events=events,
                          jsonl_path=args.jsonl, repo_root=args.repo_root or REPO_ROOT)
        findings = run_checks(ctx)
        # Per spec §5.2 L2-5 the orchestrator wants the offending item.id and
        # reason on stderr when pairing fails. We mirror to stdout too so the
        # CLI output is grep-friendly in interactive use.
        for f in findings:
            print(f.render())
            print(f.render(), file=sys.stderr)
        return 1 if any(f.severity == "error" for f in findings) else 0

    # proposal / persisted modes
    jsonl, sidecar, verdict, entry = _autodiscover(
        args.output_dir, args.run_id, args.jsonl, args.sidecar,
        args.verdict, args.entry, args.mode,
    )

    if entry is None:
        print(
            f"ERROR: --mode {args.mode} requires --entry (or --output-dir + --run-id)",
            file=sys.stderr,
        )
        return 64

    try:
        entry_data = json.loads(entry.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as e:
        print(f"ERROR: cannot load entry {entry}: {e}", file=sys.stderr)
        return 2

    # Codex round 5 traceback closure: a non-object entry payload (caller
    # passed `[]` / a scalar / null) would crash check_e3_e4 with
    # AttributeError on `entry.get(...)`. Surface as a SCHEMA finding
    # instead — schema validation below would also catch it, but bailing
    # early avoids the cross-field rules running on a non-dict and
    # producing tracebacks before the schema finding is rendered.
    if not isinstance(entry_data, dict):
        print(
            f"ERROR: entry {entry} is not a JSON object "
            f"(got {type(entry_data).__name__}); audit_artifact_entry must be "
            "an object per audit_artifact_entry.schema.json",
            file=sys.stderr,
        )
        return 2

    # Schema validation on the entry first (defense in depth — the oneOf
    # proposal/persisted arms enforce verified_at presence + AUDIT_FAILED
    # exclusion at this layer, before any cross-field rule fires).
    schema_findings: list[LintError] = list(
        validate_against_schema(entry_data, ENTRY_SCHEMA_PATH)
    )

    # Codex round 2 P1 closure: --mode persisted MUST enforce the persisted
    # oneOf arm specifically. JSON Schema oneOf accepts EITHER arm by
    # construction, so a proposal-shaped entry (no verified_at, no
    # verified_by, possibly AUDIT_FAILED status) would silently pass
    # `--mode persisted`. The mode flag is the lifecycle assertion the
    # caller is making about the entry; the lint must enforce it.
    # E3/E4 are the spec rules for proposal-mode rejection of orchestrator
    # fields; the symmetric rule for persisted mode lives here.
    verdict_block = entry_data.get("verdict") if isinstance(entry_data, dict) else None
    if isinstance(verdict_block, dict):
        if args.mode == "persisted":
            # persisted arm requires verified_at + verified_by, forbids AUDIT_FAILED
            if "verified_at" not in verdict_block:
                schema_findings.append(LintError(
                    "E3", "--mode persisted: entry.verdict.verified_at is required "
                          "(entry has proposal-arm shape; orchestrator-side fields missing)",
                    str(entry)))
            if "verified_by" not in verdict_block:
                schema_findings.append(LintError(
                    "E3", "--mode persisted: entry.verdict.verified_by is required "
                          "(entry has proposal-arm shape; orchestrator-side fields missing)",
                    str(entry)))
            if verdict_block.get("status") == "AUDIT_FAILED":
                schema_findings.append(LintError(
                    "E5", "--mode persisted: entry.verdict.status='AUDIT_FAILED' is "
                          "forbidden (AUDIT_FAILED entries are proposal-arm only per "
                          "§3.2 lifecycle-conditional table)",
                    str(entry)))
        elif args.mode == "proposal":
            # proposal arm forbids verified_at + verified_by + acknowledgement
            if "verified_at" in verdict_block:
                schema_findings.append(LintError(
                    "E4", "--mode proposal: entry.verdict.verified_at must be absent "
                          "(orchestrator-only field; wrapper-emitted proposal carrying it "
                          "is Pattern C3 attack surface)",
                    str(entry)))
            if "verified_by" in verdict_block:
                schema_findings.append(LintError(
                    "E4", "--mode proposal: entry.verdict.verified_by must be absent "
                          "(orchestrator-only field; Pattern C3 attack surface)",
                    str(entry)))
            if "acknowledgement" in entry_data:
                schema_findings.append(LintError(
                    "A4", "--mode proposal: entry.acknowledgement must be absent "
                          "(orchestrator-only write per §5.4)",
                    str(entry)))

    # Companion artifacts (sidecar + verdict + jsonl) are REQUIRED in
    # Codex round 16 P2 closure: spec §5.2 says the orchestrator follows
    # entry.artifact_paths, so when caller only passes `--entry` (and a
    # `--repo-root`), fall back to those declared paths to locate the
    # JSONL/sidecar/verdict before emitting "missing companion" errors.
    # The B7 path-resolution check (round 8) still verifies these match
    # the recorded paths; this just removes the ergonomic gap that
    # required redundant flags for a passport/proposal entry that
    # already declares its own artifact bundle.
    artifact_paths = entry_data.get("artifact_paths") if isinstance(entry_data, dict) else None
    if isinstance(artifact_paths, dict):
        repo_root = args.repo_root or REPO_ROOT
        if jsonl is None:
            recorded = artifact_paths.get("jsonl")
            if isinstance(recorded, str) and recorded:
                jsonl = (repo_root / recorded).resolve()
        if sidecar is None:
            recorded = artifact_paths.get("sidecar")
            if isinstance(recorded, str) and recorded:
                sidecar = (repo_root / recorded).resolve()
        if verdict is None:
            recorded = artifact_paths.get("verdict")
            if isinstance(recorded, str) and recorded:
                verdict = (repo_root / recorded).resolve()

    # proposal/persisted modes — they ARE the Layer 2/3 evidence Phase 6.3
    # is supposed to gate (codex round 1 P1: silently treating missing
    # files as None let valid-looking entries return exit 0 with no audit
    # evidence). When auto-discovered or explicitly given path doesn't
    # exist, surface as an artifact-incomplete finding (B7 family — the
    # bundle is supposed to be complete by §4.9 step 9).
    def _missing_companion(role: str, path: Path | None) -> None:
        if path is None:
            schema_findings.append(LintError(
                "B7",
                f"audit bundle missing {role} (auto-discover failed and no explicit "
                f"--{role} given) — proposal/persisted mode requires {role} for "
                f"Layer 2/3 verification",
                f"<{args.mode}>",
            ))
        elif not path.exists():
            schema_findings.append(LintError(
                "B7",
                f"audit bundle missing {role} at {path} — proposal/persisted mode "
                f"requires {role} for Layer 2/3 verification",
                str(path),
            ))

    _missing_companion("sidecar", sidecar)
    _missing_companion("verdict", verdict)
    _missing_companion("jsonl", jsonl)

    sidecar_data = None
    if sidecar is not None and sidecar.exists():
        try:
            sidecar_data = _load_yaml_or_json(sidecar)
        except Exception as e:
            print(f"ERROR: cannot load sidecar {sidecar}: {e}", file=sys.stderr)
            return 2
        # Codex round 6 P2 closure: a non-object companion artifact (e.g.,
        # `[]` parsed as YAML) records a SCHEMA finding via
        # validate_against_schema but `.get(...)` calls in cross-field
        # checks would still raise AttributeError before the finding
        # renders. Coerce non-dict to None so cross-field rules see "no
        # companion" and skip cleanly; the SCHEMA finding still surfaces
        # the rejection and exit code remains 1.
        schema_findings.extend(
            validate_against_schema(sidecar_data, SIDECAR_SCHEMA_PATH)
        )
        if not isinstance(sidecar_data, dict):
            sidecar_data = None

    verdict_data = None
    if verdict is not None and verdict.exists():
        try:
            verdict_data = _load_yaml_or_json(verdict)
        except Exception as e:
            print(f"ERROR: cannot load verdict {verdict}: {e}", file=sys.stderr)
            return 2
        schema_findings.extend(
            validate_against_schema(verdict_data, VERDICT_SCHEMA_PATH)
        )
        if not isinstance(verdict_data, dict):
            verdict_data = None

    events = None
    if jsonl is not None and jsonl.exists():
        # Codex round 11 P2 closure: AUDIT_FAILED bundles can have a
        # partial / non-JSON line at the end (codex was SIGKILL'd
        # mid-write); _load_jsonl() raises ValueError on those, returning
        # exit 2 as internal error and contradicting the round-9 schema
        # suspension immediately below. Decide on AUDIT_FAILED before
        # _load_jsonl runs so failure-signaling proposals with
        # partially-written streams are handled cleanly.
        verdict_status_for_jsonl = (
            verdict_data.get("verdict_status") if isinstance(verdict_data, dict) else None
        )
        if verdict_status_for_jsonl == "AUDIT_FAILED":
            # Skip per-row schema validation entirely; A7 / stream-shape
            # are also suspended in run_checks. Best-effort load still
            # populates events for the entry-side family A rules that
            # don't depend on stream completeness — but a hard parse
            # failure is acceptable evidence of "audit was killed mid-
            # write" rather than a lint-blocking error.
            try:
                events = _load_jsonl(jsonl)
            except ValueError:
                events = None  # forensic-only bundle; stream is unparseable
        else:
            try:
                events = _load_jsonl(jsonl)
            except ValueError as e:
                print(f"ERROR: cannot load jsonl {jsonl}: {e}", file=sys.stderr)
                return 2
            # Validate every JSONL row against the per-row schema. Stream-shape
            # rules (A7 + parse_audit_verdict.py probe-style stream invariants)
            # run separately in the family A check; the per-row schema gate
            # ensures malformed rows don't reach those stream checks.
            for row_idx, row in enumerate(events, start=1):
                schema_findings.extend([
                    LintError(err.rule_id, err.message,
                              f"{jsonl}:row={row_idx}")
                    for err in validate_against_schema(row, JSONL_SCHEMA_PATH)
                ])

    passport_audit_artifacts = None
    if args.passport_path is not None and args.passport_path.exists():
        try:
            passport_data = _load_yaml_or_json(args.passport_path)
            if isinstance(passport_data, dict):
                aa = passport_data.get("audit_artifact")
                if isinstance(aa, list):
                    passport_audit_artifacts = aa
        except Exception as e:
            print(f"ERROR: cannot load passport {args.passport_path}: {e}", file=sys.stderr)
            return 2

    ctx = LintContext(
        mode=args.mode,
        entry=entry_data, entry_path=entry,
        sidecar=sidecar_data, sidecar_path=sidecar,
        verdict=verdict_data, verdict_path=verdict,
        jsonl_events=events, jsonl_path=jsonl,
        output_dir=args.output_dir,
        passport_audit_artifacts=passport_audit_artifacts,
        passport_path=args.passport_path,
        repo_root=args.repo_root or REPO_ROOT,
    )

    # Codex round 12 P2 closure: when any schema-level finding fires, we
    # must NOT proceed into run_checks. Cross-field rules call .get() /
    # set() on nested fields assuming the schema-defined types — a value
    # that satisfies the top-level isinstance(dict) check (added round 5/6)
    # but has a malformed nested field (e.g. timing: [1] satisfies dict at
    # the root but timing.get(...) crashes; finding_ids: [{}] satisfies
    # array but `set(finding_ids)` crashes building a set of unhashable
    # dicts) would trace back instead of producing the documented lint
    # rejection. Short-circuit on any error-severity SCHEMA finding —
    # the schema rejection is itself the lint result; the cross-field
    # rules have nothing to add when the input doesn't match the schema
    # contract they presuppose.
    has_schema_error = any(
        f.rule_id == "SCHEMA" and f.severity == "error" for f in schema_findings
    )
    if has_schema_error:
        for f in schema_findings:
            print(f.render())
        return 1

    findings = schema_findings + run_checks(ctx)
    for f in findings:
        print(f.render())
    return 1 if any(f.severity == "error" for f in findings) else 0


if __name__ == "__main__":
    sys.exit(main())
