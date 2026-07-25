#!/usr/bin/env python3
"""parse_audit_verdict.py — ARS v3.6.7 Step 6 Phase 6.1

Reads a codex CLI 0.125+ --json JSONL event stream and converts the structured
Section 6 verdict text (from the LAST agent_message item.completed event) into
a <run_id>.verdict.yaml file.

Two CLI modes:
  --probe <jsonl>                  Validate only; exit 0 on success, non-zero on failure.
  --jsonl <jsonl> --round N --target-rounds M  Parse + emit YAML to stdout.

Exit codes:
  0   success (probe passed OR full parse emitted YAML)
  non-zero  parse failure (reason on stderr, one line)
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from datetime import datetime, timezone
from typing import Optional

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

GENERATED_BY = "scripts/run_codex_audit.sh"
GENERATOR_VERSION = "1.0.0"

# run_id filename pattern: YYYY-MM-DDTHH-MM-SSZ-XXXX  (hyphens, not colons)
RUN_ID_RE = re.compile(
    r"^[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}-[0-9]{2}-[0-9]{2}Z-[0-9a-f]{4}$"
)

# F-019 (§3.3): canonical UUID regex for thread.started.thread_id validation.
# codex 0.125+ always emits a lowercase-hex UUID in this exact format.
# A non-matching value indicates a malformed or forged stream.
_THREAD_ID_RE = re.compile(
    r"^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$"
)

# Valid dimension values (string enum per audit_verdict.schema.json)
VALID_DIMENSIONS = {"3.1", "3.2", "3.3", "3.4", "3.5", "3.6", "3.7", "4(f)"}

# ---------------------------------------------------------------------------
# JSONL parsing
# ---------------------------------------------------------------------------


def load_events(jsonl_path: str) -> list[dict]:
    """Read all JSONL rows from the given file path.

    Returns a list of parsed dicts.  Raises ParseError on file-level failures.
    """
    if not os.path.exists(jsonl_path):
        raise ParseError(f"jsonl file not found: {jsonl_path}")
    with open(jsonl_path, encoding="utf-8") as fh:
        raw = fh.read().strip()
    if not raw:
        raise ParseError(f"jsonl file is empty: {jsonl_path}")

    events: list[dict] = []
    for lineno, line in enumerate(raw.splitlines(), start=1):
        line = line.strip()
        if not line:
            continue
        try:
            row = json.loads(line)
        except json.JSONDecodeError as exc:
            raise ParseError(f"invalid JSON at row {lineno}: {exc}") from exc
        # F-027 (P3, R7): each row must be a JSON object so .get/[] work later.
        if not isinstance(row, dict):
            raise ParseError(
                f"jsonl row {lineno} is not an object: {type(row).__name__}"
            )
        events.append(row)
    return events


def validate_stream_shape(events: list[dict]) -> None:
    """Validate that the JSONL event stream has the expected clean-run shape.

    F-002 (§3.6) — Round 3 fix: anchors checks 6, 7, 8 on the FIRST
    turn.completed event (not the last).  Rounds 1-2 used last_turn_completed_idx
    throughout, which allowed the multi-turn.completed forgery:

        thread.started → turn.started → real_agent_message → turn.completed_1
            → forged_agent_message → turn.completed_2

    Under the Round 2 logic: last_turn_completed_idx pointed to turn.completed_2,
    so trailing = [] (nothing after TC_2, check 7 passed), and TC_2 < TC_2 was
    False (check 6 passed), but extract_verdict_text returned the forged message.

    Fix: locate the FIRST turn.completed.  Per §3.3 a clean run has exactly ONE
    turn.completed, at the end.  Check 7 (no trailing events after first TC) rejects
    any second TC as an illegal trailing event, and check 6 verifies the first TC
    appears after the last agent_message.  Both checks together enforce exactly-one-TC.

    Per §3.3 canonical no-tool run sequence:
      thread.started → turn.started → item.completed(agent_message) → turn.completed

    Checks:
      1. Exactly one thread.started event (multiple → forgery surface).
      2. First event is thread.started.
      3. Second event is turn.started (per §3.3 canonical sequence).
      4. No error event anywhere in the stream.
      5. Stream contains at least one agent_message.
      6. FIRST turn.completed appears after the last agent_message.
      7. No events after the FIRST turn.completed (clean run ends with first TC;
         any trailing event — including a second TC — is a forgery indicator).
      8. first turn.completed.usage.input_tokens > 0 (real codex always consumes input).
      9. thread.started.thread_id matches canonical UUID regex (F-019 §3.3).
     10. All four turn.completed.usage fields present, integers, >= 0 (F-019 §3.3).

    Raises ParseError if any check fails. Probe rejection cascades into the
    wrapper's AUDIT_FAILED branch per §4.6 case (b).
    """
    if not events:
        raise ParseError("stream is empty")

    # Check 1: exactly one thread.started event (§3.3: thread_id emitted ONCE)
    thread_started_count = sum(1 for ev in events if ev.get("type") == "thread.started")
    if thread_started_count == 0:
        raise ParseError(
            f"stream missing thread.started event (got first: {events[0].get('type')!r})"
        )
    if thread_started_count > 1:
        raise ParseError(
            f"stream has {thread_started_count} thread.started events; expected exactly 1"
        )

    # Check 2: first event is thread.started
    if events[0].get("type") != "thread.started":
        raise ParseError(
            f"stream first event is not thread.started (got: {events[0].get('type')!r})"
        )

    # Check 3: second event is turn.started (per §3.3 canonical sequence)
    if len(events) < 2 or events[1].get("type") != "turn.started":
        got = events[1].get("type") if len(events) >= 2 else "(stream too short)"
        raise ParseError(
            f"stream second event is not turn.started (got: {got!r})"
        )

    # Check 4: no error event anywhere in the stream
    if any(ev.get("type") == "error" for ev in events):
        raise ParseError("stream contains error event (codex was killed or errored mid-run)")

    # Locate the FIRST turn.completed (F-002 Round 3: must use FIRST, not last).
    # Per §3.3 a clean run has exactly one turn.completed at the stream end.
    # Using last_turn_completed_idx (Rounds 1-2) allowed a forged second TC to
    # make trailing[] appear empty while hiding a forged agent_message between TC_1
    # and TC_2.  Anchoring on FIRST TC collapses that window.
    first_turn_completed_idx = -1
    for idx, ev in enumerate(events):
        if ev.get("type") == "turn.completed":
            first_turn_completed_idx = idx
            break  # stop at FIRST occurrence

    # Locate the last agent_message (verdict-bearing event per §3.3 contract).
    # F-027 (P3, R7) + F-030 (P3, R8/R9): malformed `item` on item.started/
    # item.completed events is rejected outright. Per spec §3.3 schema, `item`
    # is an object with required `id` (non-empty string) + `type` (non-empty
    # string); object-shaped rows missing those keys are still malformed.
    last_agent_msg_idx = -1
    for idx, ev in enumerate(events):
        ev_type = ev.get("type")
        if ev_type not in ("item.completed", "item.started"):
            continue
        item = ev.get("item")
        if not isinstance(item, dict):
            raise ParseError(
                f"event {idx} ({ev_type}) has malformed item field: "
                f"{type(item).__name__}"
            )
        # F-030 R9 closure: enforce required item.id + item.type as non-empty strings.
        item_id = item.get("id")
        item_type = item.get("type")
        if not isinstance(item_id, str) or not item_id:
            raise ParseError(
                f"event {idx} ({ev_type}) item.id is not a non-empty string: {item_id!r}"
            )
        if not isinstance(item_type, str) or not item_type:
            raise ParseError(
                f"event {idx} ({ev_type}) item.type is not a non-empty string: {item_type!r}"
            )
        if ev_type == "item.completed" and item_type == "agent_message":
            last_agent_msg_idx = idx

    # Check 5: at least one agent_message present
    if last_agent_msg_idx == -1:
        raise ParseError("no agent_message in stream")

    # Check 6: FIRST turn.completed must exist and appear after the last agent_message.
    # (F-002 R3: anchored on first_turn_completed_idx, not last_turn_completed_idx)
    if first_turn_completed_idx == -1:
        raise ParseError(
            "stream missing turn.completed event (codex was killed mid-run)"
        )
    if first_turn_completed_idx < last_agent_msg_idx:
        raise ParseError(
            "turn.completed appears before last agent_message "
            "(stream truncated or forged; first turn.completed must follow all agent messages)"
        )

    # Check 7: NO events after the FIRST turn.completed.
    # (F-002 R3: anchored on first_turn_completed_idx, not last_turn_completed_idx)
    # This implicitly enforces exactly-one-TC: any second turn.completed would appear
    # here as a trailing event and be rejected.  Per §3.3 §line 284, a clean codex run
    # always ends at the single turn.completed event.
    trailing = events[first_turn_completed_idx + 1:]
    if trailing:
        trailing_types = [ev.get("type") for ev in trailing]
        raise ParseError(
            f"unexpected event(s) after turn.completed: {trailing_types!r} "
            f"(stream must end at first turn.completed per §3.3)"
        )

    # Check 9 (F-019 §3.3): thread_id must match canonical UUID format.
    # codex 0.125+ always emits a lowercase-hex UUID on the thread.started event.
    # A non-canonical value indicates a malformed or forged stream header.
    # F-025 (P3, R6): thread_id must be a string before regex match.
    # `events[0].get("thread_id", "")` returns None / list / int verbatim if
    # the key holds those types — feeding non-string to _THREAD_ID_RE.match
    # raises TypeError. Explicit type guard turns it into a clean ParseError.
    thread_id = events[0].get("thread_id")
    if not isinstance(thread_id, str):
        raise ParseError(
            f"thread.started.thread_id is not a string: {type(thread_id).__name__}"
        )
    if not _THREAD_ID_RE.match(thread_id):
        raise ParseError(
            f"thread.started.thread_id is not canonical UUID: {thread_id!r}"
        )

    # Check 10 (F-019 §3.3): all four usage fields must be present, integers,
    # and non-negative.  Type validation runs FIRST (F-022 §3.3) so non-int
    # values (e.g., "1" as string) raise a one-line ParseError instead of an
    # unhandled traceback in the input_tokens > 0 comparison below.
    turn_completed = events[first_turn_completed_idx]
    # F-025 (P3, R6): usage must be a dict before `in` / index operations.
    # JSONL with `usage: null` or `usage: []` would otherwise raise TypeError.
    usage = turn_completed.get("usage")
    if not isinstance(usage, dict):
        raise ParseError(
            f"turn.completed.usage is not an object: {type(usage).__name__}"
        )
    _USAGE_FIELDS = (
        "input_tokens",
        "cached_input_tokens",
        "output_tokens",
        "reasoning_output_tokens",
    )
    for fld in _USAGE_FIELDS:
        if fld not in usage:
            raise ParseError(f"turn.completed.usage missing field: {fld!r}")
        if not isinstance(usage[fld], int) or isinstance(usage[fld], bool):
            raise ParseError(
                f"turn.completed.usage.{fld} is not int: {usage[fld]!r}"
            )
        if usage[fld] < 0:
            raise ParseError(
                f"turn.completed.usage.{fld} is negative: {usage[fld]}"
            )

    # Check 8: first turn.completed.usage.input_tokens > 0 (§3.3 line 277, Q3 line 63).
    # Real codex always consumes input; zero → forgery indicator.
    # Runs AFTER Check 10 so input_tokens is guaranteed-int by this point.
    if usage["input_tokens"] <= 0:
        raise ParseError(
            f"turn.completed.usage.input_tokens is {usage['input_tokens']} "
            "(real codex runs always consume input tokens; zero indicates forgery)"
        )


def extract_verdict_text(events: list[dict]) -> str:
    """Return the text of the LAST item.completed agent_message event.

    Per §3.3 contract: tool-using runs emit intermediate agent_message events
    between tool calls; the verdict-bearing event is always the LAST one.

    F-027 (P3, R7): each event's `item` field must be a dict before .get;
    `item.text` for agent_message must be a non-empty string. Malformed types
    raise clean ParseError instead of TypeError tracebacks.
    """
    agent_messages: list[dict] = []
    for idx, row in enumerate(events):
        if row.get("type") != "item.completed":
            continue
        item = row.get("item")
        if not isinstance(item, dict):
            raise ParseError(
                f"event {idx} (item.completed) has malformed item field: "
                f"{type(item).__name__}"
            )
        if item.get("type") != "agent_message":
            continue
        agent_messages.append(row)
    if not agent_messages:
        raise ParseError("no agent_message in stream")
    last_item = agent_messages[-1].get("item", {})
    verdict_text = last_item.get("text")
    if not isinstance(verdict_text, str) or not verdict_text:
        raise ParseError(
            f"agent_message.item.text is not a non-empty string: "
            f"{type(verdict_text).__name__}"
        )
    return verdict_text


# ---------------------------------------------------------------------------
# Section 6 text parsing
# ---------------------------------------------------------------------------

# Summary line patterns (two canonical forms per audit template Section 6):
#
#   Form A (findings present):
#     "Round N: P1×n1 / P2×n2 / P3×n3 (M total)"
#   Form B (zero findings):
#     "Round N: 0 findings of any severity. Convergence reached."
#
# Both forms may be preceded by "Previous rounds: Round 1: ... ; all P1 ..." on
# the same or adjacent line — we anchor on the ROUND value passed via CLI to
# pick the authoritative summary line rather than a "previous rounds" recap.

# Matches: Round N: P1×n1 / P2×n2 / P3×n3 (M total)
#
# F-011 (§3.6) Round 2 fixes:
#   1. (M total) parenthetical is now MANDATORY (was optional "(?:...)?").
#      A summary line without the parenthetical is malformed per audit template
#      Section 6 line 160 and should cascade to "no parseable Section 6 summary"
#      → AUDIT_FAILED rather than silently accepting an unchecked total.
#   2. Anchored to start-of-line (^) and end-of-line ($) with re.MULTILINE to
#      prevent partial matches on lines containing "Round N:" as a substring
#      (e.g., finding entries that restate the round number in their description).
_SUMMARY_A = re.compile(
    r"^\s*Round\s+(\d+)\s*:\s*P1[×x×](\d+)\s*/\s*P2[×x×](\d+)\s*/\s*P3[×x×](\d+)"
    r"\s*\((\d+)\s*total\)\s*$",
    re.IGNORECASE | re.MULTILINE,
)

# Matches: Round N: 0 findings of any severity. Convergence reached.
# F-011: anchored similarly for consistency — avoids substring hits in
# "Previous rounds: Round 1: 0 findings ..." recap lines.
_SUMMARY_B = re.compile(
    r"^\s*Round\s+(\d+)\s*:\s*0\s+findings\s+of\s+any\s+severity[.,]?\s*Convergence\s+reached.*$",
    re.IGNORECASE | re.MULTILINE,
)

# Finding entry pattern (tolerant of formatting variation):
#
# Codex emits lines like:
#   1. **F-007** P3 §3.7 chapter_4/synthesis.md:482 — description. Fix: fix text.
#   2. **F-001** P1 3.2 path/file.md:10 - description here. Fix: suggested fix.
#
# Groups: (list_num, finding_id, severity, dimension, file, line, description, fix_text)
#
# Strategy:
#   - Finding ID: **F-NNN** (bold markdown) or bare F-NNN
#   - Severity: P1 / P2 / P3 (standalone word)
#   - Dimension: §3.1–§3.7 (with or without § prefix) or 4(f)
#   - file:line anchor (greedy non-space path, colon, integer)
#   - Description and Fix separated by "Fix:" label (case-insensitive)
#
# We use a two-pass approach: first match the structural header (id/sev/dim/file:line),
# then extract description + fix from the tail.

_FINDING_HEADER = re.compile(
    r"^\s*\d+\.\s+"                          # numbered list item: "1. "
    r"\*{0,2}(F-[0-9]{3,})\*{0,2}"          # finding ID: **F-007** or F-007
    r"\s+"
    r"(P[123])"                              # severity: P1 P2 P3
    r"\s+"
    r"(?:§)?(3\.[1-7]|4\(f\))"              # dimension: §3.x or 4(f) (with or without §)
    r"\s+"
    r"([^\s:]+)"                             # file path (no spaces, stops before colon)
    r":([0-9]+)"                             # :line
    r"\s*[-—–]+\s*"                          # separator: — or - or –
    r"(.+)",                                 # rest of line (description + fix)
    re.IGNORECASE,
)

# Fix label separator within the rest-of-line tail
# e.g.: "deictic phrase. Fix: replace with ..."
#       "description here. Fix: suggested fix here."
_FIX_SEPARATOR = re.compile(r"\.\s*Fix\s*:\s*", re.IGNORECASE)


def _parse_dimension(raw: str) -> str:
    """Normalize raw dimension string to the schema enum value."""
    d = raw.lstrip("§").strip()
    if d in VALID_DIMENSIONS:
        return d
    raise ParseError(f"malformed finding entry: unknown dimension '{raw}'")


def _parse_finding_line(line: str) -> Optional[dict]:
    """Attempt to parse one numbered finding line.  Returns None if no match."""
    m = _FINDING_HEADER.match(line)
    if not m:
        return None

    finding_id, severity, dimension_raw, file_path, line_num, tail = m.groups()
    finding_id = finding_id.upper()
    severity = severity.upper()
    dimension = _parse_dimension(dimension_raw)
    line_int = int(line_num)

    # Split tail into description and suggested_fix at ". Fix: "
    fix_parts = _FIX_SEPARATOR.split(tail, maxsplit=1)
    if len(fix_parts) == 2:
        description = fix_parts[0].strip().rstrip(".")
        suggested_fix = fix_parts[1].strip().rstrip(".")
    else:
        # No "Fix:" separator found — description consumes entire tail,
        # suggested_fix is missing → malformed entry.
        raise ParseError(
            f"malformed finding entry: no 'Fix:' separator in line: {line!r}"
        )

    if not description:
        raise ParseError(f"malformed finding entry: empty description for {finding_id}")
    if not suggested_fix:
        raise ParseError(
            f"malformed finding entry: empty suggested_fix for {finding_id}"
        )

    return {
        "id": finding_id,
        "severity": severity,
        "dimension": dimension,
        "file": file_path,
        "line": line_int,
        "description": description,
        "suggested_fix": suggested_fix,
    }


def parse_section6(
    text: str,
    current_round: Optional[int] = None,
) -> tuple[dict, list[dict]]:
    """Parse Section 6 verdict text.

    Returns (finding_counts, findings_list) where:
      finding_counts  = {"p1": int, "p2": int, "p3": int}
      findings_list   = list of finding dicts

    Raises ParseError if no authoritative summary line is found or if
    finding_counts disagrees with the parsed findings list.

    current_round: when provided, use to locate the authoritative summary line
    (avoiding "Previous rounds: Round 1: …" recaps).  When None (probe mode),
    accept the last parseable summary line.
    """
    lines = text.splitlines()

    # ---- Step 1: locate the authoritative summary line -----
    # We scan ALL lines and collect all summary-line matches.
    # If current_round is known, we require the summary to match that round.
    # If not (probe), we accept any match and take the last one.

    summary_counts: Optional[tuple[int, int, int]] = None  # (p1, p2, p3)
    # F-011: track the authoritative summary line's text for last-line check
    _authoritative_summary_line: Optional[str] = None

    for line in lines:
        # Try Form B first (zero-findings convergence line)
        mb = _SUMMARY_B.search(line)
        if mb:
            r = int(mb.group(1))
            if current_round is None or r == current_round:
                summary_counts = (0, 0, 0)
                _authoritative_summary_line = line.strip()
                if current_round is not None:
                    break
            continue

        # Try Form A (P1×n / P2×n / P3×n)
        ma = _SUMMARY_A.search(line)
        if ma:
            r, n1, n2, n3 = (
                int(ma.group(1)),
                int(ma.group(2)),
                int(ma.group(3)),
                int(ma.group(4)),
            )
            if current_round is None or r == current_round:
                # F-011: cross-validate (N total) parenthetical when present.
                # "Round 2: P1×0 / P2×3 / P3×1 (5 total)" should reject because
                # 0+3+1=4 ≠ 5. group(5) is None when parenthetical is absent.
                total_group = ma.group(5)
                if total_group is not None:
                    total_claimed = int(total_group)
                    total_computed = n1 + n2 + n3
                    if total_claimed != total_computed:
                        raise ParseError(
                            f"summary line total {total_claimed} disagrees with "
                            f"bucket sum {total_computed} (P1×{n1}+P2×{n2}+P3×{n3})"
                        )
                summary_counts = (n1, n2, n3)
                _authoritative_summary_line = line.strip()
                if current_round is not None:
                    break

    if summary_counts is None:
        raise ParseError("no parseable Section 6 summary")

    # F-011: require the authoritative summary line to be the LAST non-empty
    # line of the verdict text. Audit template Section 6 format puts the summary
    # at the end; an interior summary line indicates a malformed or shadowed
    # verdict (e.g. "Previous rounds" recap in the wrong position).
    non_empty_lines = [ln.strip() for ln in lines if ln.strip()]
    if non_empty_lines and _authoritative_summary_line is not None:
        last_nonempty = non_empty_lines[-1]
        # The authoritative summary line must match the last non-empty line.
        # We do a substring check because the line may be embedded in a longer
        # line (e.g. with markdown emphasis markers around it).
        if _authoritative_summary_line not in last_nonempty and last_nonempty not in _authoritative_summary_line:
            raise ParseError(
                "summary line is not the last non-empty line of the verdict text "
                "(found interior summary; expected it at the end per audit template Section 6)"
            )

    # ---- Step 2: parse individual finding entries ----
    findings: list[dict] = []
    for line in lines:
        # Skip summary lines to avoid spurious matches
        if _SUMMARY_A.search(line) or _SUMMARY_B.search(line):
            continue
        result = _parse_finding_line(line)
        if result is not None:
            findings.append(result)

    # ---- Step 3: cross-validate counts vs parsed findings ----
    p1_exp, p2_exp, p3_exp = summary_counts
    p1_got = sum(1 for f in findings if f["severity"] == "P1")
    p2_got = sum(1 for f in findings if f["severity"] == "P2")
    p3_got = sum(1 for f in findings if f["severity"] == "P3")

    if (p1_got, p2_got, p3_got) != (p1_exp, p2_exp, p3_exp):
        raise ParseError(
            f"finding_counts disagrees with findings[] "
            f"(summary: P1×{p1_exp}/P2×{p2_exp}/P3×{p3_exp}, "
            f"parsed: P1×{p1_got}/P2×{p2_got}/P3×{p3_got})"
        )

    finding_counts = {"p1": p1_exp, "p2": p2_exp, "p3": p3_exp}
    return finding_counts, findings


# ---------------------------------------------------------------------------
# Status classification (§3.2 cross-field rule)
# ---------------------------------------------------------------------------


def classify_status(finding_counts: dict) -> str:
    """Derive verdict_status from finding_counts per spec §3.2 cross-field rules.

    F-012 (§3.2): original implementation omitted the p3 upper bound, classifying
    p3=4 as MINOR instead of MATERIAL.  Per spec lines 231-233:

      PASS:     p1 == 0 AND p2 == 0 AND p3 == 0
      MINOR:    p1 == 0 AND p2 == 0 AND 1 <= p3 <= 3
      MATERIAL: p1 > 0 OR p2 > 0 OR p3 > 3

    Contract-critical: a 4-P3-finding audit mis-classified as MINOR lets the
    orchestrator escalate to user instead of BLOCKing — silent severity downgrade.
    """
    p1, p2, p3 = finding_counts["p1"], finding_counts["p2"], finding_counts["p3"]
    if p1 == 0 and p2 == 0 and p3 == 0:
        return "PASS"
    if p1 == 0 and p2 == 0 and 1 <= p3 <= 3:
        return "MINOR"
    return "MATERIAL"


# ---------------------------------------------------------------------------
# YAML serialisation (hand-rolled — standard library only)
# ---------------------------------------------------------------------------


def _yaml_str(value: str) -> str:
    """Double-quote a string value to safely embed colons, brackets, and backslashes."""
    escaped = value.replace("\\", "\\\\").replace('"', '\\"')
    return f'"{escaped}"'


def render_verdict_yaml(
    run_id: str,
    verdict_status: str,
    round_num: int,
    target_rounds: int,
    finding_counts: dict,
    findings: list[dict],
    generated_at: str,
) -> str:
    """Serialize verdict fields to YAML string.

    Hand-rolled to avoid PyYAML dependency and to produce a deterministic,
    human-readable output matching the §3.5 example shape.
    """
    lines: list[str] = []

    lines.append(f"run_id: {run_id}")
    lines.append(f"verdict_status: {verdict_status}")
    lines.append(f"round: {round_num}")
    lines.append(f"target_rounds: {target_rounds}")
    lines.append("finding_counts:")
    lines.append(f"  p1: {finding_counts['p1']}")
    lines.append(f"  p2: {finding_counts['p2']}")
    lines.append(f"  p3: {finding_counts['p3']}")

    if findings:
        lines.append("findings:")
        for f in findings:
            lines.append(f"  - id: {f['id']}")
            lines.append(f"    severity: {f['severity']}")
            lines.append(f"    dimension: {_yaml_str(f['dimension'])}")
            lines.append(f"    file: {_yaml_str(f['file'])}")
            lines.append(f"    line: {f['line']}")
            lines.append(f"    description: {_yaml_str(f['description'])}")
            lines.append(f"    suggested_fix: {_yaml_str(f['suggested_fix'])}")
    else:
        lines.append("findings: []")

    # F-013 (§3.5): ISO 8601 timestamps are parsed as Python datetime objects by
    # PyYAML's default loader (Loader=FullLoader / SafeLoader), violating the
    # schema's type:string constraint.  Wrap in _yaml_str() to force YAML string.
    lines.append(f"generated_at: {_yaml_str(generated_at)}")
    lines.append(f"generated_by: {_yaml_str(GENERATED_BY)}")
    lines.append(f"generator_version: {_yaml_str(GENERATOR_VERSION)}")

    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------------------
# Error type
# ---------------------------------------------------------------------------


class ParseError(Exception):
    """Raised when the JSONL stream or verdict text cannot be parsed."""


# ---------------------------------------------------------------------------
# CLI entry point
# ---------------------------------------------------------------------------


def _now_rfc3339_ms() -> str:
    """Return current UTC timestamp with millisecond precision: YYYY-MM-DDTHH:MM:SS.mmmZ"""
    now = datetime.now(timezone.utc)
    return now.strftime("%Y-%m-%dT%H:%M:%S.") + f"{now.microsecond // 1000:03d}Z"


def _extract_run_id(jsonl_path: str) -> str:
    """Extract run_id from JSONL filename basename (strip .jsonl extension)."""
    basename = os.path.basename(jsonl_path)
    # Strip .jsonl extension (required)
    if basename.endswith(".jsonl"):
        run_id = basename[: -len(".jsonl")]
    else:
        run_id = basename
    if not RUN_ID_RE.match(run_id):
        raise ParseError(
            f"jsonl filename '{basename}' does not match run_id pattern "
            f"YYYY-MM-DDTHH-MM-SSZ-XXXX (got '{run_id}')"
        )
    return run_id


def cmd_probe(jsonl_path: str) -> int:
    """Run probe mode: validate JSONL has parseable agent_message + Section 6 summary.

    Exit 0 on success, non-zero on failure.  No YAML output.
    Per spec §4.4 Step 4 and §4.6 case (b): probe does not require
    --round / --target-rounds.  Cross-field count validation is deferred to
    full parse (requires --round to anchor the authoritative summary line).

    F-002 (§3.6): validates stream shape (thread.started first, no error event,
    turn.completed after last agent_message) before accepting PASS/MINOR/MATERIAL.
    """
    try:
        events = load_events(jsonl_path)
        # F-002: stream-shape sanity check before content parsing
        validate_stream_shape(events)
        verdict_text = extract_verdict_text(events)
        # Probe: accept any parseable summary line (current_round=None)
        parse_section6(verdict_text, current_round=None)
        return 0
    except ParseError as exc:
        print(str(exc), file=sys.stderr)
        return 1


def cmd_jsonl(
    jsonl_path: str,
    round_num: int,
    target_rounds: int,
) -> int:
    """Full parse mode: parse JSONL and emit verdict YAML to stdout.

    Exit 0 on success; non-zero on failure (reason on stderr).

    F-002 (§3.6): validates stream shape before classification to ensure a
    SIGKILL'd or errored codex run cannot yield PASS/MINOR/MATERIAL status.
    """
    try:
        run_id = _extract_run_id(jsonl_path)
        events = load_events(jsonl_path)
        # F-002: stream-shape sanity check before classification
        validate_stream_shape(events)
        verdict_text = extract_verdict_text(events)
        finding_counts, findings = parse_section6(verdict_text, current_round=round_num)
        verdict_status = classify_status(finding_counts)
        generated_at = _now_rfc3339_ms()

        yaml_out = render_verdict_yaml(
            run_id=run_id,
            verdict_status=verdict_status,
            round_num=round_num,
            target_rounds=target_rounds,
            finding_counts=finding_counts,
            findings=findings,
            generated_at=generated_at,
        )
        sys.stdout.write(yaml_out)
        return 0
    except ParseError as exc:
        print(str(exc), file=sys.stderr)
        return 1


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        description=(
            "Parse codex CLI 0.125+ --json JSONL stream into verdict YAML.\n"
            "Modes: --probe (validate only) or --jsonl (emit YAML to stdout)."
        )
    )
    mode = p.add_mutually_exclusive_group(required=True)
    mode.add_argument(
        "--probe",
        metavar="JSONL",
        dest="probe_path",
        help="Validate JSONL has parseable agent_message + Section 6 summary; "
        "exit 0 on success, non-zero on failure.  No YAML output.",
    )
    mode.add_argument(
        "--jsonl",
        metavar="JSONL",
        dest="jsonl_path",
        help="Parse JSONL and emit verdict YAML to stdout.  "
        "Requires --round and --target-rounds.",
    )
    p.add_argument(
        "--round",
        type=int,
        metavar="ROUND",
        help="Audit round number (required with --jsonl).",
    )
    p.add_argument(
        "--target-rounds",
        type=int,
        metavar="TARGET_ROUNDS",
        help="Total target rounds (required with --jsonl).",
    )
    return p


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()

    if args.probe_path is not None:
        return cmd_probe(args.probe_path)

    # --jsonl mode: validate required companion flags
    if args.round is None or args.target_rounds is None:
        parser.error("--jsonl requires both --round and --target-rounds")

    if args.round < 1:
        parser.error("--round must be >= 1")
    if args.target_rounds < 1:
        parser.error("--target-rounds must be >= 1")
    if args.round > args.target_rounds:
        parser.error(f"--round ({args.round}) must be <= --target-rounds ({args.target_rounds})")

    return cmd_jsonl(
        jsonl_path=args.jsonl_path,
        round_num=args.round,
        target_rounds=args.target_rounds,
    )


if __name__ == "__main__":
    sys.exit(main())
