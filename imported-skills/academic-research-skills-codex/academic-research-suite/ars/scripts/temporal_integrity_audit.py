#!/usr/bin/env python3
"""v3.9.4 Phase 4 → 5 boundary temporal integrity verifier.

5 passes per spec §3.2:
  P1 — Mode 1 future-as-past arithmetic (TEMPORAL-ARITHMETIC-IMPOSSIBLE)
  P2 — Mode 2 version-as-evidence-past anachronism (TEMPORAL-ANACHRONISTIC-CITATION)
  P3 — Mode 3 comparator unmaterialized (TEMPORAL-COMPARATOR-UNMATERIALIZED)
  P4 — Mode 4 causal inversion (TEMPORAL-CAUSAL-INVERSION)
  P5 — Mode 5 time-bomb deictic (TEMPORAL-DEICTIC)
  + TEMPORAL-METADATA-MISSING surfacing where ground truth is unavailable.

All findings advisory in v3.9.4 (CC1).
Inputs: finalized draft markdown with v3.7.3 <!--ref:slug--> markers, timeline.yaml, citation_provenance.yaml.
Output: phase4_composition/temporal_audit_results.yaml (machine-readable) + .md (human-readable, Task 17).

This Task 9 ships the scaffold. P1-P5 implementations land in Tasks 10-16. Markdown output in Task 17.
"""
from __future__ import annotations

import argparse
import re
import sys
from datetime import date
from pathlib import Path

import yaml

DEICTIC_PATTERN = re.compile(
    r"\b(currently|now|at present|most recent|the latest|new(?:est)?|recently|"
    r"last\s+year|this\s+year|nowadays|presently|today|emerging|recent\s+cycle|"
    r"latest\s+available)\b",
    re.IGNORECASE,
)

MONTH_NAMES = "January|February|March|April|May|June|July|August|September|October|November|December"
DATE_REGEX = (
    r"\d{4}-\d{2}-\d{2}"
    r"|(?:" + MONTH_NAMES + r")\s+\d{4}"
    r"|(?:19|20)\d{2}"
)

PATTERN_A = re.compile(
    r"(?:as of|on|in|reported in|stated in|noted in)\s+"
    r"(?P<anchor>" + DATE_REGEX + r")"
    r".*?\b(?:had already|already|completed|finished|delivered)\b.*?"
    r"(?P<event>" + DATE_REGEX + r")",
    re.IGNORECASE | re.DOTALL,
)

PATTERN_B = re.compile(
    r"(?P<event>" + DATE_REGEX + r")"
    r".*?\b(?:will be|to be|scheduled for|forthcoming|upcoming|planned)\b.*?"
    r"(?:as of|in|by)\s+"
    r"(?P<anchor>" + DATE_REGEX + r")",
    re.IGNORECASE | re.DOTALL,
)

REF_MARKER_PATTERN = re.compile(r"<!--ref:([A-Za-z][A-Za-z0-9_:-]*)-->")

COMPARATOR_FORM_A = re.compile(
    r"(?P<adj>prior|previous|earlier|older|preceding)\s+"
    r"(?P<noun>edition|version|edition\s+\(\d{4}\)|version\s+\(\d{4}\))",
    re.IGNORECASE,
)
COMPARATOR_FORM_B = re.compile(
    r"\b(?P<year>(?:19|20)\d{2})\s+"
    r"(?P<noun>edition|version|standard|handbook|guideline)\b",
    re.IGNORECASE,
)
COMPARATOR_FORM_C = re.compile(
    r"(?P<noun>edition|version|standard)\s+(?:of|from)\s+"
    r"(?P<year>(?:19|20)\d{2})\b",
    re.IGNORECASE,
)

# 8 verb-to-required-ordering triggers per spec §3.2 P4
CAUSAL_TRIGGERS = [
    (re.compile(r"\benabled\b", re.IGNORECASE), "left<right"),
    (re.compile(r"\bcaused\b", re.IGNORECASE), "left<right"),
    (re.compile(r"\bled\s+to\b", re.IGNORECASE), "left<right"),
    (re.compile(r"\bin\s+response\s+to\b", re.IGNORECASE), "left>right"),
    (re.compile(r"\bsuperseded\b", re.IGNORECASE), "left>right"),
    (re.compile(r"\bpreceded\b", re.IGNORECASE), "left<right"),
    (re.compile(r"\bfollowed\s+by\b", re.IGNORECASE), "left<right"),
    (re.compile(r"\bfollowed\b(?!\s+by)", re.IGNORECASE), "left>right"),
]

MONTH_TO_NUM = {name.lower(): f"{i+1:02d}" for i, name in enumerate(MONTH_NAMES.split("|"))}
LAST_DAY = {"01": "31", "02": "28", "03": "31", "04": "30", "05": "31", "06": "30",
            "07": "31", "08": "31", "09": "30", "10": "31", "11": "30", "12": "31"}


def _date_to_interval(raw: str) -> tuple[str, str]:
    """Normalize a date capture into (start, end) ISO 8601 day strings.

    Handles all v3.9.4 schema-valid date shapes:
    - YYYY-MM-DD → (date, date) point interval (day precision)
    - YYYY-MM → YYYY-MM-01 .. YYYY-MM-last (month precision, v3.9.4.1 hotfix)
    - YYYY-MM-DD..YYYY-MM-DD → parsed interval (interval precision, v3.9.4.1 hotfix)
    - 'MonthName YYYY' → first of month .. last of month (prose form)
    - YYYY → YYYY-01-01 .. YYYY-12-31 (year precision)

    v3.9.4 only handled 3 prose forms — Crossref month-precision lookups from
    bootstrap_timeline_yaml.py emit `YYYY-MM`, and effective_date_range with
    precision:interval emits `YYYY-MM-DD..YYYY-MM-DD`. Both were schema-valid
    but raised ValueError here, causing P2/P4 to silently skip the check.
    """
    raw = raw.strip()
    # Day precision: YYYY-MM-DD
    if re.fullmatch(r"\d{4}-\d{2}-\d{2}", raw):
        return raw, raw
    # Interval precision: YYYY-MM-DD..YYYY-MM-DD (v3.9.4.1 hotfix)
    m_interval = re.fullmatch(r"(\d{4}-\d{2}-\d{2})\.\.(\d{4}-\d{2}-\d{2})", raw)
    if m_interval:
        return m_interval.group(1), m_interval.group(2)
    # Month precision: YYYY-MM (v3.9.4.1 hotfix)
    m_month = re.fullmatch(r"(\d{4})-(\d{2})", raw)
    if m_month:
        yr = m_month.group(1)
        mo = m_month.group(2)
        if mo not in LAST_DAY:
            raise ValueError(f"invalid month in date: {raw!r}")
        return f"{yr}-{mo}-01", f"{yr}-{mo}-{LAST_DAY[mo]}"
    # Prose form: "MonthName YYYY"
    m = re.fullmatch(r"(" + MONTH_NAMES + r")\s+(\d{4})", raw, re.IGNORECASE)
    if m:
        mo = MONTH_TO_NUM[m.group(1).lower()]
        yr = m.group(2)
        return f"{yr}-{mo}-01", f"{yr}-{mo}-{LAST_DAY[mo]}"
    # Year precision: YYYY
    if re.fullmatch(r"(?:19|20)\d{2}", raw):
        return f"{raw}-01-01", f"{raw}-12-31"
    raise ValueError(f"unrecognized date format: {raw!r}")


def _date_diff_days(a: str, b: str) -> int:
    """Days between two YYYY-MM-DD strings (a - b)."""
    da = date.fromisoformat(a)
    db = date.fromisoformat(b)
    return (da - db).days


def _sentence_around(draft: str, char_pos: int) -> str:
    """Extract the sentence containing char_pos."""
    pre = draft[:char_pos]
    post = draft[char_pos:]
    # Find last sentence terminator before char_pos
    m_pre = re.search(r"[.!?]\s+(?=\S)", pre[::-1])
    start = char_pos - m_pre.start() if m_pre else 0
    # Find next sentence terminator at/after char_pos
    m_post = re.search(r"[.!?](\s|$)", post)
    end = char_pos + m_post.end() if m_post else len(draft)
    return draft[start:end].strip()


def _next_finding_id(findings: list[dict]) -> int:
    """Compute the next sequential TF-NNN id (1-indexed) from existing findings."""
    counter = [int(f["finding_id"].split("-")[1]) for f in findings] or [0]
    return max(counter) + 1


def _compute_line_number(draft: str, char_pos: int) -> int:
    """Return 1-indexed line number of char_pos in draft."""
    if char_pos <= 0:
        return 1
    return draft[:char_pos].count("\n") + 1


def _provenance_confidence(slug: str, citation_provenance: dict) -> str | None:
    """v3.9.4.1 hotfix: look up citation_provenance.entries[*].confidence for a ref slug.

    Returns the confidence string ('high' | 'medium' | 'low' | 'conflict') or None
    if the slug has no provenance entry (treated as 'not first-party verified').

    Per spec §3.4: when confidence is 'low' or 'conflict', P2/P4 must NOT use the
    timeline dates for arithmetic; instead emit TEMPORAL-METADATA-MISSING. v3.9.4
    audit() never threaded citation_provenance through to P2/P4, defeating this
    safety check.
    """
    if not citation_provenance:
        return None
    for entry in citation_provenance.get("entries", []):
        if entry.get("citation_key") == slug:
            return entry.get("confidence")
    return None


def _pass_1_arithmetic(draft: str, findings: list[dict]) -> None:
    """P1 Mode 1 future-as-past arithmetic.

    Pattern A: retrospective claim '(as of X) ... had already (Y)'; violation when event Y > anchor X.
    Pattern B: prospective claim 'X (will be) ... (as of Y)'; violation when event X <= anchor Y.

    If multiple violations match in the same sentence, emit the one with the largest
    |event.start - anchor.end| gap (most clearly impossible).
    """
    pos = 0
    for sentence in re.split(r"(?<=[.!?])\s+", draft):
        sentence_start = draft.find(sentence, pos)
        if sentence_start == -1:
            sentence_start = pos
        line_no = _compute_line_number(draft, sentence_start)
        pos = sentence_start + len(sentence)

        violations = []
        m_a = PATTERN_A.search(sentence)
        if m_a:
            anchor_raw = m_a.group("anchor")
            event_raw = m_a.group("event")
            try:
                anchor_start, anchor_end = _date_to_interval(anchor_raw)
                event_start, event_end = _date_to_interval(event_raw)
            except ValueError:
                pass
            else:
                if event_start > anchor_end:
                    violations.append(("A", anchor_raw, event_raw,
                                       anchor_start, anchor_end, event_start, event_end))

        m_b = PATTERN_B.search(sentence)
        if m_b:
            event_raw = m_b.group("event")
            anchor_raw = m_b.group("anchor")
            try:
                anchor_start, anchor_end = _date_to_interval(anchor_raw)
                event_start, event_end = _date_to_interval(event_raw)
            except ValueError:
                pass
            else:
                # Pattern B violation: forthcoming event already past at anchor time
                if event_start <= anchor_end:
                    violations.append(("B", anchor_raw, event_raw,
                                       anchor_start, anchor_end, event_start, event_end))

        if not violations:
            continue

        # Emit one finding per sentence — pick the largest-gap violation.
        violations.sort(key=lambda v: abs(_date_diff_days(v[5], v[4])), reverse=True)
        which, anchor_raw, event_raw, anchor_start, anchor_end, event_start, event_end = violations[0]
        rationale = (
            f"Pattern {which}: anchor '{anchor_raw}' ({anchor_start}..{anchor_end}) "
            f"{'before' if which == 'A' else 'after'} event '{event_raw}' "
            f"({event_start}..{event_end}); "
            + ("event has not yet occurred at anchor time" if which == "A"
               else "forthcoming event already past at anchor time")
        )
        findings.append({
            "finding_id": f"TF-{_next_finding_id(findings):03d}",
            "finding_kind": "TEMPORAL-ARITHMETIC-IMPOSSIBLE",
            "severity": "HIGH",
            "mode": 1,
            "block_eligible": True,
            "draft_locator": {
                "file": "phase4_composition/draft.md",
                "line": line_no,
                "sentence": sentence.strip(),
            },
            "matched_span": None,
            "bound_refs": [],
            "bound_event": None,
            "bound_dates": {
                "left": {"role": "anchor",
                         "value": f"{anchor_start}..{anchor_end}",
                         "source": "draft_capture", "ref_slug": None},
                "right": {"role": "event",
                          "value": f"{event_start}..{event_end}",
                          "source": "draft_capture", "ref_slug": None},
            },
            "rationale": rationale,
            "suggested_fix": "Restate the claim to match the anchor's true time horizon, or hedge.",
        })


def _pass_2_anachronism(draft: str, timeline: dict, citation_provenance: dict, findings: list[dict]) -> None:
    """P2 Mode 2 version-as-evidence-past anachronism.

    For each <!--ref:slug--> marker:
    1. v3.9.4.1 hotfix: Lookup slug in citation_provenance. If confidence is 'low' or
       'conflict' → emit TEMPORAL-METADATA-MISSING and skip arithmetic (spec §3.4 promise:
       first-party-unverified dates are NOT used as ground truth).
    2. Lookup slug in timeline sources. Absent → emit TEMPORAL-METADATA-MISSING.
    3. Lookup effective_date_range. Absent or start unverified/low → emit METADATA-MISSING.
    4. Find nearest event date in ±200 chars around the ref marker.
    5. Predicate (future-version): start > event.end → emit TEMPORAL-ANACHRONISTIC-CITATION.
    6. Predicate (superseded-version): end < event.start (only when end.open_ended: false
       and end.value known and confidence high/medium) → emit TEMPORAL-ANACHRONISTIC-CITATION.
    """
    sources_by_key = {s["citation_key"]: s for s in timeline.get("sources", [])}

    for m_ref in REF_MARKER_PATTERN.finditer(draft):
        slug = m_ref.group(1)
        ref_line_no = _compute_line_number(draft, m_ref.start())

        # v3.9.4.1 hotfix: provenance confidence gate (spec §3.4)
        prov_conf = _provenance_confidence(slug, citation_provenance)
        if prov_conf in {"low", "conflict"}:
            findings.append({
                "finding_id": f"TF-{_next_finding_id(findings):03d}",
                "finding_kind": "TEMPORAL-METADATA-MISSING",
                "severity": "LOW",
                "mode": None,
                "block_eligible": False,
                "draft_locator": {
                    "file": "phase4_composition/draft.md",
                    "line": ref_line_no,
                    "sentence": _sentence_around(draft, m_ref.start()),
                },
                "matched_span": None,
                "bound_refs": [{"ref_slug": slug, "timeline_entry": None}],
                "bound_event": None,
                "bound_dates": None,
                "rationale": f"<!--ref:{slug}--> citation_provenance confidence={prov_conf}; per spec §3.4 not used as arithmetic ground truth.",
                "suggested_fix": None,
            })
            continue

        source = sources_by_key.get(slug)
        if source is None:
            findings.append({
                "finding_id": f"TF-{_next_finding_id(findings):03d}",
                "finding_kind": "TEMPORAL-METADATA-MISSING",
                "severity": "LOW",
                "mode": None,
                "block_eligible": False,
                "draft_locator": {
                    "file": "phase4_composition/draft.md",
                    "line": ref_line_no,
                    "sentence": _sentence_around(draft, m_ref.start()),
                },
                "matched_span": None,
                "bound_refs": [{"ref_slug": slug, "timeline_entry": None}],
                "bound_event": None,
                "bound_dates": None,
                "rationale": f"<!--ref:{slug}--> has no entry in timeline.yaml; cannot verify temporal claims against this citation.",
                "suggested_fix": None,
            })
            continue

        edr = source.get("effective_date_range")
        if not edr:
            findings.append({
                "finding_id": f"TF-{_next_finding_id(findings):03d}",
                "finding_kind": "TEMPORAL-METADATA-MISSING",
                "severity": "LOW",
                "mode": None,
                "block_eligible": False,
                "draft_locator": {
                    "file": "phase4_composition/draft.md", "line": ref_line_no,
                    "sentence": _sentence_around(draft, m_ref.start()),
                },
                "matched_span": None,
                "bound_refs": [{"ref_slug": slug, "timeline_entry": slug}],
                "bound_event": None,
                "bound_dates": None,
                "rationale": f"{slug} has no effective_date_range; anachronism check cannot run.",
                "suggested_fix": None,
            })
            continue

        start = edr["start"]
        start_conf = start.get("provenance", {}).get("confidence")
        if start.get("value") is None or start_conf in {"unverified", "low"}:
            findings.append({
                "finding_id": f"TF-{_next_finding_id(findings):03d}",
                "finding_kind": "TEMPORAL-METADATA-MISSING",
                "severity": "LOW",
                "mode": None,
                "block_eligible": False,
                "draft_locator": {
                    "file": "phase4_composition/draft.md", "line": ref_line_no,
                    "sentence": _sentence_around(draft, m_ref.start()),
                },
                "matched_span": None,
                "bound_refs": [{"ref_slug": slug, "timeline_entry": slug}],
                "bound_event": None,
                "bound_dates": None,
                "rationale": f"{slug} effective_date_range.start absent or low/unverified confidence; cannot verify anachronism.",
                "suggested_fix": None,
            })
            continue

        # Find nearest event date in ±200 chars around ref marker
        # Exclude dates that overlap the ref marker itself (slug digits are not event dates)
        window_start = max(0, m_ref.start() - 200)
        window_end = min(len(draft), m_ref.end() + 200)
        window = draft[window_start:window_end]
        date_pattern = re.compile(DATE_REGEX, re.IGNORECASE)
        # Compute ref marker span relative to window
        ref_in_window_start = m_ref.start() - window_start
        ref_in_window_end = m_ref.end() - window_start
        event_dates = [
            d for d in date_pattern.finditer(window)
            if d.end() <= ref_in_window_start or d.start() >= ref_in_window_end
        ]
        if not event_dates:
            continue  # no event date → no finding

        # Pick closest to the ref marker position within the window
        rel_ref = m_ref.start() - window_start
        nearest = min(event_dates, key=lambda d: abs(d.start() - rel_ref))
        event_raw = nearest.group(0)
        try:
            event_start, event_end = _date_to_interval(event_raw)
            edr_start_start, _ = _date_to_interval(start["value"])
        except ValueError:
            continue

        # Future-version check (spec §3.2 P2 step 5 first clause): start > event.end
        if edr_start_start > event_end:
            findings.append({
                "finding_id": f"TF-{_next_finding_id(findings):03d}",
                "finding_kind": "TEMPORAL-ANACHRONISTIC-CITATION",
                "severity": "HIGH",
                "mode": 2,
                "block_eligible": True,
                "draft_locator": {
                    "file": "phase4_composition/draft.md", "line": ref_line_no,
                    "sentence": _sentence_around(draft, m_ref.start()),
                },
                "matched_span": None,
                "bound_refs": [{"ref_slug": slug, "timeline_entry": slug}],
                "bound_event": {"event_id": None, "date": f"{event_start}..{event_end}"},
                "bound_dates": None,
                "rationale": (
                    f"{slug} effective_date_range starts {start['value']}, after cited "
                    f"event {event_raw} ({event_start}..{event_end}). Cited version postdates the event."
                ),
                "suggested_fix": f"Cite the version of the source that was in effect during {event_raw}.",
            })

        # Superseded-version check (spec §3.2 P2 step 5 second clause)
        end = edr.get("end", {})
        end_open_ended = end.get("open_ended", False)
        end_value = end.get("value")
        end_conf = end.get("provenance", {}).get("confidence")
        if (not end_open_ended and end_value is not None
                and end_conf in {"high", "medium"}):
            try:
                _, edr_end_end = _date_to_interval(end_value)
            except ValueError:
                pass
            else:
                if edr_end_end < event_start:
                    findings.append({
                        "finding_id": f"TF-{_next_finding_id(findings):03d}",
                        "finding_kind": "TEMPORAL-ANACHRONISTIC-CITATION",
                        "severity": "HIGH",
                        "mode": 2,
                        "block_eligible": True,
                        "draft_locator": {
                            "file": "phase4_composition/draft.md", "line": ref_line_no,
                            "sentence": _sentence_around(draft, m_ref.start()),
                        },
                        "matched_span": None,
                        "bound_refs": [{"ref_slug": slug, "timeline_entry": slug}],
                        "bound_event": {"event_id": None, "date": f"{event_start}..{event_end}"},
                        "bound_dates": None,
                        "rationale": (
                            f"{slug} effective_date_range ended {end_value}, before cited "
                            f"event {event_raw} ({event_start}..{event_end}). Cited version was "
                            f"superseded before the event."
                        ),
                        "suggested_fix": f"Cite the version of the source that was in effect during {event_raw}.",
                    })


def _pass_3_comparator(draft: str, timeline: dict, findings: list[dict]) -> None:
    """P3 Mode 3 comparator unmaterialized.

    Detects prose comparator framing (Form A: 'prior edition', Form B: 'YYYY edition',
    Form C: 'edition of YYYY'). For each match, binds version_family_id via the
    nearest <!--ref:slug--> in the sentence/paragraph. If no timeline entry in that
    family has a matching year, emits TEMPORAL-COMPARATOR-UNMATERIALIZED.

    Per spec §3.2 P3: each match independently emits up to one finding per match;
    there is no per-sentence cap.
    """
    sources_by_key = {s["citation_key"]: s for s in timeline.get("sources", [])}
    sources_by_family: dict[str, list[dict]] = {}
    for s in timeline.get("sources", []):
        fam = s.get("version_family_id")
        if fam:
            sources_by_family.setdefault(fam, []).append(s)

    pos = 0
    for sentence in re.split(r"(?<=[.!?])\s+", draft):
        sentence_start = draft.find(sentence, pos)
        if sentence_start == -1:
            sentence_start = pos
        line_no = _compute_line_number(draft, sentence_start)
        pos = sentence_start + len(sentence)

        for pattern_name, pat in [("A", COMPARATOR_FORM_A), ("B", COMPARATOR_FORM_B), ("C", COMPARATOR_FORM_C)]:
            for m in pat.finditer(sentence):
                # Resolve version_family_id via ref marker in sentence
                refs_in_sentence = REF_MARKER_PATTERN.findall(sentence)
                if not refs_in_sentence:
                    continue  # binding ambiguous — emit no finding
                bound_slug = refs_in_sentence[0]
                bound_source = sources_by_key.get(bound_slug)
                if not bound_source or not bound_source.get("version_family_id"):
                    continue
                family = bound_source["version_family_id"]

                # Determine comparator year
                if pattern_name == "A":
                    year_match = re.search(
                        r"\b(?:19|20)\d{2}\b",
                        sentence[max(0, m.start() - 60):min(len(sentence), m.end() + 60)],
                    )
                    if not year_match:
                        continue
                    comparator_year = year_match.group(0)
                else:
                    comparator_year = m.group("year")

                # Check whether any source in this family has matching published_date year
                family_sources = sources_by_family.get(family, [])
                matched = False
                for s in family_sources:
                    pd = s.get("published_date")
                    if pd and pd.get("value") and comparator_year in pd["value"]:
                        matched = True
                        break

                if not matched:
                    findings.append({
                        "finding_id": f"TF-{_next_finding_id(findings):03d}",
                        "finding_kind": "TEMPORAL-COMPARATOR-UNMATERIALIZED",
                        "severity": "MEDIUM",
                        "mode": 3,
                        "block_eligible": False,
                        "draft_locator": {
                            "file": "phase4_composition/draft.md", "line": line_no,
                            "sentence": sentence.strip(),
                        },
                        "matched_span": {
                            "text": m.group(0),
                            "char_start": m.start(),
                            "char_end": m.end(),
                        },
                        "bound_refs": [{"ref_slug": bound_slug, "timeline_entry": bound_slug}],
                        "bound_event": None,
                        "bound_dates": None,
                        "rationale": (
                            f"Comparator '{m.group(0)}' (Form {pattern_name}, year={comparator_year}) "
                            f"references version family '{family}' but no timeline entry exists for that year. "
                            f"v3.9.4 reports this as claim-unsupported; v3.10 CC5 may escalate to phantom."
                        ),
                        "suggested_fix": (
                            f"Either add a timeline entry for the {comparator_year} version of {family}, "
                            f"or rewrite the prose to remove the comparator claim."
                        ),
                    })
                    # do NOT break — spec allows one finding per match


def _pass_4_causal(draft: str, timeline: dict, citation_provenance: dict, findings: list[dict]) -> None:
    """P4 Mode 4 causal inversion.

    For each causal trigger phrase, identifies left and right arguments. Each side
    may bind to either a <!--ref:slug--> marker (preferred) or a direct date capture
    in the sentence (v3.9.4.1 hotfix: spec §3.2 P4 fallback).

    v3.9.4.1 also adds citation_provenance gate (spec §3.4): if either bound slug has
    confidence:low or conflict, emit TEMPORAL-METADATA-MISSING and skip predicate.

    Looks up refs' published_date OR uses direct date capture, then verifies the
    required ordering. If violated, emits TEMPORAL-CAUSAL-INVERSION.
    """
    sources_by_key = {s["citation_key"]: s for s in timeline.get("sources", [])}
    date_pattern = re.compile(DATE_REGEX, re.IGNORECASE)

    pos = 0
    for sentence in re.split(r"(?<=[.!?])\s+", draft):
        sentence_start = draft.find(sentence, pos)
        if sentence_start == -1:
            sentence_start = pos
        line_no = _compute_line_number(draft, sentence_start)
        pos = sentence_start + len(sentence)

        for trigger_pat, required_order in CAUSAL_TRIGGERS:
            m_trig = trigger_pat.search(sentence)
            if not m_trig:
                continue

            pre = sentence[:m_trig.start()]
            post = sentence[m_trig.end():]

            # Bind left: nearest ref BEFORE trigger; else nearest direct date BEFORE
            left_refs = list(REF_MARKER_PATTERN.finditer(pre))
            left_slug = left_refs[-1].group(1) if left_refs else None
            left_date_raw = None
            if left_slug is None:
                # v3.9.4.1 fix #3: direct date fallback (spec §3.2 P4)
                left_dates = list(date_pattern.finditer(pre))
                if left_dates:
                    left_date_raw = left_dates[-1].group(0)

            # Bind right: nearest ref AFTER trigger; else nearest direct date AFTER
            right_refs = list(REF_MARKER_PATTERN.finditer(post))
            right_slug = right_refs[0].group(1) if right_refs else None
            right_date_raw = None
            if right_slug is None:
                right_dates = list(date_pattern.finditer(post))
                if right_dates:
                    right_date_raw = right_dates[0].group(0)

            # At least one side must bind
            if not (left_slug or left_date_raw) or not (right_slug or right_date_raw):
                continue

            # v3.9.4.1 hotfix: provenance gate for either slug
            for chk_slug in [left_slug, right_slug]:
                if chk_slug is None:
                    continue
                prov_conf = _provenance_confidence(chk_slug, citation_provenance)
                if prov_conf in {"low", "conflict"}:
                    findings.append({
                        "finding_id": f"TF-{_next_finding_id(findings):03d}",
                        "finding_kind": "TEMPORAL-METADATA-MISSING",
                        "severity": "LOW",
                        "mode": None,
                        "block_eligible": False,
                        "draft_locator": {
                            "file": "phase4_composition/draft.md", "line": line_no,
                            "sentence": sentence.strip(),
                        },
                        "matched_span": None,
                        "bound_refs": [{"ref_slug": chk_slug, "timeline_entry": None}],
                        "bound_event": None,
                        "bound_dates": None,
                        "rationale": f"<!--ref:{chk_slug}--> citation_provenance confidence={prov_conf}; per spec §3.4 not used as arithmetic ground truth for P4.",
                        "suggested_fix": None,
                    })
                    # Skip this trigger after emitting METADATA-MISSING for either side
                    break
            else:
                pass  # no provenance issue, continue to predicate
            # Re-check: if any prov gate fired, the for-else didn't run, we want to skip predicate
            if any(
                _provenance_confidence(s, citation_provenance) in {"low", "conflict"}
                for s in [left_slug, right_slug] if s is not None
            ):
                continue

            # Resolve left date
            if left_slug:
                left_src = sources_by_key.get(left_slug)
                if not left_src:
                    continue
                left_pd = left_src.get("published_date", {}).get("value")
                if not left_pd:
                    continue
                try:
                    left_start, _ = _date_to_interval(left_pd)
                except ValueError:
                    continue
                left_source = "timeline_ref"
            else:
                try:
                    left_start, _ = _date_to_interval(left_date_raw)
                except ValueError:
                    continue
                left_source = "draft_capture"

            # Resolve right date
            if right_slug:
                right_src = sources_by_key.get(right_slug)
                if not right_src:
                    continue
                right_pd = right_src.get("published_date", {}).get("value")
                if not right_pd:
                    continue
                try:
                    right_start, _ = _date_to_interval(right_pd)
                except ValueError:
                    continue
                right_source = "timeline_ref"
            else:
                try:
                    right_start, _ = _date_to_interval(right_date_raw)
                except ValueError:
                    continue
                right_source = "draft_capture"

            violated = (
                (required_order == "left<right" and left_start >= right_start)
                or (required_order == "left>right" and left_start <= right_start)
            )
            if not violated:
                continue

            # v3.9.4.1 hotfix: bound_refs and bound_dates.source vary by binding mode
            bound_refs_list = []
            if left_slug:
                bound_refs_list.append({"ref_slug": left_slug, "timeline_entry": left_slug})
            if right_slug:
                bound_refs_list.append({"ref_slug": right_slug, "timeline_entry": right_slug})

            findings.append({
                "finding_id": f"TF-{_next_finding_id(findings):03d}",
                "finding_kind": "TEMPORAL-CAUSAL-INVERSION",
                "severity": "MEDIUM",
                "mode": 4,
                "block_eligible": False,
                "draft_locator": {
                    "file": "phase4_composition/draft.md", "line": line_no,
                    "sentence": sentence.strip(),
                },
                "matched_span": {
                    "text": m_trig.group(0),
                    "char_start": m_trig.start(),
                    "char_end": m_trig.end(),
                },
                "bound_refs": bound_refs_list,
                "bound_event": None,
                "bound_dates": {
                    "left": {"role": "left_arg", "value": left_start,
                             "source": left_source, "ref_slug": left_slug},
                    "right": {"role": "right_arg", "value": right_start,
                              "source": right_source, "ref_slug": right_slug},
                },
                "rationale": (
                    f"Trigger '{m_trig.group(0)}' requires ordering {required_order}, "
                    f"but left.date={left_start} and right.date={right_start} violate predicate."
                ),
                "suggested_fix": "Rewrite to match the actual ordering, or revise the causal claim.",
            })
            break  # one finding per sentence


def _pass_5_deictic(draft: str, findings: list[dict]) -> None:
    """P5 Mode 5 time-bomb deictic regex lint."""
    lines = draft.splitlines(keepends=True)

    for m in DEICTIC_PATTERN.finditer(draft):
        line_no = _compute_line_number(draft, m.start())
        line_text = lines[line_no - 1].rstrip("\n") if line_no <= len(lines) else ""

        findings.append({
            "finding_id": f"TF-{_next_finding_id(findings):03d}",
            "finding_kind": "TEMPORAL-DEICTIC",
            "severity": "LOW",
            "mode": 5,
            "block_eligible": False,
            "draft_locator": {
                "file": "phase4_composition/draft.md",
                "line": line_no,
                "sentence": line_text,
            },
            "matched_span": {
                "text": m.group(0),
                "char_start": m.start(),
                "char_end": m.end(),
            },
            "bound_refs": [],
            "bound_event": None,
            "bound_dates": None,
            "rationale": f"Deictic phrase '{m.group(0)}' anchors claim to writing time; rewrite to specific date or version identifier.",
            "suggested_fix": "Replace with 'as of YYYY-MM-DD' or a specific edition/year reference.",
        })


def audit(draft: str, timeline: dict, citation_provenance: dict,
          report_reference_date: str, audit_run_id: str) -> dict:
    """Run the 5-pass verifier. Returns an aggregate matching temporal_audit_results.schema.json.

    v3.9.4.1 hotfix: citation_provenance now flows through to P2 and P4 (per spec §3.4).
    """
    findings: list[dict] = []
    _pass_1_arithmetic(draft, findings)
    _pass_2_anachronism(draft, timeline, citation_provenance, findings)
    _pass_3_comparator(draft, timeline, findings)
    _pass_4_causal(draft, timeline, citation_provenance, findings)
    _pass_5_deictic(draft, findings)
    return {
        "schema_version": "1.0",
        "audit_run_id": audit_run_id,
        "report_reference_date": report_reference_date,
        "findings": findings,
    }


def _render_markdown(result: dict) -> str:
    """Render the temporal audit results dict as a human-readable Markdown report."""
    lines = [
        "# Temporal Audit Results",
        "",
        f"- audit_run_id: `{result['audit_run_id']}`",
        f"- report_reference_date: `{result['report_reference_date']}`",
        f"- total findings: **{len(result['findings'])}**",
        "",
    ]
    if not result["findings"]:
        lines.append("_No temporal-integrity findings in this draft._")
        return "\n".join(lines) + "\n"
    for f in result["findings"]:
        lines.extend([
            f"## {f['finding_id']} — {f['finding_kind']} ({f['severity']})",
            "",
            f"- mode: {f['mode']}",
            f"- file: `{f['draft_locator']['file']}` line {f['draft_locator']['line']}",
            f"- sentence: \"{f['draft_locator']['sentence']}\"",
            f"- rationale: {f['rationale']}",
        ])
        if f.get("suggested_fix"):
            lines.append(f"- suggested fix: {f['suggested_fix']}")
        lines.append("")
    return "\n".join(lines) + "\n"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="v3.9.4 temporal integrity verifier (Phase 4 → 5 boundary)")
    parser.add_argument("--draft", type=Path, required=True)
    parser.add_argument("--timeline", type=Path, required=True)
    parser.add_argument("--citation-provenance", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--markdown-output", type=Path, default=None,
                        help="Optional path for human-readable .md report")
    parser.add_argument("--report-reference-date", required=True)
    parser.add_argument("--audit-run-id", required=True)
    args = parser.parse_args(argv)

    draft = args.draft.read_text()
    timeline = yaml.safe_load(args.timeline.read_text())
    citation_provenance = yaml.safe_load(args.citation_provenance.read_text())

    result = audit(draft, timeline, citation_provenance,
                   args.report_reference_date, args.audit_run_id)

    args.output.write_text(yaml.safe_dump(result, sort_keys=False))
    if args.markdown_output:
        args.markdown_output.write_text(_render_markdown(result))
    return 0


if __name__ == "__main__":
    sys.exit(main())
