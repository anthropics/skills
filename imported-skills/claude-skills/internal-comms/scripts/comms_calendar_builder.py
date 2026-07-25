#!/usr/bin/env python3
"""comms_calendar_builder.py

Build a 7-touchpoint sequencing calendar for an internal change event.

Prosci's documented floor for behavioral change adoption is 5–7 touchpoints
across multiple channels (Prosci Best Practices in Change Management, 11th ed.).
This tool produces a sequenced calendar with timing (T-N / T+N), channel,
owner, ADKAR stage, and key message per touchpoint.

Surfaces gaps and channel mismatches as anti-pattern warnings:
  - <5 touchpoints planned for disruptive change
  - Slack-only sequencing for a layoff (synchronous channel required)
  - No manager_cascade touchpoint before the announcement
  - No follow-up touchpoint after the announcement

Stdlib only.
"""
from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass, asdict, field
from datetime import date, datetime, timedelta
from pathlib import Path


MAGNITUDES = {"low", "medium", "high", "disruptive"}
KNOWN_CHANNELS = {
    "email", "slack", "allhands", "manager_cascade",
    "town_hall", "intranet",
}
SYNCHRONOUS_CHANNELS = {"allhands", "town_hall"}


@dataclass
class CalendarTouchpoint:
    seq: int
    timing: str           # T-3, T+0, T+7 etc.
    offset_days: int      # negative = before, positive = after
    channel: str
    owner: str
    adkar_stage: str
    key_message: str
    iso_date: str         # ISO date if effective_date is provided


@dataclass
class CalendarReport:
    change_name: str
    magnitude: str
    effective_date: str
    audience_size: int
    channels_available: list[str]
    working_days_available: int
    touchpoints: list[CalendarTouchpoint] = field(default_factory=list)
    warnings: list[str] = field(default_factory=list)


def _pick_channel(channels: list[str], preferred: list[str], fallback: str) -> str:
    for p in preferred:
        if p in channels:
            return p
    return fallback if fallback in channels else (channels[0] if channels else "email")


def _compute_iso(eff: str, offset_days: int) -> str:
    if not eff:
        return ""
    try:
        d = datetime.fromisoformat(eff).date()
    except ValueError:
        return ""
    return (d + timedelta(days=offset_days)).isoformat()


def build_calendar(raw: dict) -> CalendarReport:
    event = raw.get("change_event") or {}
    name = event.get("name", "Untitled Change")
    mag = event.get("magnitude", "medium")
    if mag not in MAGNITUDES:
        raise SystemExit(
            f"change_event.magnitude must be one of {sorted(MAGNITUDES)}; got '{mag}'"
        )
    eff = str(event.get("effective_date", "")).strip()
    audience_size = int(event.get("audience_size", 0) or 0)
    channels = list(raw.get("channels_available") or [])
    if not channels:
        raise SystemExit("channels_available must be a non-empty list")
    working_days = int(raw.get("working_days_available", 14) or 14)

    # Validate channels
    unknown = [c for c in channels if c not in KNOWN_CHANNELS]
    warnings: list[str] = []
    if unknown:
        warnings.append(
            f"Unknown channels (will be ignored for sequencing logic): {unknown}. "
            f"Known: {sorted(KNOWN_CHANNELS)}"
        )

    # Touchpoint plan — 7 entries, keyed to T-N / T+N
    # Sequence (Prosci 5–7 floor; we ship 7):
    #   1) T-3  manager_cascade (Awareness)
    #   2) T-1  email           (Awareness — broad heads-up)
    #   3) T+0  allhands/town_hall (Knowledge — primary announcement)
    #   4) T+0  intranet/email  (Knowledge — FAQ publication)
    #   5) T+1  slack           (Desire — Q&A thread, sponsor reads replies)
    #   6) T+7  email           (Ability — training / how-to / office hours)
    #   7) T+14 allhands/email  (Reinforcement — 2-week check-in)
    plan = [
        {"seq": 1, "offset": -3, "preferred": ["manager_cascade", "email"],
         "fallback": "email", "owner": "manager_cascade_owner",
         "adkar": "Awareness", "msg": "Manager pre-brief: talking points + timing"},
        {"seq": 2, "offset": -1, "preferred": ["email"],
         "fallback": "email", "owner": "internal_comms_lead",
         "adkar": "Awareness", "msg": "Save-the-date heads-up to all-hands"},
        {"seq": 3, "offset": 0, "preferred": ["town_hall", "allhands"],
         "fallback": "allhands", "owner": "sponsor_exec",
         "adkar": "Knowledge", "msg": "Primary announcement, sponsor present"},
        {"seq": 4, "offset": 0, "preferred": ["intranet", "email"],
         "fallback": "email", "owner": "internal_comms_lead",
         "adkar": "Knowledge", "msg": "FAQ + supporting docs published"},
        {"seq": 5, "offset": 1, "preferred": ["slack", "intranet"],
         "fallback": "slack", "owner": "sponsor_exec",
         "adkar": "Desire", "msg": "Q&A thread, sponsor responding live"},
        {"seq": 6, "offset": 7, "preferred": ["email", "intranet"],
         "fallback": "email", "owner": "enablement_lead",
         "adkar": "Ability", "msg": "Training / office-hours / how-to"},
        {"seq": 7, "offset": 14, "preferred": ["allhands", "email"],
         "fallback": "email", "owner": "sponsor_exec",
         "adkar": "Reinforcement", "msg": "2-week check-in: progress + still-open items"},
    ]

    touchpoints: list[CalendarTouchpoint] = []
    for item in plan:
        chan = _pick_channel(channels, item["preferred"], item["fallback"])
        timing = f"T{item['offset']:+d}" if item["offset"] != 0 else "T+0"
        touchpoints.append(CalendarTouchpoint(
            seq=item["seq"],
            timing=timing,
            offset_days=item["offset"],
            channel=chan,
            owner=item["owner"],
            adkar_stage=item["adkar"],
            key_message=item["msg"],
            iso_date=_compute_iso(eff, item["offset"]),
        ))

    # Anti-pattern checks
    if len(touchpoints) < 5:
        warnings.append(
            f"ANTI-PATTERN: only {len(touchpoints)} touchpoints planned. "
            "Prosci floor for behavioral change is 5–7."
        )
    if mag == "disruptive" and not any(t.channel in SYNCHRONOUS_CHANNELS for t in touchpoints):
        warnings.append(
            "ANTI-PATTERN: disruptive change with no synchronous channel "
            "(town_hall / allhands). Required."
        )
    # Layoff inference: name contains layoff/RIF keyword
    name_l = name.lower()
    layoff_event = any(kw in name_l for kw in ["layoff", "rif", "reduction in force", "redundanc"])
    if layoff_event:
        if all(t.channel == "slack" for t in touchpoints):
            warnings.append(
                "ANTI-PATTERN: Slack-only sequencing for a layoff event. "
                "Synchronous channel (town_hall + manager_cascade 1:1) required."
            )
        if not any(t.channel == "manager_cascade" for t in touchpoints):
            warnings.append(
                "ANTI-PATTERN: layoff event with no manager_cascade touchpoint. "
                "Affected employees must hear from their direct manager first."
            )
    # Pre-comm check
    if not any(t.offset_days < 0 and t.channel == "manager_cascade" for t in touchpoints):
        warnings.append(
            "WARN: no manager_cascade touchpoint scheduled before announcement. "
            "Managers should hear 24–48h ahead so the cascade does not break "
            "on first contact with reports."
        )
    # Follow-up check
    if not any(t.offset_days > 7 for t in touchpoints):
        warnings.append(
            "WARN: no follow-up touchpoint scheduled >7 days after announcement. "
            "ADKAR Reinforcement stage is unstaffed."
        )
    # Working-days feasibility
    needed_days = 14 + 3  # T-3 to T+14
    if working_days < needed_days:
        warnings.append(
            f"WARN: working_days_available={working_days} is less than the "
            f"{needed_days}-day span needed (T-3 through T+14). Compress at risk."
        )
    # Audience-size sanity for channels
    if audience_size > 500 and "allhands" not in channels and "town_hall" not in channels:
        warnings.append(
            f"WARN: audience_size={audience_size} but no all-hands/town-hall channel. "
            "Large audiences require a synchronous channel for trust events."
        )

    return CalendarReport(
        change_name=name,
        magnitude=mag,
        effective_date=eff,
        audience_size=audience_size,
        channels_available=channels,
        working_days_available=working_days,
        touchpoints=touchpoints,
        warnings=warnings,
    )


def render_markdown(r: CalendarReport) -> str:
    lines: list[str] = []
    lines.append(f"# Comms Calendar — {r.change_name}")
    lines.append("")
    lines.append(f"**Magnitude:** {r.magnitude}  ")
    lines.append(f"**Effective date:** {r.effective_date or '_(not provided)_'}  ")
    lines.append(f"**Audience size:** {r.audience_size}  ")
    lines.append(f"**Channels available:** {', '.join(r.channels_available)}  ")
    lines.append(f"**Working days available:** {r.working_days_available}  ")
    lines.append("")
    lines.append("## Touchpoint sequence (7 entries)")
    lines.append("")
    lines.append("| # | Timing | ISO date | Channel | Owner | ADKAR | Key message |")
    lines.append("|---|--------|----------|---------|-------|-------|-------------|")
    for t in r.touchpoints:
        lines.append(
            f"| {t.seq} | {t.timing} | {t.iso_date or '—'} | {t.channel} | "
            f"{t.owner} | {t.adkar_stage} | {t.key_message} |"
        )
    lines.append("")
    if r.warnings:
        lines.append("## Warnings / anti-patterns")
        lines.append("")
        for w in r.warnings:
            lines.append(f"- {w}")
        lines.append("")
    return "\n".join(lines)


def sample_input() -> dict:
    return {
        "change_event": {
            "name": "Reorganization: merging Platform and Infrastructure into one group",
            "magnitude": "high",
            "effective_date": "2026-06-15",
            "audience_size": 320,
        },
        "channels_available": [
            "email", "slack", "allhands", "manager_cascade", "town_hall", "intranet",
        ],
        "working_days_available": 21,
    }


def main() -> int:
    p = argparse.ArgumentParser(
        description="Build a 7-touchpoint internal-comms sequencing calendar."
    )
    p.add_argument("--input", type=Path, help="Path to calendar-input JSON.")
    p.add_argument(
        "--output", choices=["markdown", "json"], default="markdown",
        help="Output format (default: markdown).",
    )
    p.add_argument("--sample", action="store_true", help="Use built-in sample and exit.")
    args = p.parse_args()

    if args.sample:
        raw = sample_input()
    else:
        if not args.input:
            p.error("--input is required unless --sample is given")
        if not args.input.exists():
            p.error(f"input file not found: {args.input}")
        with args.input.open("r", encoding="utf-8") as f:
            raw = json.load(f)

    rep = build_calendar(raw)
    if args.output == "json":
        print(json.dumps(asdict(rep), indent=2))
    else:
        print(render_markdown(rep))
    return 0


if __name__ == "__main__":
    sys.exit(main())
