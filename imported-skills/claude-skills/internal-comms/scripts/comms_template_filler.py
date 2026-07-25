#!/usr/bin/env python3
"""comms_template_filler.py

Fill a 4-artifact internal-comms package — pre-comm, primary announcement, FAQ,
follow-up — for a specific internal change event. Each touchpoint is explicitly
tagged with the ADKAR stage (Awareness / Desire / Knowledge / Ability /
Reinforcement) it serves, per audience segment.

ADKAR (Prosci, Hiatt 2006) anchors each artifact:
  pre-comm        -> Awareness + Desire (manager-first cascade)
  announcement    -> Knowledge + Desire reinforcement
  FAQ             -> Knowledge + Ability
  follow-up       -> Ability + Reinforcement

Stdlib only.
"""
from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass, field, asdict
from pathlib import Path


CHANGE_TYPES = {
    "reorg",
    "tool_rollout",
    "policy_change",
    "leadership_change",
    "layoff",
    "acquisition",
    "product_launch_internal",
    "benefit_change",
}

MAGNITUDES = {"low", "medium", "high", "disruptive"}

ADKAR_STAGES = ["Awareness", "Desire", "Knowledge", "Ability", "Reinforcement"]


# Per change-type, default ADKAR emphasis order (the stage most at risk first).
ADKAR_EMPHASIS: dict[str, list[str]] = {
    "reorg":                   ["Desire", "Knowledge", "Ability", "Reinforcement", "Awareness"],
    "tool_rollout":            ["Knowledge", "Ability", "Desire", "Reinforcement", "Awareness"],
    "policy_change":           ["Awareness", "Knowledge", "Ability", "Reinforcement", "Desire"],
    "leadership_change":       ["Awareness", "Desire", "Reinforcement", "Knowledge", "Ability"],
    "layoff":                  ["Awareness", "Desire", "Reinforcement", "Knowledge", "Ability"],
    "acquisition":             ["Awareness", "Desire", "Knowledge", "Reinforcement", "Ability"],
    "product_launch_internal": ["Knowledge", "Ability", "Desire", "Awareness", "Reinforcement"],
    "benefit_change":          ["Awareness", "Knowledge", "Ability", "Desire", "Reinforcement"],
}


@dataclass
class Touchpoint:
    artifact: str           # pre-comm | announcement | faq | follow-up
    audience_segment: str
    adkar_stage: str
    channel: str
    timing: str             # e.g., T-2, T+0, T+7
    subject: str
    body: str


@dataclass
class CommsPackage:
    change_type: str
    magnitude: str
    effective_date: str
    audience_segments: list[str]
    channels: list[str]
    touchpoints: list[Touchpoint] = field(default_factory=list)
    notes: list[str] = field(default_factory=list)


def validate_input(raw: dict) -> tuple[str, str, str, list[str], list[str]]:
    ct = raw.get("change_type", "")
    if ct not in CHANGE_TYPES:
        raise SystemExit(
            f"change_type must be one of {sorted(CHANGE_TYPES)}; got '{ct}'"
        )
    mag = raw.get("change_magnitude", "")
    if mag not in MAGNITUDES:
        raise SystemExit(
            f"change_magnitude must be one of {sorted(MAGNITUDES)}; got '{mag}'"
        )
    eff = str(raw.get("effective_date", "")).strip()
    if not eff:
        raise SystemExit("effective_date is required (ISO 8601 string)")
    segs = list(raw.get("audience_segments") or [])
    if not segs:
        raise SystemExit("audience_segments must be a non-empty list")
    chans = list(raw.get("channels") or [])
    if not chans:
        raise SystemExit("channels must be a non-empty list")
    return ct, mag, eff, segs, chans


def _pick_channel(channels: list[str], preferred: list[str]) -> str:
    for p in preferred:
        if p in channels:
            return p
    return channels[0]


def _segment_voice(segment: str) -> str:
    s = segment.lower()
    if "manager" in s or "lead" in s:
        return "manager"
    if "exec" in s or "leadership" in s:
        return "exec"
    if "affected" in s and "un" not in s:
        return "affected"
    if "unaffected" in s or "rest" in s:
        return "unaffected"
    return "ic"


def _precomm_body(ct: str, mag: str, eff: str, segment: str) -> str:
    voice = _segment_voice(segment)
    if voice == "manager":
        return (
            f"You are receiving this pre-brief because the {ct.replace('_', ' ')} "
            f"will be announced company-wide on {eff} (magnitude: {mag}). "
            "Please review the talking points below and be ready to answer "
            "questions from your direct reports starting at the announcement time. "
            "Do not share this content before the announcement window opens. "
            "If a report asks a question you cannot answer, say 'I will follow up "
            "by end of day' rather than speculating."
        )
    if voice == "exec":
        return (
            f"This is a sponsor brief for the {ct.replace('_', ' ')} on {eff}. "
            "You are named as the accountable executive in the announcement and "
            "the town hall. Please confirm both within 24 hours. Decline now if "
            "you cannot be visibly present — invisible sponsorship is a Kotter "
            "step-1 failure."
        )
    return (
        f"Heads-up: there is a {ct.replace('_', ' ')} announcement scheduled for "
        f"{eff}. More information is being prepared. No action is required from "
        "you yet."
    )


def _announcement_body(ct: str, mag: str, eff: str, segment: str) -> str:
    return (
        f"This message announces the {ct.replace('_', ' ')}, effective {eff}. "
        f"Magnitude: {mag}. The reasoning, the scope, the people affected, and "
        "the immediate next steps are below. Each section is written to answer "
        "a specific employee question. See the FAQ for the questions we have "
        "anticipated; reply to this thread (or join the town hall) to ask the "
        "ones we have not."
    )


def _faq_body(ct: str, mag: str, segment: str) -> str:
    seed = [
        ("Will my compensation change?",
         "State the answer plainly. If unchanged: 'No.' If changing: name the "
         "effective date and the comp-review channel."),
        ("Will my reporting line change?",
         "Name the new manager (or confirm it is unchanged). If TBD, name the "
         "date by which it will be confirmed."),
        ("Will my role or scope change?",
         "Describe the delta concretely. Avoid 'evolving' / 'transforming'."),
        ("Is this a precursor to layoffs?",
         "Answer directly. Hedged answers here are read as 'yes'."),
        ("When does this take effect?",
         "Single date; if phased, list the phase dates."),
        ("Why now?",
         "One sentence on the trigger; reference the business signal, not the "
         "internal politics."),
        ("Who decided this and who can I ask follow-up questions?",
         "Name a single accountable executive and a single channel for follow-up."),
    ]
    lines = [f"FAQ for {segment} (change: {ct.replace('_', ' ')}, magnitude: {mag}):", ""]
    for q, a in seed:
        lines.append(f"Q: {q}")
        lines.append(f"A: {a}")
        lines.append("")
    return "\n".join(lines).rstrip()


def _followup_body(ct: str, eff: str, segment: str) -> str:
    return (
        f"Two weeks after {eff}, this follow-up reinforces the {ct.replace('_', ' ')}. "
        "Three signals are reported: (1) measurable outcome the change was meant "
        "to produce, (2) one specific story of an employee adapting successfully "
        "(Ability stage), and (3) what is still open and the date it will close "
        "(Reinforcement stage). Reply with feedback; the sponsor reads every reply."
    )


def build(raw: dict) -> CommsPackage:
    ct, mag, eff, segs, chans = validate_input(raw)
    pkg = CommsPackage(
        change_type=ct,
        magnitude=mag,
        effective_date=eff,
        audience_segments=segs,
        channels=chans,
    )

    emphasis = ADKAR_EMPHASIS.get(ct, ADKAR_STAGES)

    for seg in segs:
        voice = _segment_voice(seg)
        # 1. Pre-comm (T-2): Awareness + Desire (manager-cascade priority)
        pkg.touchpoints.append(Touchpoint(
            artifact="pre-comm",
            audience_segment=seg,
            adkar_stage="Awareness" if voice != "manager" else "Desire",
            channel=_pick_channel(chans, ["manager_cascade", "email", "slack"]),
            timing="T-2",
            subject=f"[Pre-brief] {ct.replace('_', ' ').title()} announcement on {eff}",
            body=_precomm_body(ct, mag, eff, seg),
        ))
        # 2. Announcement (T+0): Knowledge primary; ADKAR emphasis stage as secondary
        pkg.touchpoints.append(Touchpoint(
            artifact="announcement",
            audience_segment=seg,
            adkar_stage="Knowledge",
            channel=_pick_channel(chans, ["allhands", "town_hall", "email"]),
            timing="T+0",
            subject=f"{ct.replace('_', ' ').title()}: what's changing and why",
            body=_announcement_body(ct, mag, eff, seg),
        ))
        # 3. FAQ (T+0 immediately after announcement): Knowledge + Ability
        pkg.touchpoints.append(Touchpoint(
            artifact="faq",
            audience_segment=seg,
            adkar_stage="Ability",
            channel=_pick_channel(chans, ["intranet", "email", "slack"]),
            timing="T+0",
            subject=f"FAQ — {ct.replace('_', ' ').title()}",
            body=_faq_body(ct, mag, seg),
        ))
        # 4. Follow-up (T+14): Reinforcement
        pkg.touchpoints.append(Touchpoint(
            artifact="follow-up",
            audience_segment=seg,
            adkar_stage="Reinforcement",
            channel=_pick_channel(chans, ["email", "allhands", "slack"]),
            timing="T+14",
            subject=f"Two-week check-in: {ct.replace('_', ' ')}",
            body=_followup_body(ct, eff, seg),
        ))

    # Notes / anti-pattern guards
    if mag == "disruptive" and "town_hall" not in chans and "allhands" not in chans:
        pkg.notes.append(
            "ANTI-PATTERN: disruptive change without a synchronous channel "
            "(town_hall / allhands). Add one before publication."
        )
    if ct == "layoff" and "manager_cascade" not in chans:
        pkg.notes.append(
            "ANTI-PATTERN: layoff comms without manager_cascade channel. "
            "Direct-manager 1:1 is mandatory for affected employees."
        )
    if len(pkg.touchpoints) < 5:
        pkg.notes.append(
            "Prosci floor for behavioral change is 5–7 touchpoints; current "
            f"plan has {len(pkg.touchpoints)}. Add more segments or channels."
        )
    pkg.notes.append(
        f"ADKAR emphasis order for change_type='{ct}': "
        + " > ".join(emphasis)
    )
    return pkg


def render_markdown(pkg: CommsPackage) -> str:
    lines: list[str] = []
    lines.append(f"# Internal Comms Package — {pkg.change_type.replace('_', ' ').title()}")
    lines.append("")
    lines.append(f"**Magnitude:** {pkg.magnitude}  ")
    lines.append(f"**Effective date:** {pkg.effective_date}  ")
    lines.append(f"**Audience segments:** {', '.join(pkg.audience_segments)}  ")
    lines.append(f"**Channels available:** {', '.join(pkg.channels)}  ")
    lines.append("")
    for tp in pkg.touchpoints:
        lines.append(f"## [{tp.artifact}] {tp.audience_segment} — ADKAR: {tp.adkar_stage}")
        lines.append("")
        lines.append(f"- **Timing:** {tp.timing}  ")
        lines.append(f"- **Channel:** {tp.channel}  ")
        lines.append(f"- **Subject:** {tp.subject}")
        lines.append("")
        lines.append(tp.body)
        lines.append("")
    if pkg.notes:
        lines.append("## Notes")
        lines.append("")
        for n in pkg.notes:
            lines.append(f"- {n}")
        lines.append("")
    return "\n".join(lines)


def sample_input() -> dict:
    return {
        "change_type": "tool_rollout",
        "audience_segments": ["engineering managers", "engineering ICs", "rest of company"],
        "change_magnitude": "medium",
        "effective_date": "2026-06-01",
        "channels": ["email", "slack", "allhands", "manager_cascade", "intranet"],
    }


def main() -> int:
    p = argparse.ArgumentParser(
        description="Fill a 4-artifact internal-comms package with ADKAR-tagged touchpoints."
    )
    p.add_argument("--input", type=Path, help="Path to comms-brief JSON.")
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

    pkg = build(raw)
    if args.output == "json":
        print(json.dumps(asdict(pkg), indent=2))
    else:
        print(render_markdown(pkg))
    return 0


if __name__ == "__main__":
    sys.exit(main())
