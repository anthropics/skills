#!/usr/bin/env python3
"""change_announcement_builder.py

Produce a Kotter 8-step compliant primary internal announcement.

Kotter's 8 steps (Kotter 1996, *Leading Change*):
  1. Establish Urgency
  2. Build Guiding Coalition
  3. Form Strategic Vision
  4. Communicate the Vision
  5. Empower Broad-Based Action
  6. Generate Short-Term Wins
  7. Sustain Momentum / Consolidate Gains
  8. Anchor in Culture

Each step is explicitly labeled inline in the output so reviewers can audit
which steps are weak.

Validates magnitude vs. tone:
  - 'disruptive' magnitude rejects "exciting news" / "thrilled to" / "celebrate" framing
  - 'high' magnitude rejects "minor update" / "small change" framing
  - 'layoff'-like phrasing without a 'disruptive' magnitude flag is rejected

Industry tuning via --profile {tech-startup, scaleup, enterprise, public-company, non-profit}.

Stdlib only.
"""
from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass, asdict, field
from pathlib import Path


MAGNITUDES = {"low", "medium", "high", "disruptive"}
PROFILES = {"tech-startup", "scaleup", "enterprise", "public-company", "non-profit"}

# Per-profile tone calibration. Public-company is conservative (material-event
# awareness, no forward-looking-statement language). Startup is direct.
PROFILE_TONE: dict[str, dict[str, str]] = {
    "tech-startup": {
        "urgency": "We're moving on this now because the business signal is clear and waiting costs more than acting.",
        "coalition": "Decided by: {decided_by}. Supported by the leadership team.",
        "vision": "Where we want to be in 12 months and why this change is the path to get there.",
        "communicate": "Same content, same day, same level of detail to everyone — no inner-circle leaks.",
        "empower": "Managers have a talking-points doc; ICs have an FAQ; both are linked below.",
        "wins": "The first measurable signal we expect to see in 30 days is named below.",
        "sustain": "We will re-broadcast progress at 30 / 60 / 90 days. Same channel, same sponsor.",
        "anchor": "This change is now part of how we work. The hiring rubric and review criteria are being updated to reflect it.",
    },
    "scaleup": {
        "urgency": "The decision was made now because waiting another quarter would compound the problem we're solving.",
        "coalition": "Decided by {decided_by}, with input from the leadership team and the impacted function leads.",
        "vision": "The 12-month state this change moves us toward, and the metric that will tell us we've arrived.",
        "communicate": "All segments receive the same core message today; segment-specific FAQs follow within 24 hours.",
        "empower": "Managers have talking points; an FAQ is published; office hours are scheduled.",
        "wins": "A 30-day milestone is committed; progress is shared on the same channel.",
        "sustain": "Cadence: 30 / 60 / 90-day check-ins from the named sponsor.",
        "anchor": "Operating rhythm, hiring criteria, and review rubric will reflect the change going forward.",
    },
    "enterprise": {
        "urgency": "This decision aligns with the strategic plan approved by leadership; the timing reflects readiness, not crisis.",
        "coalition": "Sponsored by {decided_by}. The change has been reviewed by the relevant business-unit leadership and applicable functions (HR, Legal, Finance).",
        "vision": "Strategic objective and the operating outcome this change advances.",
        "communicate": "Cascade plan: leadership > directors > managers > ICs, with consistent core messaging at each level.",
        "empower": "Manager toolkits, FAQ, town-hall schedule, and the change-network contacts are published on the intranet.",
        "wins": "First measurable success criterion is named for the 30-day review.",
        "sustain": "Standing change-management cadence at 30 / 60 / 90 days, reporting against the success criteria.",
        "anchor": "Operating procedures, role descriptions, and performance criteria will be updated to reflect the change.",
    },
    "public-company": {
        "urgency": "This change supports the strategic priorities communicated to shareholders; timing reflects internal readiness.",
        "coalition": "Sponsored by {decided_by}. Reviewed with the relevant leadership and functional partners.",
        "vision": "How this advances the publicly stated strategic priorities.",
        "communicate": "Internal communication is coordinated with Investor Relations; please direct external inquiries to IR.",
        "empower": "Manager toolkits and FAQ are published; office hours are scheduled. Material non-public information should be handled per the insider-trading policy.",
        "wins": "Internal milestone for the 30-day review is named; external disclosure will follow standard reporting cadence.",
        "sustain": "Internal cadence at 30 / 60 / 90 days; external reporting through normal disclosure channels.",
        "anchor": "Operating procedures will be updated through the standard policy-update workflow.",
    },
    "non-profit": {
        "urgency": "This change reflects our commitment to the mission and the constituents we serve.",
        "coalition": "Decided by {decided_by}, in consultation with leadership and (where applicable) the board.",
        "vision": "How this change advances the mission and serves our constituents better.",
        "communicate": "Staff hear from leadership today; volunteers and constituents are briefed through the channels they normally hear from.",
        "empower": "Managers and program leads have talking points; an FAQ is published; office hours are open.",
        "wins": "First mission-aligned milestone is named for the 30-day review.",
        "sustain": "Cadence at 30 / 60 / 90 days with a focus on mission outcomes.",
        "anchor": "Programs, training, and onboarding materials will be updated to reflect the change.",
    },
}

# Magnitude/tone anti-pattern keywords (case-insensitive substring match).
DISRUPTIVE_BANNED = [
    "exciting news", "thrilled to", "celebrate", "win for the team",
    "great opportunity", "happy to share",
]
HIGH_BANNED = [
    "minor update", "small change", "tiny tweak", "no big deal", "minor restructuring",
]
LAYOFF_KEYWORDS = ["layoff", "reduction in force", "rif", "let go", "eliminating", "redundanc"]


@dataclass
class Announcement:
    change_summary: str
    magnitude: str
    profile: str
    steps: list[dict] = field(default_factory=list)
    validations: list[str] = field(default_factory=list)
    blocked: bool = False


def _lower(s: str) -> str:
    return (s or "").lower()


def validate_tone(raw: dict, magnitude: str) -> list[str]:
    issues: list[str] = []
    combined = " ".join([
        _lower(raw.get("change_summary", "")),
        _lower(raw.get("why_this_change", "")),
        _lower(raw.get("what_changes", "")),
        _lower(raw.get("what_stays_the_same", "")),
    ])

    if magnitude == "disruptive":
        for kw in DISRUPTIVE_BANNED:
            if kw in combined:
                issues.append(
                    f"REJECTED: 'disruptive' magnitude with celebratory framing "
                    f"('{kw}'). Anti-pattern (Sucher & Gupta, MIT Sloan)."
                )
    if magnitude == "high":
        for kw in HIGH_BANNED:
            if kw in combined:
                issues.append(
                    f"REJECTED: 'high' magnitude with minimizing framing "
                    f"('{kw}'). Anti-pattern (Better.com / Vishal-Garg case)."
                )
    # Layoff-keyword vs magnitude check
    layoff_present = any(kw in combined for kw in LAYOFF_KEYWORDS)
    if layoff_present and magnitude != "disruptive":
        issues.append(
            "REJECTED: layoff/RIF language present but magnitude is not "
            "'disruptive'. Re-classify magnitude before continuing."
        )
    # Passive-voice accountability check
    if "decisions have been made" in combined or "the decision has been made" in combined:
        issues.append(
            "WARN: passive-voice accountability detected ('decisions have been "
            "made'). Name the decision-maker (Lencioni: Vulnerability-Based Trust)."
        )
    return issues


def build_announcement(raw: dict, profile: str) -> Announcement:
    if profile not in PROFILES:
        raise SystemExit(f"--profile must be one of {sorted(PROFILES)}; got '{profile}'")
    mag = raw.get("change_magnitude", "")
    if mag not in MAGNITUDES:
        raise SystemExit(
            f"change_magnitude must be one of {sorted(MAGNITUDES)}; got '{mag}'"
        )
    decided_by = raw.get("who_decided") or "the leadership team"
    tone = PROFILE_TONE[profile]
    validations = validate_tone(raw, mag)
    blocked = any(v.startswith("REJECTED") for v in validations)

    summary = raw.get("change_summary", "[no summary provided]")
    why = raw.get("why_this_change", "[no reason provided]")
    what_changes = raw.get("what_changes", "[change scope not specified]")
    what_stays = raw.get("what_stays_the_same", "[stability scope not specified]")
    eff = raw.get("effective_date", "[date TBD]")
    next_steps = raw.get("next_steps", "[next steps TBD]")
    qa_seed = list(raw.get("q_and_a_seed") or [])

    steps = [
        {
            "step": 1,
            "label": "Establish Urgency",
            "body": (
                f"{tone['urgency']} The change: {summary}. The reason now: {why}. "
                f"Effective: {eff}. Magnitude: {mag}."
            ),
        },
        {
            "step": 2,
            "label": "Build Guiding Coalition",
            "body": tone["coalition"].format(decided_by=decided_by),
        },
        {
            "step": 3,
            "label": "Form Strategic Vision",
            "body": (
                f"{tone['vision']} What changes: {what_changes}. What stays the "
                f"same: {what_stays}."
            ),
        },
        {
            "step": 4,
            "label": "Communicate the Vision",
            "body": tone["communicate"],
        },
        {
            "step": 5,
            "label": "Empower Broad-Based Action",
            "body": (
                f"{tone['empower']} Next steps: {next_steps}."
            ),
        },
        {
            "step": 6,
            "label": "Generate Short-Term Wins",
            "body": tone["wins"],
        },
        {
            "step": 7,
            "label": "Sustain Momentum",
            "body": tone["sustain"],
        },
        {
            "step": 8,
            "label": "Anchor in Culture",
            "body": tone["anchor"],
        },
    ]

    # Append seeded Q&A as appendix to Step 5 (empower-with-info).
    if qa_seed:
        qa_block = "\n\nSeed Q&A appendix (Empower stage):\n"
        for i, item in enumerate(qa_seed, 1):
            q = item.get("q", "") if isinstance(item, dict) else str(item)
            a = item.get("a", "") if isinstance(item, dict) else ""
            qa_block += f"  Q{i}: {q}\n  A{i}: {a}\n"
        steps[4]["body"] += qa_block

    return Announcement(
        change_summary=summary,
        magnitude=mag,
        profile=profile,
        steps=steps,
        validations=validations,
        blocked=blocked,
    )


def render_markdown(a: Announcement) -> str:
    lines: list[str] = []
    lines.append(f"# Change Announcement (Kotter 8-step)")
    lines.append("")
    lines.append(f"**Change:** {a.change_summary}  ")
    lines.append(f"**Magnitude:** {a.magnitude}  ")
    lines.append(f"**Profile (tone):** {a.profile}  ")
    if a.blocked:
        lines.append("")
        lines.append("> **BLOCKED — magnitude/tone anti-pattern detected. Fix before publishing.**")
    lines.append("")
    for s in a.steps:
        lines.append(f"## Step {s['step']} — {s['label']}")
        lines.append("")
        lines.append(s["body"])
        lines.append("")
    if a.validations:
        lines.append("## Validation results")
        lines.append("")
        for v in a.validations:
            lines.append(f"- {v}")
        lines.append("")
    return "\n".join(lines)


def sample_input() -> dict:
    return {
        "change_summary": "Migrating internal documentation from Confluence to Notion",
        "why_this_change": "Confluence search reliability and the cost of duplicate licenses with Notion (already used by product team) make consolidation the right move now",
        "what_changes": "All net-new documentation is authored in Notion starting June 1; existing Confluence pages are read-only after Aug 1 and migrated by Oct 1",
        "what_stays_the_same": "Permissions model, document ownership, retention policy",
        "effective_date": "2026-06-01",
        "who_decided": "Head of IT and the engineering leadership team",
        "change_magnitude": "medium",
        "q_and_a_seed": [
            {"q": "Will my existing Confluence pages move automatically?",
             "a": "Yes. The IT team is handling migration through Oct 1. You will be notified when your space is migrated."},
            {"q": "Do I need to learn a new tool?",
             "a": "Notion fundamentals are covered in the office-hour series starting June 5. Self-serve docs are linked below."},
        ],
        "next_steps": "Office hours start June 5; manager talking points are in the intranet under People-Ops > Change > Notion-rollout.",
    }


def main() -> int:
    p = argparse.ArgumentParser(
        description="Build a Kotter 8-step compliant internal change announcement."
    )
    p.add_argument("--input", type=Path, help="Path to announcement-input JSON.")
    p.add_argument(
        "--profile",
        choices=sorted(PROFILES),
        default="scaleup",
        help="Industry profile for tone calibration (default: scaleup).",
    )
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

    ann = build_announcement(raw, args.profile)
    if args.output == "json":
        print(json.dumps(asdict(ann), indent=2))
    else:
        print(render_markdown(ann))
    return 0


if __name__ == "__main__":
    sys.exit(main())
