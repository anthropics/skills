#!/usr/bin/env python3
"""process_documenter.py

Read a JSON description of a business process (one entry per stage) and emit:
  - a text-based BPMN-style swim-lane diagram in Markdown, OR
  - a normalized JSON artifact for downstream tools.

Stdlib only. Use `--sample` to print a 6-stage procurement-intake example to
stdout.

Input schema (JSON):
{
  "process_name": "Procurement Intake",
  "wip": 12,                       # optional, integer; used by cycle_time_analyzer
  "stages": [
    {
      "name": "Requestor submits PO request",
      "owner": "Requestor",
      "type": "value-add",         # one of: value-add | wait | rework
      "duration_minutes_p50": 15,
      "duration_minutes_p90": 30
    },
    ...
  ]
}
"""
from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass, asdict
from enum import Enum
from pathlib import Path


VALID_TYPES = {"value-add", "wait", "rework"}


class StageType(str, Enum):
    VALUE_ADD = "value-add"
    WAIT = "wait"
    REWORK = "rework"


@dataclass
class Stage:
    name: str
    owner: str
    type: str
    duration_minutes_p50: float
    duration_minutes_p90: float

    def validate(self, idx: int) -> list[str]:
        errs: list[str] = []
        if not self.name:
            errs.append(f"stage[{idx}]: missing 'name'")
        if not self.owner:
            errs.append(f"stage[{idx}]: missing 'owner'")
        if self.type not in VALID_TYPES:
            errs.append(
                f"stage[{idx}] ('{self.name}'): invalid type '{self.type}' "
                f"(expected one of {sorted(VALID_TYPES)})"
            )
        if self.duration_minutes_p50 < 0:
            errs.append(f"stage[{idx}] ('{self.name}'): p50 must be >= 0")
        if self.duration_minutes_p90 < self.duration_minutes_p50:
            errs.append(
                f"stage[{idx}] ('{self.name}'): p90 ({self.duration_minutes_p90}) "
                f"< p50 ({self.duration_minutes_p50})"
            )
        return errs


def load_process(path: Path) -> dict:
    with path.open("r", encoding="utf-8") as f:
        return json.load(f)


def normalize(raw: dict) -> dict:
    """Validate + return a normalized dict. Raises ValueError on bad input."""
    if "stages" not in raw or not isinstance(raw["stages"], list):
        raise ValueError("input must include a non-empty 'stages' list")

    stages: list[Stage] = []
    errors: list[str] = []
    for idx, s in enumerate(raw["stages"]):
        try:
            stage = Stage(
                name=s.get("name", ""),
                owner=s.get("owner", ""),
                type=s.get("type", ""),
                duration_minutes_p50=float(s.get("duration_minutes_p50", 0)),
                duration_minutes_p90=float(s.get("duration_minutes_p90", 0)),
            )
        except (TypeError, ValueError) as e:
            errors.append(f"stage[{idx}]: parse error: {e}")
            continue
        errors.extend(stage.validate(idx))
        stages.append(stage)

    if errors:
        raise ValueError("invalid input:\n  - " + "\n  - ".join(errors))

    return {
        "process_name": raw.get("process_name", "Untitled Process"),
        "wip": int(raw.get("wip", 0)) if raw.get("wip") is not None else 0,
        "stages": [asdict(s) for s in stages],
    }


def render_markdown(normalized: dict) -> str:
    """Render a text-based BPMN-style swim-lane diagram in Markdown."""
    name = normalized["process_name"]
    stages = normalized["stages"]
    lines: list[str] = []

    lines.append(f"# Process Map: {name}")
    lines.append("")
    lines.append(f"**Stages:** {len(stages)}  ")
    lines.append(
        f"**Total P50:** {sum(s['duration_minutes_p50'] for s in stages):.1f} min  "
    )
    lines.append(
        f"**Total P90:** {sum(s['duration_minutes_p90'] for s in stages):.1f} min"
    )
    lines.append("")

    # Group by owner -> swim lane
    lanes: dict[str, list[tuple[int, dict]]] = {}
    for idx, s in enumerate(stages):
        lanes.setdefault(s["owner"], []).append((idx, s))

    lines.append("## Swim Lanes")
    lines.append("")
    type_glyph = {"value-add": "[V]", "wait": "[W]", "rework": "[R]"}
    lane_width = max(20, max((len(o) for o in lanes), default=20) + 4)
    sep = "+" + "-" * (lane_width + 2) + "+" + "-" * 72 + "+"

    lines.append("```")
    lines.append(sep)
    lines.append(
        "| " + "OWNER".ljust(lane_width) + " | " + "STAGES (in process order)".ljust(70) + " |"
    )
    lines.append(sep)
    for owner, owned in lanes.items():
        owner_cell = owner.ljust(lane_width)
        cells = []
        for idx, s in owned:
            glyph = type_glyph.get(s["type"], "[?]")
            cells.append(
                f"#{idx+1} {glyph} {s['name'][:32]} "
                f"(p50={s['duration_minutes_p50']:.0f}m)"
            )
        row_text = "  ->  ".join(cells)
        # Wrap row_text to 70 chars
        wrapped = []
        cur = ""
        for token in row_text.split(" "):
            if len(cur) + len(token) + 1 > 70:
                wrapped.append(cur)
                cur = token
            else:
                cur = (cur + " " + token).strip()
        if cur:
            wrapped.append(cur)
        for i, line in enumerate(wrapped):
            left = owner_cell if i == 0 else " " * lane_width
            lines.append(f"| {left} | {line.ljust(70)} |")
        lines.append(sep)
    lines.append("```")
    lines.append("")
    lines.append("Legend: `[V]` value-add  `[W]` wait  `[R]` rework")
    lines.append("")

    lines.append("## Linear sequence")
    lines.append("")
    lines.append("| # | Stage | Owner | Type | P50 (min) | P90 (min) |")
    lines.append("|---|-------|-------|------|-----------|-----------|")
    for idx, s in enumerate(stages):
        lines.append(
            f"| {idx+1} | {s['name']} | {s['owner']} | {s['type']} | "
            f"{s['duration_minutes_p50']:.1f} | {s['duration_minutes_p90']:.1f} |"
        )
    lines.append("")
    return "\n".join(lines)


def sample_process() -> dict:
    return {
        "process_name": "Procurement Intake (Sample)",
        "wip": 12,
        "stages": [
            {
                "name": "Requestor submits PO request",
                "owner": "Requestor",
                "type": "value-add",
                "duration_minutes_p50": 15,
                "duration_minutes_p90": 30,
            },
            {
                "name": "Wait for manager review queue",
                "owner": "Manager",
                "type": "wait",
                "duration_minutes_p50": 480,
                "duration_minutes_p90": 1440,
            },
            {
                "name": "Manager approves request",
                "owner": "Manager",
                "type": "value-add",
                "duration_minutes_p50": 10,
                "duration_minutes_p90": 25,
            },
            {
                "name": "Wait for finance review queue",
                "owner": "Finance",
                "type": "wait",
                "duration_minutes_p50": 720,
                "duration_minutes_p90": 2880,
            },
            {
                "name": "Finance validates budget code",
                "owner": "Finance",
                "type": "value-add",
                "duration_minutes_p50": 20,
                "duration_minutes_p90": 60,
            },
            {
                "name": "Rework: missing vendor W-9",
                "owner": "Requestor",
                "type": "rework",
                "duration_minutes_p50": 120,
                "duration_minutes_p90": 360,
            },
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Document a business process as a BPMN-style swim-lane diagram."
    )
    parser.add_argument("--input", type=Path, help="Path to process JSON file.")
    parser.add_argument(
        "--output", type=Path, help="Output file path (default: stdout)."
    )
    parser.add_argument(
        "--format",
        choices=["markdown", "json"],
        default="markdown",
        help="Output format (default: markdown).",
    )
    parser.add_argument(
        "--sample",
        action="store_true",
        help="Print a 6-stage procurement-intake sample and exit.",
    )
    args = parser.parse_args()

    if args.sample:
        raw = sample_process()
    else:
        if not args.input:
            parser.error("--input is required unless --sample is given")
        if not args.input.exists():
            parser.error(f"input file not found: {args.input}")
        raw = load_process(args.input)

    try:
        normalized = normalize(raw)
    except ValueError as e:
        print(f"ERROR: {e}", file=sys.stderr)
        return 1

    if args.format == "json":
        out = json.dumps(normalized, indent=2)
    else:
        out = render_markdown(normalized)

    if args.output:
        args.output.write_text(out, encoding="utf-8")
        print(f"wrote {args.output}", file=sys.stderr)
    else:
        print(out)
    return 0


if __name__ == "__main__":
    sys.exit(main())
