#!/usr/bin/env python3
"""Frontend human-centered law auditor.

Reads evidence JSON, evaluates fast-gate checks and 21 human-centered principles,
then emits a markdown report and optional JSON output.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Callable

PASS = "pass"
FAIL = "fail"
UNKNOWN = "unknown"

STATUS_POINTS = {
    PASS: 1.0,
    FAIL: 0.0,
    UNKNOWN: 0.4,
}


@dataclass
class Principle:
    key: str
    name: str
    weight: int
    mechanism: str
    requirement: str
    signal: str
    fix: str
    evaluator: Callable[[dict[str, Any]], tuple[str, str]]


@dataclass
class GateCheck:
    key: str
    title: str
    evaluator: Callable[[dict[str, Any]], tuple[str, str]]
    fix: str


def as_bool(metrics: dict[str, Any], key: str) -> bool | None:
    value = metrics.get(key)
    if isinstance(value, bool):
        return value
    return None


def as_number(metrics: dict[str, Any], key: str) -> float | None:
    value = metrics.get(key)
    if isinstance(value, (int, float)):
        return float(value)
    return None


def as_text(metrics: dict[str, Any], key: str) -> str | None:
    value = metrics.get(key)
    if isinstance(value, str):
        return value.strip().lower()
    return None


def flag_missing(metrics: dict[str, Any], keys: list[str]) -> tuple[bool, str]:
    missing = [key for key in keys if metrics.get(key) is None]
    if missing:
        return True, f"Missing required metrics: {', '.join(missing)}"
    return False, ""


def make_bool_evaluator(
    key: str,
    expected: bool = True,
    pass_message: str = "Check passed.",
    fail_message: str = "Check failed.",
) -> Callable[[dict[str, Any]], tuple[str, str]]:
    def evaluator(metrics: dict[str, Any]) -> tuple[str, str]:
        value = as_bool(metrics, key)
        if value is None:
            return UNKNOWN, f"Missing boolean metric: {key}"
        if value is expected:
            return PASS, pass_message
        return FAIL, fail_message

    return evaluator


def evaluate_fitts(metrics: dict[str, Any]) -> tuple[str, str]:
    missing, reason = flag_missing(metrics, ["min_target_size_px", "primary_action_reach", "critical_action_at_task_end"])
    if missing:
        return UNKNOWN, reason
    size = as_number(metrics, "min_target_size_px")
    reach = as_text(metrics, "primary_action_reach")
    at_end = as_bool(metrics, "critical_action_at_task_end")
    if size is None or reach is None or at_end is None:
        return UNKNOWN, "Invalid metric types for Fitts's Law inputs."
    good_reach = reach in {"natural", "stretch", "near", "edge"}
    if size >= 44 and good_reach and at_end:
        return PASS, f"min_target_size_px={size:g}, reach={reach}, critical action aligned to task end."
    return FAIL, f"Need larger/easier targets or better placement (size={size:g}, reach={reach}, at_task_end={at_end})."


def evaluate_hick(metrics: dict[str, Any]) -> tuple[str, str]:
    missing, reason = flag_missing(metrics, ["screen_choice_count", "progressive_disclosure"])
    if missing:
        return UNKNOWN, reason
    choices = as_number(metrics, "screen_choice_count")
    disclosure = as_bool(metrics, "progressive_disclosure")
    if choices is None or disclosure is None:
        return UNKNOWN, "Invalid metric types for Hick's Law inputs."
    if choices <= 7 and disclosure:
        return PASS, f"screen_choice_count={choices:g}, progressive disclosure enabled."
    return FAIL, f"Too many concurrent choices or missing progressive disclosure (choices={choices:g}, disclosure={disclosure})."


def evaluate_miller(metrics: dict[str, Any]) -> tuple[str, str]:
    chunk_count = as_number(metrics, "chunk_count")
    if chunk_count is None:
        return UNKNOWN, "Missing numeric metric: chunk_count"
    if 3 <= chunk_count <= 9:
        return PASS, f"chunk_count={chunk_count:g} within manageable range."
    return FAIL, f"chunk_count={chunk_count:g} outside 3-9 chunk guidance."


def evaluate_doherty(metrics: dict[str, Any]) -> tuple[str, str]:
    feedback_ms = as_number(metrics, "feedback_ms_p95")
    if feedback_ms is None:
        return UNKNOWN, "Missing numeric metric: feedback_ms_p95"
    if feedback_ms <= 400:
        return PASS, f"feedback_ms_p95={feedback_ms:g}ms within threshold."
    return FAIL, f"feedback_ms_p95={feedback_ms:g}ms exceeds 400ms; users may lose flow."


def evaluate_focal(metrics: dict[str, Any]) -> tuple[str, str]:
    focal_points = as_number(metrics, "focal_points")
    if focal_points is None:
        return UNKNOWN, "Missing numeric metric: focal_points"
    if focal_points == 1:
        return PASS, "Exactly one focal point present."
    return FAIL, f"focal_points={focal_points:g}; expected exactly 1 dominant focal target."


def evaluate_von_restorff(metrics: dict[str, Any]) -> tuple[str, str]:
    isolates = as_number(metrics, "isolated_key_element_count")
    if isolates is None:
        return UNKNOWN, "Missing numeric metric: isolated_key_element_count"
    if 1 <= isolates <= 2:
        return PASS, f"isolated_key_element_count={isolates:g} keeps key isolation effective."
    return FAIL, f"isolated_key_element_count={isolates:g}; isolation is either missing or overused."


def evaluate_occam(metrics: dict[str, Any]) -> tuple[str, str]:
    score = as_number(metrics, "simplicity_score")
    if score is None:
        return UNKNOWN, "Missing numeric metric: simplicity_score"
    if score >= 80:
        return PASS, f"simplicity_score={score:g} indicates focused scope."
    return FAIL, f"simplicity_score={score:g}; interface likely has avoidable complexity."


def evaluate_parkinson(metrics: dict[str, Any]) -> tuple[str, str]:
    creep = as_bool(metrics, "scope_creep_signals")
    if creep is None:
        return UNKNOWN, "Missing boolean metric: scope_creep_signals"
    if not creep:
        return PASS, "No major scope creep signals found."
    return FAIL, "Feature/scope creep detected; trim non-critical additions."


def build_principles() -> list[Principle]:
    return [
        Principle(
            key="fitts",
            name="Fitts's Law",
            weight=5,
            mechanism="Movement time is shaped by target distance and size.",
            requirement="Critical actions must be large and easy to reach.",
            signal="Target size and reachability improve hit accuracy and speed.",
            fix="Increase target size/padding and move high-value actions closer to task endpoints.",
            evaluator=evaluate_fitts,
        ),
        Principle(
            key="hick",
            name="Hick's Law",
            weight=5,
            mechanism="Decision time rises as visible choices increase.",
            requirement="Limit concurrent choices and defer advanced options.",
            signal="Lower first-action latency and reduced decision stall.",
            fix="Reduce choice density and introduce progressive disclosure.",
            evaluator=evaluate_hick,
        ),
        Principle(
            key="gestalt-proximity",
            name="Gestalt: Proximity",
            weight=4,
            mechanism="Spatial closeness signals conceptual grouping.",
            requirement="Related items stay close, unrelated groups stay apart.",
            signal="Fewer label-field association errors.",
            fix="Increase intra-group cohesion and inter-group separation.",
            evaluator=lambda m: _range_eval(
                m,
                key="group_spacing_ratio",
                lower=2.0,
                pass_message="group_spacing_ratio supports clear grouping.",
                fail_message="group_spacing_ratio too low; group boundaries unclear.",
            ),
        ),
        Principle(
            key="gestalt-similarity",
            name="Gestalt: Similarity",
            weight=4,
            mechanism="Shared appearance implies shared function.",
            requirement="Same component role must keep consistent styling.",
            signal="Reduced functional misclassification.",
            fix="Unify role-based tokens for color, shape, and typography.",
            evaluator=make_bool_evaluator(
                "role_style_consistency",
                expected=True,
                pass_message="Role styles are consistent.",
                fail_message="Role style inconsistency likely causes behavior confusion.",
            ),
        ),
        Principle(
            key="gestalt-continuity",
            name="Gestalt: Continuity",
            weight=3,
            mechanism="Eyes follow uninterrupted visual paths.",
            requirement="Flow and continuation cues should be explicit.",
            signal="Better discovery of next steps and off-screen content.",
            fix="Align paths and expose continuation hints (peeking cards, steppers).",
            evaluator=make_bool_evaluator(
                "continuity_cue",
                expected=True,
                pass_message="Continuity cues are present.",
                fail_message="Missing continuity cues reduce flow discoverability.",
            ),
        ),
        Principle(
            key="gestalt-closure",
            name="Gestalt: Closure",
            weight=2,
            mechanism="Users mentally complete incomplete shapes/structures.",
            requirement="Partial visual structures must remain interpretable.",
            signal="Cleaner UI with intact comprehension.",
            fix="Use simplified structure only when completion remains obvious.",
            evaluator=make_bool_evaluator(
                "closure_support",
                expected=True,
                pass_message="Closure cues are interpretable.",
                fail_message="Insufficient closure cues make partial structures ambiguous.",
            ),
        ),
        Principle(
            key="gestalt-figure-ground",
            name="Gestalt: Figure/Ground",
            weight=4,
            mechanism="Attention depends on clear foreground/background separation.",
            requirement="Focus context should dominate via layering and contrast.",
            signal="Lower context-loss in modal/sheet flows.",
            fix="Strengthen scrim/layer contrast and focus hierarchy.",
            evaluator=make_bool_evaluator(
                "figure_ground_contrast",
                expected=True,
                pass_message="Figure/ground separation is clear.",
                fail_message="Weak figure/ground separation causes focus ambiguity.",
            ),
        ),
        Principle(
            key="gestalt-common-fate",
            name="Gestalt: Common Fate",
            weight=3,
            mechanism="Synchronized motion implies grouping.",
            requirement="Related elements should animate in coordinated direction/timing.",
            signal="Improved grouping comprehension in motion states.",
            fix="Unify motion curves/directions for grouped elements.",
            evaluator=make_bool_evaluator(
                "motion_group_consistency",
                expected=True,
                pass_message="Motion grouping is coherent.",
                fail_message="Motion inconsistency weakens perceived grouping.",
            ),
        ),
        Principle(
            key="gestalt-focal-point",
            name="Gestalt: Focal Point",
            weight=4,
            mechanism="Contrast directs first attention.",
            requirement="Each screen should have one dominant attention anchor.",
            signal="Higher primary action discoverability.",
            fix="Converge to one visual priority and demote competing accents.",
            evaluator=evaluate_focal,
        ),
        Principle(
            key="von-restorff",
            name="Von Restorff Effect",
            weight=3,
            mechanism="Distinct items are more memorable than uniform items.",
            requirement="Isolate one key action/info node from a stable baseline.",
            signal="Higher recall and click concentration on key target.",
            fix="Use selective contrast for one key choice, not all choices.",
            evaluator=evaluate_von_restorff,
        ),
        Principle(
            key="jakob",
            name="Jakob's Law",
            weight=4,
            mechanism="Users expect familiar interaction patterns from prior products.",
            requirement="Trust-critical flows should follow established conventions.",
            signal="Lower navigation and auth confusion.",
            fix="Align navigation/search/auth/checkout patterns with common standards.",
            evaluator=make_bool_evaluator(
                "pattern_familiarity",
                expected=True,
                pass_message="Conventions are preserved in critical flows.",
                fail_message="Unfamiliar critical patterns raise cognitive onboarding cost.",
            ),
        ),
        Principle(
            key="miller",
            name="Miller's Law",
            weight=4,
            mechanism="Working memory handles limited chunks concurrently.",
            requirement="Chunk content and stage long tasks.",
            signal="Improved completion on long forms and flows.",
            fix="Split dense screens into smaller chunked steps.",
            evaluator=evaluate_miller,
        ),
        Principle(
            key="goal-gradient",
            name="Goal-Gradient Hypothesis",
            weight=3,
            mechanism="Motivation rises as users approach completion.",
            requirement="Progress and milestones should remain visible.",
            signal="Completion acceleration in later steps.",
            fix="Expose progress counters and milestone reinforcement.",
            evaluator=make_bool_evaluator(
                "progress_visible",
                expected=True,
                pass_message="Progress visibility supports motivation.",
                fail_message="Hidden progress weakens completion momentum.",
            ),
        ),
        Principle(
            key="zeigarnik",
            name="Zeigarnik Effect",
            weight=3,
            mechanism="Incomplete tasks persist in memory and drive return behavior.",
            requirement="Unfinished states must be visible with a resume path.",
            signal="Higher interrupted-flow recovery.",
            fix="Expose completion status and one-click resume mechanisms.",
            evaluator=make_bool_evaluator(
                "unfinished_resume_path",
                expected=True,
                pass_message="Resume path for unfinished tasks exists.",
                fail_message="No clear resume path for interrupted tasks.",
            ),
        ),
        Principle(
            key="tesler",
            name="Tesler's Law",
            weight=4,
            mechanism="Complexity cannot be removed, only redistributed.",
            requirement="System should absorb complexity from users.",
            signal="Lower entry friction and cleaner structured data.",
            fix="Use smart defaults, autocomplete, masks, and structured controls.",
            evaluator=make_bool_evaluator(
                "system_handles_complexity",
                expected=True,
                pass_message="System absorbs key complexity.",
                fail_message="User is carrying avoidable complexity burden.",
            ),
        ),
        Principle(
            key="peak-end",
            name="Peak-End Rule",
            weight=4,
            mechanism="Users remember the peak and the ending disproportionately.",
            requirement="Final states should be explicit and confidence-building.",
            signal="Higher satisfaction and reduced uncertainty after submit.",
            fix="Add clear success/failure closure with next-step guidance.",
            evaluator=make_bool_evaluator(
                "positive_end_state",
                expected=True,
                pass_message="Ending experience provides clear closure.",
                fail_message="Weak ending state likely harms recall and trust.",
            ),
        ),
        Principle(
            key="postel",
            name="Postel's Law",
            weight=4,
            mechanism="Robust systems accept varied input but emit consistent output.",
            requirement="Input parsing should tolerate common human variations.",
            signal="Fewer avoidable validation dead-ends.",
            fix="Support tolerant parsing and provide precise recovery guidance.",
            evaluator=make_bool_evaluator(
                "input_tolerant_parsing",
                expected=True,
                pass_message="Input handling is tolerant and structured.",
                fail_message="Rigid input handling likely punishes normal user variations.",
            ),
        ),
        Principle(
            key="doherty",
            name="Doherty Threshold",
            weight=5,
            mechanism="Fast feedback preserves cognitive flow and productivity.",
            requirement="Interactions should acknowledge user intent rapidly.",
            signal="Reduced duplicate taps and waiting confusion.",
            fix="Provide immediate visual acknowledgment and optimize perceived speed.",
            evaluator=evaluate_doherty,
        ),
        Principle(
            key="serial-position",
            name="Serial Position Effect",
            weight=3,
            mechanism="First and last sequence items are recalled best.",
            requirement="Place critical actions/info at sequence boundaries.",
            signal="Higher discovery/recall of key actions.",
            fix="Move top-priority actions to start/end positions.",
            evaluator=make_bool_evaluator(
                "critical_actions_boundary_placement",
                expected=True,
                pass_message="Critical actions are at memorable boundaries.",
                fail_message="Critical actions are buried in low-recall positions.",
            ),
        ),
        Principle(
            key="occam",
            name="Occam's Razor",
            weight=3,
            mechanism="Simpler sufficient solutions reduce cognitive load.",
            requirement="Remove non-essential UI and interaction burden.",
            signal="Faster task completion and fewer distractions.",
            fix="Trim unnecessary states/features and simplify task path.",
            evaluator=evaluate_occam,
        ),
        Principle(
            key="parkinson",
            name="Parkinson's Law",
            weight=2,
            mechanism="Work expands without explicit constraints.",
            requirement="Guard against feature creep in delivery scope.",
            signal="Lean implementation aligned to user goal.",
            fix="Enforce MVP boundaries and defer non-critical additions.",
            evaluator=evaluate_parkinson,
        ),
    ]


def _range_eval(
    metrics: dict[str, Any],
    key: str,
    lower: float | None = None,
    upper: float | None = None,
    pass_message: str = "Range check passed.",
    fail_message: str = "Range check failed.",
) -> tuple[str, str]:
    value = as_number(metrics, key)
    if value is None:
        return UNKNOWN, f"Missing numeric metric: {key}"
    if lower is not None and value < lower:
        return FAIL, f"{fail_message} ({key}={value:g}, lower={lower:g})"
    if upper is not None and value > upper:
        return FAIL, f"{fail_message} ({key}={value:g}, upper={upper:g})"
    return PASS, f"{pass_message} ({key}={value:g})"


def build_gate_checks() -> list[GateCheck]:
    return [
        GateCheck(
            key="one-primary-cta",
            title="Single dominant primary CTA",
            evaluator=lambda m: _range_eval(
                m,
                key="primary_cta_count",
                lower=1,
                upper=1,
                pass_message="Exactly one primary CTA found.",
                fail_message="Need exactly one primary CTA.",
            ),
            fix="Keep one dominant primary action and demote secondary actions.",
        ),
        GateCheck(
            key="touch-target-size",
            title="Critical touch targets >= 44px",
            evaluator=lambda m: _range_eval(
                m,
                key="min_target_size_px",
                lower=44,
                pass_message="Target size meets minimum threshold.",
                fail_message="Target size below threshold.",
            ),
            fix="Increase hit area (padding/wrapper) for critical controls.",
        ),
        GateCheck(
            key="task-end-action-placement",
            title="Primary completion action at task endpoint",
            evaluator=make_bool_evaluator(
                "critical_action_at_task_end",
                expected=True,
                pass_message="Completion action aligns with task endpoint.",
                fail_message="Completion action placement breaks task flow.",
            ),
            fix="Place submit/continue where user naturally finishes the task.",
        ),
        GateCheck(
            key="choice-density",
            title="Choice density <= 7 visible options",
            evaluator=lambda m: _range_eval(
                m,
                key="screen_choice_count",
                upper=7,
                pass_message="Choice density is manageable.",
                fail_message="Too many visible choices.",
            ),
            fix="Reduce options and defer advanced paths with progressive disclosure.",
        ),
        GateCheck(
            key="progress-visible",
            title="Progress visible on multi-step flows",
            evaluator=make_bool_evaluator(
                "progress_visible",
                expected=True,
                pass_message="Progress indicators are visible.",
                fail_message="Progress indicators are missing or unclear.",
            ),
            fix="Add stepper/progress bar/counter for staged tasks.",
        ),
        GateCheck(
            key="fast-feedback",
            title="Interaction feedback <= 400ms p95",
            evaluator=evaluate_doherty,
            fix="Show immediate pressed/loading feedback and reduce response latency.",
        ),
        GateCheck(
            key="inline-validation",
            title="Validation rules visible with inline recovery",
            evaluator=make_bool_evaluator(
                "inline_validation_clear",
                expected=True,
                pass_message="Validation behavior is clear and inline.",
                fail_message="Validation guidance is hidden or vague.",
            ),
            fix="Show requirements before submit and field-level actionable errors.",
        ),
        GateCheck(
            key="input-tolerant",
            title="Input tolerance and normalization",
            evaluator=make_bool_evaluator(
                "input_tolerant_parsing",
                expected=True,
                pass_message="Input parsing handles common variations.",
                fail_message="Input handling is brittle for normal human formats.",
            ),
            fix="Accept common formats and normalize internally.",
        ),
        GateCheck(
            key="boundary-placement",
            title="Critical actions are at list/menu boundaries",
            evaluator=make_bool_evaluator(
                "critical_actions_boundary_placement",
                expected=True,
                pass_message="Critical actions use high-recall positions.",
                fail_message="Critical actions are placed in low-recall mid positions.",
            ),
            fix="Move high-priority actions to beginning or end positions.",
        ),
        GateCheck(
            key="clear-ending",
            title="Explicit positive ending/closure",
            evaluator=make_bool_evaluator(
                "positive_end_state",
                expected=True,
                pass_message="Flow ending provides clear closure.",
                fail_message="Ending lacks confidence and closure feedback.",
            ),
            fix="Add success/failure confirmation and next-step guidance.",
        ),
    ]


def build_template() -> dict[str, Any]:
    return {
        "meta": {
            "project": "example-product",
            "flow": "signup",
            "auditor": "your-name",
            "notes": "Fill measured values before running strict mode.",
        },
        "metrics": {
            "primary_cta_count": 1,
            "min_target_size_px": 44,
            "primary_action_reach": "natural",
            "critical_action_at_task_end": True,
            "screen_choice_count": 6,
            "progressive_disclosure": True,
            "group_spacing_ratio": 2.0,
            "role_style_consistency": True,
            "continuity_cue": True,
            "closure_support": True,
            "figure_ground_contrast": True,
            "motion_group_consistency": True,
            "focal_points": 1,
            "isolated_key_element_count": 1,
            "pattern_familiarity": True,
            "chunk_count": 6,
            "progress_visible": True,
            "unfinished_resume_path": True,
            "system_handles_complexity": True,
            "positive_end_state": True,
            "input_tolerant_parsing": True,
            "feedback_ms_p95": 300,
            "critical_actions_boundary_placement": True,
            "inline_validation_clear": True,
            "simplicity_score": 85,
            "scope_creep_signals": False,
        },
    }


def evaluate_principles(metrics: dict[str, Any], principles: list[Principle]) -> list[dict[str, Any]]:
    results: list[dict[str, Any]] = []
    for principle in principles:
        status, diagnosis = principle.evaluator(metrics)
        results.append(
            {
                "key": principle.key,
                "name": principle.name,
                "weight": principle.weight,
                "status": status,
                "diagnosis": diagnosis,
                "mechanism": principle.mechanism,
                "requirement": principle.requirement,
                "signal": principle.signal,
                "fix": principle.fix,
            }
        )
    return results


def evaluate_gates(metrics: dict[str, Any], gates: list[GateCheck]) -> list[dict[str, Any]]:
    results: list[dict[str, Any]] = []
    for gate in gates:
        status, evidence = gate.evaluator(metrics)
        results.append(
            {
                "key": gate.key,
                "title": gate.title,
                "status": status,
                "evidence": evidence,
                "fix": gate.fix,
            }
        )
    return results


def compute_score(results: list[dict[str, Any]]) -> float:
    total_weight = sum(result["weight"] for result in results)
    if total_weight == 0:
        return 0.0
    weighted_points = 0.0
    for result in results:
        points = STATUS_POINTS.get(result["status"], 0.0)
        weighted_points += result["weight"] * points
    return round((weighted_points / total_weight) * 100.0, 2)


def status_emoji(status: str) -> str:
    if status == PASS:
        return "PASS"
    if status == FAIL:
        return "FAIL"
    return "UNKNOWN"


def classify_priority(result: dict[str, Any]) -> str:
    if result["status"] != FAIL:
        return ""
    weight = result["weight"]
    if weight >= 5:
        return "P0"
    if weight >= 4:
        return "P1"
    return "P2"


def render_report(
    meta: dict[str, Any],
    gate_results: list[dict[str, Any]],
    principle_results: list[dict[str, Any]],
    score: float,
) -> str:
    now = datetime.now(timezone.utc).isoformat()
    gate_failures = [row for row in gate_results if row["status"] == FAIL]
    unknown_principles = [row for row in principle_results if row["status"] == UNKNOWN]
    priorities = [row for row in principle_results if row["status"] == FAIL]
    priorities.sort(key=lambda row: row["weight"], reverse=True)

    lines: list[str] = []
    lines.append("# Frontend Human-Centered Law Audit")
    lines.append("")
    lines.append(f"- Generated (UTC): {now}")
    lines.append(f"- Project: {meta.get('project', 'unknown')}")
    lines.append(f"- Flow: {meta.get('flow', 'unknown')}")
    lines.append(f"- Auditor: {meta.get('auditor', 'unknown')}")
    lines.append("")
    lines.append("## Summary")
    lines.append("")
    lines.append(f"- Overall score: **{score:.2f}/100**")
    lines.append(f"- Fast gate failures: **{len(gate_failures)}** / {len(gate_results)}")
    lines.append(f"- Principle failures: **{len(priorities)}** / {len(principle_results)}")
    lines.append(f"- Unknown principle checks: **{len(unknown_principles)}**")
    lines.append("")
    lines.append("## Fast Gate")
    lines.append("")
    lines.append("| Check | Status | Evidence | Fix |")
    lines.append("|---|---|---|---|")
    for gate in gate_results:
        lines.append(
            f"| {gate['title']} | {status_emoji(gate['status'])} | {gate['evidence']} | {gate['fix']} |"
        )
    lines.append("")
    lines.append("## Principle Results")
    lines.append("")
    lines.append("| Priority | Principle | Status | Weight | Diagnosis | Required change |")
    lines.append("|---|---|---|---:|---|---|")
    for result in principle_results:
        priority = classify_priority(result)
        lines.append(
            f"| {priority} | {result['name']} | {status_emoji(result['status'])} | {result['weight']} | {result['diagnosis']} | {result['fix']} |"
        )
    lines.append("")
    lines.append("## Priority Fix Backlog")
    lines.append("")
    if priorities:
        for result in priorities:
            priority = classify_priority(result)
            lines.append(f"- **{priority} {result['name']}**: {result['diagnosis']}")
            lines.append(f"  - Why it matters: {result['mechanism']}")
            lines.append(f"  - Acceptance target: {result['signal']}")
            lines.append(f"  - Fix: {result['fix']}")
    else:
        lines.append("- No failed principles. Keep regression checks in CI.")
    lines.append("")
    if unknown_principles:
        lines.append("## Data Gaps")
        lines.append("")
        for result in unknown_principles:
            lines.append(f"- **{result['name']}**: {result['diagnosis']}")
        lines.append("")
    lines.append("## Recheck Criteria")
    lines.append("")
    lines.append("- Fast gate failures must be zero.")
    lines.append("- Overall score should meet or exceed team threshold.")
    lines.append("- Unknown checks should be resolved by adding missing evidence.")
    lines.append("")
    return "\n".join(lines)


def load_input(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError("Input JSON must be an object.")
    meta = payload.get("meta")
    metrics = payload.get("metrics")
    if not isinstance(meta, dict):
        raise ValueError("Input JSON must include object field: meta")
    if not isinstance(metrics, dict):
        raise ValueError("Input JSON must include object field: metrics")
    return payload


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Audit frontend evidence against human-centered design laws.")
    parser.add_argument("--input", type=Path, help="Path to evidence JSON.")
    parser.add_argument("--output", type=Path, help="Path to markdown report output.")
    parser.add_argument("--json-out", type=Path, help="Optional JSON results output path.")
    parser.add_argument("--strict", action="store_true", help="Return non-zero when gate/score threshold fails.")
    parser.add_argument("--fail-threshold", type=float, default=85.0, help="Minimum score required in strict mode.")
    parser.add_argument("--init-template", type=Path, help="Write a template evidence JSON to this path and exit.")
    args = parser.parse_args()

    if args.init_template:
        template = build_template()
        write_json(args.init_template, template)
        print(f"Wrote template evidence JSON: {args.init_template}")
        return 0

    if not args.input:
        parser.error("--input is required unless --init-template is used.")

    payload = load_input(args.input)
    meta = payload["meta"]
    metrics = payload["metrics"]

    principles = build_principles()
    gates = build_gate_checks()
    principle_results = evaluate_principles(metrics, principles)
    gate_results = evaluate_gates(metrics, gates)
    score = compute_score(principle_results)
    report = render_report(meta, gate_results, principle_results, score)

    if args.output:
        args.output.write_text(report + "\n", encoding="utf-8")
        print(f"Wrote markdown report: {args.output}")
    else:
        print(report)

    result_payload = {
        "meta": meta,
        "score": score,
        "gate_results": gate_results,
        "principle_results": principle_results,
        "strict_threshold": args.fail_threshold,
    }
    if args.json_out:
        write_json(args.json_out, result_payload)
        print(f"Wrote JSON results: {args.json_out}")

    if args.strict:
        gate_failures = sum(1 for gate in gate_results if gate["status"] == FAIL)
        if gate_failures > 0 or score < args.fail_threshold:
            print(
                f"Strict mode failed: gate_failures={gate_failures}, score={score:.2f}, threshold={args.fail_threshold:.2f}",
            )
            return 2

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
