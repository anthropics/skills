#!/usr/bin/env python3
"""study_designer.py - Select a product-research method from goal + stage, emit a plan skeleton.

Stdlib-only. Deterministic. NO LLM calls.

Maps (research goal x product stage) to an appropriate method and emits a method-matched
plan skeleton (objective framing, participant criteria, task/guide structure, success
criteria). The core discipline: GENERATIVE goals (discover problems) and EVALUATIVE goals
(test a solution) demand different methods — picking the wrong one is the most common error.

Usage:
    python3 study_designer.py --sample
    python3 study_designer.py --goal discovery --stage concept --profile b2b-saas
    python3 study_designer.py --goal evaluative --stage live --output json
"""

from __future__ import annotations

import argparse
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
try:
    import config_loader as _cfg
except ImportError:  # pragma: no cover
    _cfg = None

PROFILES = ["b2b-saas", "consumer-app", "enterprise", "marketplace", "hardware", "platform"]

# (goal, stage) -> method. goal in {discovery, evaluative, validation}; stage in {concept, prototype, beta, live}
METHOD_MAP = {
    ("discovery", "concept"): "generative interviews (semi-structured)",
    ("discovery", "prototype"): "contextual inquiry",
    ("discovery", "beta"): "diary study + follow-up interviews",
    ("discovery", "live"): "behavioral analytics review + generative interviews",
    ("evaluative", "concept"): "concept test (comprehension + desirability)",
    ("evaluative", "prototype"): "moderated usability test",
    ("evaluative", "beta"): "unmoderated usability test + task-success metrics",
    ("evaluative", "live"): "benchmark usability study (SUS / task time)",
    ("validation", "concept"): "survey (desirability + willingness signals)",
    ("validation", "prototype"): "prototype A/B preference test",
    ("validation", "beta"): "fake-door / feature-demand test",
    ("validation", "live"): "live A/B experiment (route to product-team/experiment-designer)",
}

GUIDE_SKELETONS = {
    "generative": ["Warm-up + context", "Recent relevant experience (story, not opinion)",
                   "Workarounds + frustrations", "Jobs-to-be-done probe", "Magic-wand / wrap"],
    "evaluative": ["Pre-task context", "Task 1 (representative)", "Task 2 (edge)",
                   "Observation: where do they hesitate/err?", "Post-task SUS / debrief"],
    "validation": ["Screener", "Stimulus exposure", "Comprehension + desirability items",
                   "Trade-off / preference items", "Behavioral-intent item"],
}


def design(goal: str, stage: str, profile: str) -> dict:
    if profile not in PROFILES:
        raise ValueError(f"Unknown profile '{profile}'. Choose from {PROFILES}.")
    key = (goal, stage)
    if key not in METHOD_MAP:
        raise ValueError(f"No method for goal={goal}, stage={stage}. "
                         f"goal in [discovery,evaluative,validation]; stage in [concept,prototype,beta,live].")
    method = METHOD_MAP[key]
    family = "generative" if goal == "discovery" else ("evaluative" if goal == "evaluative" else "validation")
    redirect = None
    if "experiment-designer" in method:
        redirect = "Live A/B is a product experiment — use product-team/experiment-designer, not this skill."
    return {
        "goal": goal,
        "stage": stage,
        "profile": profile,
        "method": method,
        "method_family": family,
        "objective_framing": f"A {family} study at the {stage} stage to {('discover unmet needs' if family=='generative' else 'evaluate the solution' if family=='evaluative' else 'validate demand/desirability')}.",
        "participant_criteria": [
            "Recruit to the target segment (screen for the job, not a job title).",
            "Exclude internal/biased participants and prior-study repeats unless longitudinal.",
            "Recruit per-segment if results will be reported per-segment.",
        ],
        "guide_skeleton": GUIDE_SKELETONS[family],
        "success_criteria": [
            "Generative: themes recur across independent participants (saturation).",
            "Evaluative: task-success rate + severity-rated problem list.",
            "Validation: pre-registered desirability / preference threshold.",
        ],
        "redirect": redirect,
        "note": "Method must match the goal. A usability test cannot discover unmet needs; an interview cannot measure task success.",
    }


def _render_human(r: dict) -> str:
    lines = [f"Study Design: goal={r['goal']}, stage={r['stage']}, profile={r['profile']}", "",
             f"  Recommended method: {r['method']}  (family: {r['method_family']})",
             f"  Objective: {r['objective_framing']}", "", "  Participant criteria:"]
    for c in r["participant_criteria"]:
        lines.append(f"    - {c}")
    lines.append("  Guide skeleton:")
    for i, g in enumerate(r["guide_skeleton"], 1):
        lines.append(f"    {i}. {g}")
    lines.append("  Success criteria:")
    for s in r["success_criteria"]:
        lines.append(f"    - {s}")
    if r["redirect"]:
        lines += ["", f"  !! {r['redirect']}"]
    lines += ["", f"note: {r['note']}"]
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description="Select a product-research method from goal + stage.")
    p.add_argument("--goal", choices=["discovery", "evaluative", "validation"], default="discovery")
    p.add_argument("--stage", choices=["concept", "prototype", "beta", "live"], default="prototype")
    p.add_argument("--profile", default=None, choices=PROFILES,
                   help="overrides onboarding default_profile")
    p.add_argument("--output", choices=["human", "json"], default="human")
    p.add_argument("--sample", action="store_true", help="use the embedded sample")
    args = p.parse_args(argv)

    conf = _cfg.load_config() if _cfg else {}
    profile_default = conf.get("default_profile", "b2b-saas")
    goal, stage, profile = ("discovery", "prototype", profile_default) if args.sample \
        else (args.goal, args.stage, args.profile or profile_default)
    try:
        result = design(goal, stage, profile)
    except ValueError as e:
        print(f"error: {e}", file=sys.stderr)
        return 2

    if args.output == "json":
        print(json.dumps(result, indent=2))
    else:
        print(_render_human(result))
    return 0


if __name__ == "__main__":
    sys.exit(main())
