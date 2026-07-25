#!/usr/bin/env python3
"""route_explainer.py - Print the routing decision in a form the LLM can act on.

Stdlib-only. Takes the JSON output of doctype_classifier.py (or runs the
classifier itself), and prints a short routing brief: which sub-skill to
invoke, what evidence supports the decision, and what to ask the user if
the verdict is ambiguous.

This is the "never silently chain" enforcer — it prints the recommendation
in a structured form that makes it obvious whether the orchestrator should
route silently, ask one clarifying question, or refuse outright (because
the input is below the 100-line threshold or design-system isn't onboarded).

NO LLM CALLS. Pure formatting + decision-tree branching.

Usage:
    python doctype_classifier.py --input X.md --output json | python route_explainer.py
    python route_explainer.py --classification-file classification.json
"""

from __future__ import annotations

import argparse
import json
import os
import sys
from pathlib import Path
from typing import Any

# Bridge to the design-system config so we can refuse if not onboarded
_DESIGN_SYSTEM_SCRIPTS = (
    Path(__file__).resolve().parent.parent.parent / "design-system" / "scripts"
)
sys.path.insert(0, str(_DESIGN_SYSTEM_SCRIPTS))
try:
    import config_loader as cfg
except ImportError:
    cfg = None


def _design_system_status() -> dict[str, Any]:
    if cfg is None:
        return {"onboarded": False, "reason": "config_loader not importable"}
    if os.environ.get("MARKDOWN_HTML_NO_CONFIG") == "1":
        return {"onboarded": True, "reason": "bypass env set", "bypass": True}
    if cfg.setup_completed():
        c = cfg.load_config()
        return {
            "onboarded": True,
            "default_output_dir": c.get("default_output_dir"),
            "design_style": c.get("design_style"),
            "brand_primary": (c.get("brand") or {}).get("primary"),
            "completed_at": c.get("setup_completed_at"),
        }
    return {"onboarded": False, "reason": "no setup_completed_at in config"}


def explain(classification: dict[str, Any]) -> dict[str, Any]:
    verdict = classification["verdict"]
    line_count = classification["line_count"]
    below_min = classification["below_min_lines"]
    ds = _design_system_status()

    refusals: list[str] = []

    if below_min:
        refusals.append(
            f"Input is {line_count} lines (< {classification['min_lines_threshold']}). "
            f"Per Shihipar's threshold, markdown wins below 100 lines. "
            f"Recommend keeping this as markdown and re-running only on longer documents."
        )
    if not ds.get("onboarded"):
        refusals.append(
            "Design-system has not been onboarded. Run "
            "`python3 markdown-html/skills/design-system/scripts/onboard.py` "
            "(or `--defaults`) before conversion, so the converters have brand tokens to apply."
        )

    next_action = ""
    sub_skill = None

    if refusals:
        next_action = "REFUSE — fix the issues above before routing."
    elif verdict in ("document", "review", "slides"):
        sub_skill = f"md-{verdict}"
        next_action = (
            f"ROUTE_SILENTLY -> {sub_skill}. "
            f"Evidence: {classification['winner']} won with score "
            f"{classification['winner_score']} (runner-up {classification['runner_up']}="
            f"{classification['runner_up_score']})."
        )
    elif verdict == "needs-clarification":
        winner = classification["winner"]
        runner = classification["runner_up"]
        next_action = (
            f"ASK_USER one question: 'I see signals for both md-{winner} (score "
            f"{classification['winner_score']}) and md-{runner} (score "
            f"{classification['runner_up_score']}). Recommended: md-{winner}. "
            f"Confirm or override?'"
        )
    else:  # ambiguous
        next_action = (
            "ASK_USER one question: 'Which document type is this — long-form "
            "document, code review with diff, or slide deck? "
            "Recommended: md-document (safe default).'"
        )

    return {
        "decision": "REFUSE" if refusals else next_action.split(" ", 1)[0],
        "sub_skill": sub_skill,
        "next_action": next_action,
        "refusals": refusals,
        "classification_verdict": verdict,
        "line_count": line_count,
        "design_system": ds,
    }


def render_human(explanation: dict[str, Any]) -> str:
    out = []
    out.append(f"Routing decision: {explanation['decision']}")
    if explanation["sub_skill"]:
        out.append(f"  sub-skill: {explanation['sub_skill']}")
    out.append(f"  next action: {explanation['next_action']}")
    if explanation["refusals"]:
        out.append("")
        out.append("Refusals:")
        for r in explanation["refusals"]:
            out.append(f"  - {r}")
    out.append("")
    out.append("Design-system:")
    ds = explanation["design_system"]
    out.append(f"  onboarded: {ds.get('onboarded')}")
    if ds.get("onboarded"):
        out.append(f"  default_output_dir: {ds.get('default_output_dir')}")
        out.append(f"  design_style: {ds.get('design_style')}")
        out.append(f"  brand_primary: {ds.get('brand_primary')}")
    else:
        out.append(f"  reason: {ds.get('reason')}")
    return "\n".join(out)


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--classification-file",
                        help="Path to a doctype_classifier JSON output. Default: read stdin.")
    parser.add_argument("--output", choices=["human", "json"], default="human")
    args = parser.parse_args(argv)

    if args.classification_file:
        with open(args.classification_file, encoding="utf-8") as f:
            classification = json.load(f)
    else:
        if sys.stdin.isatty():
            parser.print_help()
            return 0
        classification = json.load(sys.stdin)

    explanation = explain(classification)
    if args.output == "json":
        print(json.dumps(explanation, indent=2))
    else:
        print(render_human(explanation))
    return 0 if explanation["decision"] != "REFUSE" else 3


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
