#!/usr/bin/env python3
"""Workflow intake recommendation engine.

Turns a (possibly vague) workflow request into a concrete topology proposal:
recommended topology, model picks, a budget guard, and a one-line rationale for
every choice. Fills unknown answers with the safest documented default so a
vague request still yields a presentable "here's what I'd build and why".

Stdlib only. Deterministic: same inputs -> same recommendation.
"""
import argparse
import json
import re
import sys

CHOICES_TRI = ("yes", "no", "unknown")
CHOICES_UNITS = ("known", "unknown", "loop")
CHOICES_STAGES = ("single", "multiple", "unknown")

# Keyword -> signal. Lowercased substring match on the task description.
VERB_CHAIN = ("then", "->", "=>", "after", "followed by", "and then")
PANEL_WORDS = ("best", "compare", "options", "approaches", "alternatives",
               "candidates", "which", "rank", "score them")
COSTLY_WORDS = ("critical", "costly", "act on", "production", "security",
                "verify", "false positive", "high stakes", "merge", "deploy")
LOOP_WORDS = ("until", "keep", "as many", "all the", "every", "exhaust",
              "find issues", "discover", "as long as", "budget")
MERGE_WORDS = ("dedup", "deduplicate", "merge results", "merge findings",
               "merge them all", "combine all", "consolidate", "aggregate",
               "count across", "total across")
LIST_WORDS = ("each", "list of", "set of", "batch", "files", "documents",
              "questions", "items", "prs", "pull requests", "tickets")


def _has(task, words):
    t = task.lower()
    return any(w in t for w in words)


def classify(task, units, stages, needs_all, structured):
    """Return (topology, runner_up_or_None, signals_dict)."""
    t = task.lower()
    signals = {
        "verb_chain": bool(re.search(r"\b(then|after)\b", t)) or _has(task, VERB_CHAIN),
        "panel": _has(task, PANEL_WORDS),
        "costly": _has(task, COSTLY_WORDS),
        "loop_like": _has(task, LOOP_WORDS),
        "merge_like": _has(task, MERGE_WORDS),
        "list_like": _has(task, LIST_WORDS),
    }

    # Resolve unknowns with documented defaults (see decision_and_intake_guide.md).
    if units == "unknown":
        if signals["loop_like"]:
            units_eff = "loop"
        elif signals["list_like"] or signals["merge_like"]:
            # An explicit list, or a dedup/merge step, both imply a bounded set.
            units_eff = "known"
        else:
            units_eff = "loop"  # safest default when the count is undiscovered
    else:
        units_eff = units
    if stages == "unknown":
        stages_eff = "multiple" if signals["verb_chain"] else "single"
    else:
        stages_eff = stages
    if needs_all == "unknown":
        needs_all_eff = "yes" if signals["merge_like"] else "no"
    else:
        needs_all_eff = needs_all

    signals["units_effective"] = units_eff
    signals["stages_effective"] = stages_eff
    signals["needs_all_effective"] = needs_all_eff

    # Decision tree.
    runner_up = None
    if signals["panel"]:
        topology = "judge-panel"
        runner_up = "fan-out"
    elif units_eff == "loop":
        topology = "loop"
        runner_up = "fan-out"
    elif needs_all_eff == "yes":
        topology = "barrier"
        runner_up = "pipeline"
    elif stages_eff == "multiple":
        topology = "pipeline"
        runner_up = "barrier"
    else:
        topology = "fan-out"
        runner_up = "pipeline"

    return topology, runner_up, signals


def model_plan(topology, signals):
    """Per-stage model recommendation."""
    plan = []
    if topology == "fan-out":
        plan.append(("fan-out stage", "haiku", "independent, mechanical per-item work is cheap on Haiku"))
        plan.append(("final synthesis", "opus", "combining many results into one report needs strong reasoning"))
    elif topology == "pipeline":
        plan.append(("stage 1 (triage/extract)", "haiku", "first-pass classification is cheap and high-volume"))
        plan.append(("stage 2 (verify/refine)", "sonnet", "second stage acts on fewer items and needs judgement"))
    elif topology == "barrier":
        plan.append(("parallel collection", "haiku", "gather raw results cheaply before the merge"))
        plan.append(("merge/dedup synthesis", "opus", "reconciling the full set is the hard reasoning step"))
    elif topology == "loop":
        plan.append(("per-iteration agent", "sonnet", "each round must reason about what's already found"))
    elif topology == "judge-panel":
        plan.append(("draft angles", "sonnet", "diverse drafts need real generation capability"))
        plan.append(("scoring judges", "haiku", "scoring against a rubric is cheap and parallelizable"))
        plan.append(("final refine", "opus", "polishing the winning plan rewards the strongest model"))
    if signals.get("costly"):
        plan.append(("skeptic-vote verification", "sonnet",
                     "a wrong result is costly here — add 3 independent refute-attempts, survive on majority"))
    return plan


def budget_guard(signals):
    if signals["units_effective"] == "loop":
        return ("budget.remaining() > 50_000 (plus a hard count cap)",
                "open-ended loop — guard is mandatory or it hits the 1000-agent cap")
    return ("optional; set budget.total if the user gave a token target",
            "fixed topology with a known/bounded item count — no runaway risk")


def recommend(task, units, stages, needs_all, structured):
    topology, runner_up, signals = classify(task, units, stages, needs_all, structured)
    models = model_plan(topology, signals)
    bguard, bwhy = budget_guard(signals)

    if structured == "unknown":
        structured_eff = "yes"
        structured_why = "default on — a small JSON schema makes downstream stages reliable at near-zero cost"
    else:
        structured_eff = structured
        structured_why = ("user asked for structured data back" if structured == "yes"
                          else "user wants free-text output")

    rationale = {
        "topology": _topology_reason(topology, signals),
        "runner_up": runner_up,
        "structured_output": structured_why,
        "budget": bwhy,
    }
    return {
        "task": task,
        "recommended_topology": topology,
        "runner_up_topology": runner_up,
        "resolved_signals": {k: v for k, v in signals.items() if k.endswith("effective") or k in
                             ("panel", "costly", "loop_like", "merge_like", "verb_chain", "list_like")},
        "model_plan": [{"stage": s, "model": m, "why": w} for s, m, w in models],
        "structured_output": structured_eff,
        "budget_guard": bguard,
        "rationale": rationale,
        "add_verification": bool(signals.get("costly")),
    }


def _topology_reason(topology, signals):
    return {
        "fan-out": "independent units, one pass each, combined at the end -> parallel fan-out then a final synthesis agent",
        "pipeline": "ordered stages where each item should advance the moment it's ready (no barrier) -> pipeline; faster than parallel-per-stage",
        "barrier": "a later step needs the whole prior result set (dedup/merge/count) -> parallel barrier, then process",
        "loop": "item count is undiscovered -> guarded loop (stop on goal, budget, or dryness) with a hard cap",
        "judge-panel": "wide solution space, want best-of-N -> generate diverse drafts, score in parallel, synthesize the winner",
    }[topology]


def render_human(rec):
    lines = []
    lines.append(f"Task: {rec['task']}")
    lines.append("")
    lines.append(f"RECOMMENDED TOPOLOGY: {rec['recommended_topology']}")
    lines.append(f"  why: {rec['rationale']['topology']}")
    if rec["runner_up_topology"]:
        lines.append(f"  runner-up if the above doesn't fit: {rec['runner_up_topology']}")
    lines.append("")
    lines.append("MODEL PLAN:")
    for m in rec["model_plan"]:
        lines.append(f"  - {m['stage']}: {m['model']}  ({m['why']})")
    lines.append("")
    lines.append(f"STRUCTURED OUTPUT: {rec['structured_output']}  ({rec['rationale']['structured_output']})")
    lines.append(f"BUDGET GUARD: {rec['budget_guard']}")
    lines.append(f"  why: {rec['rationale']['budget']}")
    if rec["add_verification"]:
        lines.append("VERIFICATION: add a skeptic-vote pass — a wrong result is costly for this task.")
    lines.append("")
    lines.append("Present this to the user as 'here's what I'd build and why', then confirm before scaffolding.")
    lines.append(f"Next: python scaffold_workflow.py --topology {rec['recommended_topology']} --name <name> --description \"...\"")
    return "\n".join(lines)


SAMPLE = {
    "task": "review my open PRs for bugs before I merge them",
    "units": "unknown",
    "stages": "unknown",
    "needs_all": "unknown",
    "structured": "unknown",
}


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--task", help="free-text description of the task to automate")
    p.add_argument("--units", choices=CHOICES_UNITS, default="unknown",
                   help="is the unit count a known list, unknown, or loop-discovered")
    p.add_argument("--stages", choices=CHOICES_STAGES, default="unknown",
                   help="single stage or multiple ordered stages")
    p.add_argument("--needs-all", dest="needs_all", choices=CHOICES_TRI, default="unknown",
                   help="does a later step need all prior results at once")
    p.add_argument("--structured", choices=CHOICES_TRI, default="unknown",
                   help="does any step need structured data back")
    p.add_argument("--json", action="store_true", help="emit JSON instead of human-readable text")
    p.add_argument("--sample", action="store_true", help="run with a built-in vague-request sample")
    args = p.parse_args(argv)

    if args.sample or not args.task:
        if not args.task and not args.sample:
            print("No --task given; running --sample. Use --help for options.\n", file=sys.stderr)
        s = SAMPLE
        rec = recommend(s["task"], s["units"], s["stages"], s["needs_all"], s["structured"])
    else:
        rec = recommend(args.task, args.units, args.stages, args.needs_all, args.structured)

    print(json.dumps(rec, indent=2) if args.json else render_human(rec))
    return 0


if __name__ == "__main__":
    sys.exit(main())
