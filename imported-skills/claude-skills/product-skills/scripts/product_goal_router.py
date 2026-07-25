#!/usr/bin/env python3
"""product_goal_router.py — deterministic lane classifier for the product-team domain.

Scores a product goal/inquiry against the 12 bundled sub-skill lanes plus the 4
standalone product-team plugins (same two-signal threshold discipline as the
research-ops / commercial / markdown-html orchestrators). Emits a routing decision
an agent can branch on mechanically.

Exit codes:
  0  confident route emitted (route_to set)
  2  ambiguous — ask ONE clarifying question naming the top two lanes
  3  no signal — do not guess; ask the user to restate the goal
Stdlib only. Deterministic: same text in, same route out.
"""

import argparse
import json
import sys

SIGNALS = {
    "PRIORITIZE": {
        "skill": "product-manager-toolkit",
        "path": "product-team/skills/product-manager-toolkit",
        "keywords": ["prioritize", "rice", "backlog ranking", "feature ranking",
                      "prd", "product requirements", "interview synthesis", "wsjf",
                      "cost of delay"],
    },
    "STRATEGY": {
        "skill": "product-strategist",
        "path": "product-team/skills/product-strategist",
        "keywords": ["okr", "objective", "strategy", "quarterly planning",
                      "north star", "vision", "alignment"],
    },
    "UX": {
        "skill": "ux-researcher-designer",
        "path": "product-team/skills/ux-researcher-designer",
        "keywords": ["persona", "journey map", "usability", "user research",
                      "research synthesis", "interview guide"],
    },
    "DESIGN_SYSTEM": {
        "skill": "ui-design-system",
        "path": "product-team/skills/ui-design-system",
        "keywords": ["design token", "component spec", "design system",
                      "wcag", "contrast", "typography scale"],
    },
    "COMPETITIVE": {
        "skill": "competitive-teardown",
        "path": "product-team/skills/competitive-teardown",
        "keywords": ["competitor", "competitive", "teardown", "pricing matrix",
                      "market position", "feature comparison"],
    },
    "ANALYTICS": {
        "skill": "product-analytics",
        "path": "product-team/skills/product-analytics",
        "keywords": ["retention", "cohort", "funnel", "kpi", "activation",
                      "churn", "aarrr", "north star metric", "tracking plan",
                      "event taxonomy"],
    },
    "EXPERIMENT": {
        "skill": "experiment-designer",
        "path": "product-team/skills/experiment-designer",
        "keywords": ["a/b test", "ab test", "experiment", "sample size",
                      "hypothesis", "mde", "statistical power", "eval"],
    },
    "DISCOVERY": {
        "skill": "product-discovery",
        "path": "product-team/skills/product-discovery",
        "keywords": ["discovery", "opportunity", "assumption", "opportunity solution tree",
                      "ost", "continuous discovery", "customer interview cadence",
                      "jtbd", "jobs to be done"],
    },
    "ROADMAP": {
        "skill": "roadmap-communicator",
        "path": "product-team/skills/roadmap-communicator",
        "keywords": ["roadmap", "release notes", "changelog", "launch comms",
                      "now next later"],
    },
    "SPEC_TO_REPO": {
        "skill": "spec-to-repo",
        "path": "product-team/skills/spec-to-repo",
        "keywords": ["spec to repo", "scaffold from spec", "build from spec",
                      "generate the repo", "turn this spec into"],
    },
    "LANDING": {
        "skill": "landing-page-generator",
        "path": "product-team/skills/landing-page-generator",
        "keywords": ["landing page", "hero section", "waitlist page", "marketing page"],
    },
    "SAAS_SCAFFOLD": {
        "skill": "saas-scaffolder",
        "path": "product-team/skills/saas-scaffolder",
        "keywords": ["saas boilerplate", "saas skeleton", "bootstrap a saas",
                      "auth and billing", "stripe integration scaffold"],
    },
    # Standalone product-team plugins (packaged separately, routable all the same)
    "STORIES": {
        "skill": "agile-product-owner",
        "path": "product-team/agile-product-owner/skills/agile-product-owner",
        "keywords": ["user story", "user stories", "acceptance criteria", "invest",
                      "epic breakdown", "sprint capacity", "story splitting"],
    },
    "HIG": {
        "skill": "apple-hig-expert",
        "path": "product-team/apple-hig-expert/skills/apple-hig-expert",
        "keywords": ["hig", "human interface guidelines", "ios design", "liquid glass",
                      "tap target", "apple design"],
    },
    "CODE_TO_PRD": {
        "skill": "code-to-prd",
        "path": "product-team/code-to-prd/skills/code-to-prd",
        "keywords": ["reverse engineer", "code to prd", "prd from code",
                      "document this codebase as a prd", "existing app into a prd"],
    },
    "SUMMARIZE": {
        "skill": "research-summarizer",
        "path": "product-team/research-summarizer/skills/research-summarizer",
        "keywords": ["summarize this paper", "summarize research", "citation extraction",
                      "compare these papers", "article summary"],
    },
}

SAMPLE_GOAL = ("we keep shipping features nobody uses — I want a weekly discovery "
               "habit and an opportunity solution tree before the next roadmap review")


def score(text: str) -> dict:
    low = text.lower()
    scores, hits = {}, {}
    for lane, spec in SIGNALS.items():
        matched = [kw for kw in spec["keywords"] if kw in low]
        scores[lane] = len(matched)
        hits[lane] = matched
    return {"scores": scores, "hits": hits}


def decide(scores: dict) -> dict:
    ranked = sorted(scores.items(), key=lambda kv: (-kv[1], kv[0]))
    (top_lane, top), (second_lane, second) = ranked[0], ranked[1]
    if top == 0:
        return {"decision": "NO_SIGNAL", "exit": 3}
    if top >= 2 and (second == 0 or top >= 2 * second):
        return {"decision": "ROUTE", "lane": top_lane, "exit": 0}
    candidates = [top_lane] + ([second_lane] if second > 0 else [])
    return {"decision": "ASK", "candidates": candidates, "exit": 2}


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Deterministic lane router for product-team goals.")
    src = ap.add_mutually_exclusive_group()
    src.add_argument("--text", help="Goal / inquiry text to classify.")
    src.add_argument("--input", help="Read goal text from a file ('-' for stdin).")
    ap.add_argument("--output", choices=["json", "human"], default="json")
    ap.add_argument("--sample", action="store_true",
                    help="Classify a built-in sample goal and exit.")
    args = ap.parse_args()

    if args.sample:
        text = SAMPLE_GOAL
    elif args.text:
        text = args.text
    elif args.input:
        text = (sys.stdin.read() if args.input == "-"
                else open(args.input, encoding="utf-8").read())
    else:
        ap.error("one of --text, --input, or --sample is required")

    result = score(text)
    verdict = decide(result["scores"])
    out = {
        "goal": text.strip()[:300],
        "scores": {k: v for k, v in result["scores"].items() if v},
        "decision": verdict["decision"],
    }
    if verdict["decision"] == "ROUTE":
        lane = verdict["lane"]
        out["route_to"] = SIGNALS[lane]["skill"]
        out["skill_path"] = SIGNALS[lane]["path"]
        out["matched_signals"] = result["hits"][lane]
    elif verdict["decision"] == "ASK":
        out["candidates"] = [
            {"lane": lane, "skill": SIGNALS[lane]["skill"], "score": result["scores"][lane]}
            for lane in verdict["candidates"]
        ]
        out["instruction"] = ("Ask ONE clarifying question naming both candidate lanes, "
                              "with a recommended answer. Never guess silently.")
    else:
        out["instruction"] = ("No lane signal. Ask the user to restate the goal with the "
                              "deliverable named. Do not route on fuzz.")

    if args.output == "json":
        print(json.dumps(out, indent=2))
    else:
        print(f"Decision: {out['decision']}")
        if "route_to" in out:
            print(f"Route to: {out['route_to']} ({out['skill_path']})")
            print(f"Signals:  {', '.join(out['matched_signals'])}")
        elif "candidates" in out:
            names = " vs ".join(c["skill"] for c in out["candidates"])
            print(f"Ambiguous: {names} — ask one clarifying question.")
        else:
            print("No signal — ask the user to restate the goal.")
    return verdict["exit"]


if __name__ == "__main__":
    sys.exit(main())
