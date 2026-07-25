#!/usr/bin/env python3
"""skill_recommender.py — Recommend which skills the next session should use.

Stdlib-only. Scans a handoff document for content signals and matches them to
skills in this repo. Output: ranked recommendations with rationale.

Signal-to-skill mapping (a representative subset; see references for full taxonomy):

  - "write a skill" / "new skill" / "skill author"   -> write-a-skill
  - "less tokens" / "be brief" / "caveman"           -> caveman
  - "grill" / "stress-test" / "decision tree"        -> grill-me
  - "test" / "TDD" / "unit test"                     -> tdd-guide
  - "RICE" / "prioritize" / "feature score"          -> rice-prioritizer
  - "user story" / "INVEST"                          -> user-story-writer
  - "code quality" / "refactor" / "complexity"       -> karpathy-coder
  - "CI" / "ship gate" / "pre-flight"                -> ship-gate
  - "audit" / "compliance" / "ISO" / "GDPR"          -> compliance-os
  - "SLO" / "error budget" / "burn rate"             -> slo-architect
  - "feature flag" / "kill switch" / "rollout"       -> feature-flags-architect
  - "incident" / "postmortem"                        -> incident-response
  - "security" / "OWASP" / "threat"                  -> ai-security / threat-detection
  - "research" / "citations" / "sources"             -> autoresearch-agent

NO LLM CALLS. Pattern-match recommender.

Usage:
    python skill_recommender.py                          # uses embedded sample
    python skill_recommender.py path/to/handoff.md
    python skill_recommender.py handoff.md --output json
"""

import argparse
import json
import re
import sys
from typing import Any, Dict, List, Tuple


# (keyword pattern, skill name, rationale template)
SKILL_SIGNALS: List[Tuple[re.Pattern, str, str]] = [
    (re.compile(r"\b(write|create|author|build)\s+(a\s+)?skill\b", re.IGNORECASE),
     "write-a-skill",
     "Next session involves authoring a new skill; the write-a-skill skill applies Matt Pocock's 3-phase workflow + validates against the 6-item checklist."),
    (re.compile(r"\b(caveman|less\s+tokens|be\s+brief|compress)\b", re.IGNORECASE),
     "caveman",
     "Next session benefits from token-compressed responses; caveman applies Matt's compression rules deterministically."),
    (re.compile(r"\b(grill|stress[-\s]?test|interrog|decision\s+tree)\b", re.IGNORECASE),
     "grill-me",
     "Next session involves stress-testing a plan; grill-me walks decision branches one-at-a-time with forcing questions."),
    (re.compile(r"\b(TDD|unit\s+test|test\s+driven)\b", re.IGNORECASE),
     "tdd-guide",
     "Next session involves testing; tdd-guide enforces test-first discipline."),
    (re.compile(r"\b(RICE|prioritiz|feature\s+score)\b", re.IGNORECASE),
     "rice-prioritizer",
     "Next session involves feature prioritization; rice-prioritizer computes Reach × Impact × Confidence ÷ Effort."),
    (re.compile(r"\b(user\s+stor|INVEST)\b", re.IGNORECASE),
     "user-story-writer",
     "Next session involves user stories; user-story-writer applies INVEST + Gherkin acceptance criteria."),
    (re.compile(r"\b(karpathy|complexity|refactor|code\s+quality)\b", re.IGNORECASE),
     "karpathy-coder",
     "Next session involves code-quality discipline; karpathy-coder runs complexity_checker + assumption_linter + diff_surgeon."),
    (re.compile(r"\b(ship\s+gate|pre[-\s]?flight|production\s+ready)\b", re.IGNORECASE),
     "ship-gate",
     "Next session involves pre-production audit; ship-gate runs 89 checks across 8 categories."),
    (re.compile(r"\b(ISO\s+13485|ISO\s+27001|GDPR|HIPAA|MDR|FDA|compliance|audit)\b", re.IGNORECASE),
     "compliance-os",
     "Next session involves regulatory/compliance work; compliance-os covers 12 frameworks with mock audit scenarios."),
    (re.compile(r"\b(SLO|error\s+budget|burn\s+rate)\b", re.IGNORECASE),
     "slo-architect",
     "Next session involves SLO/SLI/error-budget work; slo-architect applies Google SRE Workbook discipline."),
    (re.compile(r"\b(feature\s+flag|kill\s+switch|gradual\s+rollout|canary)\b", re.IGNORECASE),
     "feature-flags-architect",
     "Next session involves feature-flag work; feature-flags-architect scans flag debt + rollout plans."),
    (re.compile(r"\b(incident|postmortem|outage|root\s+cause)\b", re.IGNORECASE),
     "incident-response",
     "Next session involves incident response or postmortem; incident-response provides templates + analysis tools."),
    (re.compile(r"\b(AI\s+security|prompt\s+inject|threat\s+model|OWASP)\b", re.IGNORECASE),
     "ai-security",
     "Next session involves AI security or threat work; ai-security covers prompt injection + model threats."),
    (re.compile(r"\b(research|citation|authoritative\s+source|deep\s+research)\b", re.IGNORECASE),
     "autoresearch-agent",
     "Next session needs citation-backed research; autoresearch-agent produces deep-research reports."),
    (re.compile(r"\b(handoff|next\s+session|continue\s+the\s+work)\b", re.IGNORECASE),
     "handoff",
     "Next session may need to be handed off again; handoff produces continuity docs."),
]


SAMPLE_HANDOFF = """# Handoff — ship Matt Pocock skills batch

## Goal of next session
Open PR for caveman + grill-me + handoff skills. Validate against the karpathy-coder
gate (complexity checker + assumption linter) and the write-a-skill 6-item checklist.
Investigate any CI failures.

## State of play
Done: write-a-skill plugin shipped + merged.
In progress: 3 sibling skills built locally, need PR.
Blocking: nothing.

## Open decisions
- Should we caveman the PR description?
- Re-grill the plan before opening PR?

## Artifacts
- Branch: feature/pocock-productivity-batch
- Issues: none
- PRD: documentation/implementation/pocock-derived-skills-plan.md
"""


def recommend(text: str) -> List[Dict[str, Any]]:
    hits: Dict[str, Dict[str, Any]] = {}
    for pattern, skill, rationale in SKILL_SIGNALS:
        matches = pattern.findall(text)
        if not matches:
            continue
        if skill not in hits:
            hits[skill] = {"skill": skill, "rationale": rationale, "hits": 0, "matched_keywords": []}
        hits[skill]["hits"] += len(matches)
        hits[skill]["matched_keywords"].extend(
            m if isinstance(m, str) else " ".join(filter(None, m))
            for m in matches[:3]
        )
    ranked = sorted(hits.values(), key=lambda x: -x["hits"])
    return ranked


def analyze(text: str) -> Dict[str, Any]:
    recommendations = recommend(text)
    return {
        "total_skills_recommended": len(recommendations),
        "recommendations": recommendations,
    }


def render_text(r: Dict[str, Any]) -> str:
    lines = []
    lines.append("=" * 72)
    lines.append("SKILL RECOMMENDER FOR NEXT SESSION")
    lines.append("=" * 72)
    lines.append("")
    lines.append(f"Skills recommended: {r['total_skills_recommended']}")
    lines.append("")
    if not r["recommendations"]:
        lines.append("No skill signals detected. Next session may not need a specific skill.")
    else:
        for i, rec in enumerate(r["recommendations"], start=1):
            kw_preview = ", ".join(rec["matched_keywords"][:3])
            lines.append(f"  [{i}] {rec['skill']:30s} (matched {rec['hits']}x: {kw_preview})")
            lines.append(f"      {rec['rationale']}")
            lines.append("")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Recommend skills for the next session based on handoff content.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument("path", nargs="?", help="Path to handoff markdown (uses embedded sample if omitted)")
    parser.add_argument("--output", choices=("text", "json"), default="text", help="Output format")
    args = parser.parse_args()

    if args.path:
        try:
            with open(args.path, "r", encoding="utf-8") as f:
                text = f.read()
        except (IOError, OSError) as e:
            print(f"error: {e}", file=sys.stderr)
            return 1
    else:
        text = SAMPLE_HANDOFF

    result = analyze(text)
    if args.output == "json":
        print(json.dumps(result, indent=2))
    else:
        print(render_text(result))
    return 0


if __name__ == "__main__":
    sys.exit(main())
